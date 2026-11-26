//! Optional OpenCL BN254 G1 MSM backend for Xark's Groth16 prover.
//!
//! Small inputs use independent scalar-point products. Inputs of 256 or more
//! scalars use a 4-bit bucket MSM. Input validation also materializes each
//! scalar's 64 four-bit digits once in a compact byte table, which bucket scans
//! reuse instead of extracting from scalar limbs for every bucket. The dispatch
//! point is an initial heuristic, not a measured crossover; run
//! `cargo run --release -p xark-groth16-opencl --example msm_bench` on the target
//! GPU before treating it as a performance choice. Both kernels are variable-time.
//! The benchmark's `XARK_OPENCL_DEVICE_INDEX` selects a zero-based OpenCL GPU
//! in platform enumeration order and defaults to 0; it prints device identity
//! with every benchmark report.
//!
//! OpenCL dispatch uses a per-device, in-process admission queue. By default it
//! permits one active MSM, up to eight waiting chunks, and reserves at most 75%
//! of reported global device memory. Set `XARK_OPENCL_MAX_ACTIVE_JOBS`,
//! `XARK_OPENCL_MAX_QUEUED_JOBS`, and `XARK_OPENCL_MEMORY_PERCENT` before process
//! startup to change those limits. Up to 256 MiB of combined active and waiting
//! host input/preparation memory is reserved by default; set
//! `XARK_OPENCL_MAX_RESERVED_HOST_BYTES` to change it. An over-budget or
//! queue-full chunk declines to the prover's CPU path. Separate processes do
//! not share this queue.
//!
//! [`OpenClMsm::from_env`], which `xark prove --prover opencl` uses, also reads
//! `XARK_OPENCL_DEVICE` (`gpu`, the default, or `any`, which admits CPU
//! runtimes such as POCL) and `XARK_OPENCL_MIN_DOMAIN` (the smallest domain it
//! takes a proof for, [`DEFAULT_MIN_DOMAIN`] by default).
//!
//! GPU work exposes input-dependent timing and device/driver memory residency.
//! OpenCL is not claimed constant-time or guaranteed to erase device
//! memory. Use CPU proving for secret inputs on shared or untrusted hardware.

use std::ops::Range;

use ark_bn254::{Fq, Fr, G1Affine, G1Projective};
use ark_ec::{AdditiveGroup, AffineRepr, CurveGroup};
use ark_ff::{BigInt, PrimeField, Zero};
use ark_serialize::{CanonicalSerialize, Compress};
use opencl3::{
    command_queue::CommandQueue,
    context::Context,
    device::{CL_DEVICE_TYPE_ALL, CL_DEVICE_TYPE_GPU, Device},
    kernel::{ExecuteKernel, Kernel},
    memory::{
        Buffer, CL_MAP_READ, CL_MAP_WRITE_INVALIDATE_REGION, CL_MEM_ALLOC_HOST_PTR,
        CL_MEM_READ_ONLY, CL_MEM_READ_WRITE, CL_MEM_WRITE_ONLY, CL_TRUE, ClMem,
    },
    platform::get_platforms,
    program::Program,
    types::cl_device_type,
};
use xark_groth16::{Accelerator, msm::Scalar};
mod fft;
mod pool;
mod scheduler;
use scheduler::DeviceScheduler;

const MSM_SOURCE: &str = concat!(
    include_str!("../kernels/msm_pointwise.cl"),
    "\n",
    include_str!("../kernels/msm_digits.cl"),
    "\n",
    include_str!("../kernels/msm_bucket.cl"),
    "\n",
    include_str!("../kernels/msm_sorted.cl"),
    "\n",
    include_str!("../kernels/fft.cl"),
);
const POINT_WORDS: usize = 17;
const TERM_WORDS: usize = 24;
const BUCKET_BITS: usize = 4;
const BUCKET_WINDOWS: usize = 256 / BUCKET_BITS;
const BUCKET_COUNT: usize = (1 << BUCKET_BITS) - 1;
const BUCKET_THRESHOLD: usize = 256;

/// OpenCL backend. Its variable-time scalar multiplication may expose input-
/// dependent timing, and device buffers are not guaranteed to be erased. Use
/// only on trusted, single-tenant hardware; separate processes do not share the
/// in-process admission queue. The default constructor selects a GPU;
/// `with_any_device` also permits CPU OpenCL runtimes for correctness testing.
pub struct OpenClMsm {
    device_type: cl_device_type,
    device_index: usize,
    runtime: Option<Runtime>,
    min_domain: usize,
}

/// The smallest QAP domain the device takes a proof for, by default. A proof on
/// the device has a fixed cost of about 60 ms (an Apple M3 Max), which its H MSM
/// pays back only past 2^17 points: there keccak256 (89k constraints) proved in
/// about the CPU's time, and at 2^18 aes256_gcm (210k) 1.4× faster.
pub const DEFAULT_MIN_DOMAIN: usize = 1 << 18;

/// Identifies the OpenCL device used by an initialized backend.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OpenClDeviceInfo {
    pub index: usize,
    pub name: String,
    pub vendor: String,
    pub version: String,
    pub driver_version: String,
    pub compute_units: u32,
    pub global_memory_bytes: u64,
}

/// Device selection for an OpenCL MSM context.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OpenClDeviceKind {
    /// Use an OpenCL GPU.
    Gpu,
    /// Use the first available OpenCL device, including a CPU device.
    Any,
}

impl Default for OpenClMsm {
    fn default() -> Self {
        Self::new()
    }
}

impl OpenClMsm {
    /// Select the first available OpenCL GPU.
    pub fn new() -> Self {
        Self::with_device_kind(OpenClDeviceKind::Gpu)
    }

    /// Select the first available OpenCL device, including a CPU runtime.
    pub fn with_any_device() -> Self {
        Self::with_device_kind(OpenClDeviceKind::Any)
    }

    /// Select the first available device of the requested kind.
    pub fn with_device_kind(kind: OpenClDeviceKind) -> Self {
        Self::with_device_index(kind, 0)
    }

    /// Select a zero-based device among available devices of the requested kind.
    /// Enumeration follows OpenCL platform order, then each platform's device order.
    pub fn with_device_index(kind: OpenClDeviceKind, device_index: usize) -> Self {
        let device_type = match kind {
            OpenClDeviceKind::Gpu => CL_DEVICE_TYPE_GPU,
            OpenClDeviceKind::Any => CL_DEVICE_TYPE_ALL,
        };
        Self {
            device_type,
            device_index,
            runtime: None,
            min_domain: DEFAULT_MIN_DOMAIN,
        }
    }

    /// The device `XARK_OPENCL_DEVICE` names and the minimum domain
    /// `XARK_OPENCL_MIN_DOMAIN` sets (see the crate docs), else a GPU from
    /// [`DEFAULT_MIN_DOMAIN`].
    pub fn from_env() -> Self {
        let kind = match std::env::var("XARK_OPENCL_DEVICE").as_deref() {
            Ok("any") => OpenClDeviceKind::Any,
            _ => OpenClDeviceKind::Gpu,
        };
        let min = std::env::var("XARK_OPENCL_MIN_DOMAIN")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(DEFAULT_MIN_DOMAIN);
        Self::with_device_kind(kind).with_min_domain(min)
    }

    /// The smallest domain this device takes a proof for.
    pub fn min_domain(&self) -> usize {
        self.min_domain
    }

    /// Take proofs from a domain of `points` points on ([`DEFAULT_MIN_DOMAIN`]
    /// unless set); smaller ones prove on the CPU alone.
    pub fn with_min_domain(mut self, points: usize) -> Self {
        self.min_domain = points;
        self
    }

    /// Load the device and build the kernels. Returns false when the runtime
    /// or compiler is unavailable, allowing callers to report a clean fallback.
    pub fn initialize(&mut self) -> bool {
        self.runtime().is_some()
    }

    /// Return metadata for the device selected during initialization.
    pub fn device_info(&mut self) -> Option<&OpenClDeviceInfo> {
        self.runtime().map(|runtime| &runtime.device_info)
    }

    fn runtime(&mut self) -> Option<&mut Runtime> {
        if self.runtime.is_none() {
            self.runtime = Runtime::new(self.device_type, self.device_index);
        }
        self.runtime.as_mut()
    }
}

impl Accelerator for OpenClMsm {
    fn wants_proof(&self, domain_size: usize) -> bool {
        domain_size >= self.min_domain
    }

    fn to_coset(&mut self, dom: &xark_groth16::Domain, buf: &mut [Fr]) -> bool {
        gpu_fft_enabled()
            && self
                .runtime()
                .and_then(|runtime| runtime.coset_transform(dom, buf, fft::Transform::ToCoset))
                .is_some()
    }

    fn from_coset_to_t(&mut self, dom: &xark_groth16::Domain, buf: &mut [Fr]) -> bool {
        gpu_fft_enabled()
            && self
                .runtime()
                .and_then(|runtime| runtime.coset_transform(dom, buf, fft::Transform::FromCosetToT))
                .is_some()
    }

    fn ifft_to_t(&mut self, dom: &xark_groth16::Domain, buf: &mut [Fr]) -> bool {
        gpu_fft_enabled()
            && self
                .runtime()
                .and_then(|runtime| runtime.coset_transform(dom, buf, fft::Transform::IfftToT))
                .is_some()
    }

    /// Builds the domain's FFT tables and runs each kernel once on a few points,
    /// so the proof's first launches don't pay for it.
    fn prepare(&mut self, domain_size: usize) {
        let Some(runtime) = self.runtime() else {
            return;
        };
        if gpu_fft_enabled() && domain_size.is_power_of_two() && domain_size >= fft::MIN_GPU_FFT {
            if !runtime.twiddles.contains_key(&domain_size)
                && let Some(tables) = runtime.tables(domain_size)
            {
                runtime.twiddles.insert(domain_size, tables);
            }
            if let Some(dom) = xark_groth16::Domain::new(fft::MIN_GPU_FFT, Default::default()) {
                let mut buf = vec![Fr::from(1u64); dom.n];
                runtime.coset_transform(&dom, &mut buf, fft::Transform::ToCoset);
                runtime.coset_transform(&dom, &mut buf, fft::Transform::FromCosetToT);
                runtime.coset_transform(&dom, &mut buf, fft::Transform::IfftToT);
            }
        }
        runtime.prewarm(domain_size);
        let count = BUCKET_THRESHOLD * 2;
        let mut points = Vec::new();
        let g = G1Affine::generator();
        for _ in 0..count {
            let _ = g.serialize_uncompressed(&mut points);
        }
        let scalars: Vec<Scalar> = (0..count as u64)
            .map(|i| BigInt([i.wrapping_mul(0x9e37_79b9_7f4a_7c15), i, i ^ 0x5555, 1]))
            .collect();
        let _ = self.msm(false, &points, false, &scalars);
    }

    fn wants_msm(&self) -> bool {
        find_device(self.device_type, self.device_index).is_some()
    }

    fn wants_msm_for(&self, g2: bool, scalars: &[Scalar]) -> bool {
        !g2 && !prefers_cpu(scalars) && self.wants_msm()
    }

    fn msm(
        &mut self,
        g2: bool,
        points: &[u8],
        compressed: bool,
        scalars: &[Scalar],
    ) -> Option<Vec<u8>> {
        if g2 {
            return None;
        }
        if scalars.is_empty() {
            return serialize_point(G1Affine::zero());
        }
        if prefers_cpu(scalars) {
            return None;
        }
        let encoding = if compressed {
            Compress::Yes
        } else {
            Compress::No
        };
        let point_size = G1Affine::generator().serialized_size(encoding);
        if points.len() != scalars.len().checked_mul(point_size)? {
            return None;
        }

        let runtime = self.runtime()?;
        let ranges = runtime.chunk_ranges(scalars.len())?;
        let mut total = G1Projective::zero();
        for range in ranges {
            let point_bytes = &points[range.start * point_size..range.end * point_size];
            let result = runtime.run_chunk(point_bytes, encoding, &scalars[range.clone()])?;
            total += result;
        }
        serialize_point(total.into_affine())
    }
}

struct Runtime {
    context: Context,
    queue: CommandQueue,
    program: Program,
    max_alloc_bytes: usize,
    scheduler: std::sync::Arc<DeviceScheduler>,
    device_info: OpenClDeviceInfo,
    /// Per domain size: twiddles and coset factors.
    twiddles: std::collections::HashMap<usize, fft::Tables>,
    /// Buffers kept from call to call (see [`pool`]).
    pool: pool::Pool,
}

impl Runtime {
    fn new(device_type: cl_device_type, device_index: usize) -> Option<Self> {
        let (device, device_id) = find_device(device_type, device_index)?;
        let context = Context::from_device(&device).ok()?;
        let queue = CommandQueue::create_default(&context, 0).ok()?;
        let program =
            match Program::create_and_build_from_source(&context, MSM_SOURCE, "-cl-std=CL1.2") {
                Ok(program) => program,
                Err(log) => {
                    if std::env::var_os("XARK_OPENCL_BUILD_LOG").is_some() {
                        eprintln!("OpenCL build failed: {log}");
                    }
                    return None;
                }
            };
        let max_alloc_bytes = usize::try_from(device.max_mem_alloc_size().ok()?).ok()?;
        let global_mem_bytes = usize::try_from(device.global_mem_size().ok()?).ok()?;
        let scheduler = scheduler::for_device(device_id, global_mem_bytes)?;
        let device_info = OpenClDeviceInfo {
            index: device_index,
            name: device.name().ok()?,
            vendor: device.vendor().ok()?,
            version: device.version().ok()?,
            driver_version: device.driver_version().ok()?,
            compute_units: device.max_compute_units().ok()?,
            global_memory_bytes: device.global_mem_size().ok()?,
        };
        Some(Self {
            context,
            queue,
            program,
            max_alloc_bytes,
            scheduler,
            device_info,
            twiddles: Default::default(),
            pool: pool::Pool::default(),
        })
    }

    fn chunk_ranges(&self, count: usize) -> Option<Vec<Range<usize>>> {
        let word_bytes = std::mem::size_of::<u32>();
        let point_bytes = POINT_WORDS.checked_mul(word_bytes)?;
        let scalar_bytes = 4usize.checked_mul(std::mem::size_of::<u64>())?;
        let term_bytes = TERM_WORDS.checked_mul(word_bytes)?;
        let valid_bytes = word_bytes;
        let live_bytes_per_point = point_bytes
            .checked_add(scalar_bytes)?
            .checked_add(term_bytes.checked_mul(2)?)?
            .checked_add(valid_bytes.checked_mul(2)?)?;
        let by_buffer = [point_bytes, scalar_bytes, term_bytes, valid_bytes]
            .into_iter()
            .map(|bytes| self.max_alloc_bytes.checked_div(bytes))
            .collect::<Option<Vec<_>>>()?
            .into_iter()
            .min()?;
        let usable_memory = self
            .scheduler
            .memory_budget_bytes()
            .checked_sub(POINT_WORDS.checked_mul(word_bytes)?)?;
        let by_global = usable_memory.checked_div(live_bytes_per_point)?;
        let max_points = by_buffer.min(by_global);
        if max_points == 0 {
            return None;
        }
        let chunk_count = count.checked_add(max_points - 1)?.checked_div(max_points)?;
        let mut ranges = Vec::new();
        ranges.try_reserve_exact(chunk_count).ok()?;
        let mut start = 0usize;
        while start < count {
            let end = start.checked_add(max_points)?.min(count);
            ranges.push(start..end);
            start = end;
        }
        Some(ranges)
    }

    fn run_chunk(
        &self,
        point_bytes: &[u8],
        encoding: Compress,
        scalars: &[Scalar],
    ) -> Option<G1Projective> {
        let bucket_bytes = estimated_chunk_bytes(scalars.len(), true);
        let use_buckets = scalars.len() >= BUCKET_THRESHOLD
            && self.bucket_scratch_fits(scalars.len())
            && bucket_bytes.is_some_and(|bytes| bytes <= self.scheduler.memory_budget_bytes());
        let host_bytes = estimated_host_chunk_bytes(point_bytes.len(), scalars.len())?;
        let _permit = self.scheduler.acquire(
            estimated_chunk_bytes(scalars.len(), use_buckets)?,
            host_bytes,
        )?;
        if use_buckets {
            if std::env::var_os("XARK_OPENCL_LEGACY_BUCKETS").is_none() {
                return self.run_sorted_chunk(point_bytes, encoding, scalars);
            }
            return self.run_bucket_chunk(point_bytes, encoding, scalars);
        }
        let (point_words, scalar_limbs) = prepare_inputs(point_bytes, encoding, scalars)?;
        let count = scalars.len();
        let term_word_count = count.checked_mul(TERM_WORDS)?;
        let mut result_words = [0u32; POINT_WORDS];

        // SAFETY: null host pointers request device-owned allocations; lengths
        // come from checked input dimensions and are measured in elements.
        let mut point_buffer = unsafe {
            Buffer::<u32>::create(
                &self.context,
                CL_MEM_READ_ONLY,
                point_words.len(),
                std::ptr::null_mut(),
            )
        }
        .ok()?;
        let mut scalar_buffer = unsafe {
            Buffer::<u64>::create(
                &self.context,
                CL_MEM_READ_ONLY,
                scalar_limbs.len(),
                std::ptr::null_mut(),
            )
        }
        .ok()?;
        let term_buffer = unsafe {
            Buffer::<u32>::create(
                &self.context,
                CL_MEM_READ_WRITE,
                term_word_count,
                std::ptr::null_mut(),
            )
        }
        .ok()?;
        let term_scratch = unsafe {
            Buffer::<u32>::create(
                &self.context,
                CL_MEM_READ_WRITE,
                term_word_count,
                std::ptr::null_mut(),
            )
        }
        .ok()?;
        let valid_buffer = unsafe {
            Buffer::<u32>::create(
                &self.context,
                CL_MEM_READ_WRITE,
                count,
                std::ptr::null_mut(),
            )
        }
        .ok()?;
        let valid_scratch = unsafe {
            Buffer::<u32>::create(
                &self.context,
                CL_MEM_READ_WRITE,
                count,
                std::ptr::null_mut(),
            )
        }
        .ok()?;
        let result_buffer = unsafe {
            Buffer::<u32>::create(
                &self.context,
                CL_MEM_WRITE_ONLY,
                result_words.len(),
                std::ptr::null_mut(),
            )
        }
        .ok()?;

        // SAFETY: both buffers belong to this runtime's context and each slice
        // is live and covers the complete destination allocation for the call.
        unsafe {
            self.queue
                .enqueue_write_buffer(&mut point_buffer, CL_TRUE, 0, &point_words, &[])
                .ok()?;
            self.queue
                .enqueue_write_buffer(&mut scalar_buffer, CL_TRUE, 0, &scalar_limbs, &[])
                .ok()?;
        }

        let term_kernel = Kernel::create(&self.program, "opencl_msm_terms").ok()?;
        let count_arg = u64::try_from(count).ok()?;
        // SAFETY: argument order matches `opencl_msm_terms`; all buffers were
        // created from this context and `count` is the scalar/point length.
        unsafe {
            ExecuteKernel::new(&term_kernel)
                .set_arg(&point_buffer)
                .set_arg(&scalar_buffer)
                .set_arg(&count_arg)
                .set_arg(&term_buffer)
                .set_arg(&valid_buffer)
                .set_global_work_size(count)
                .enqueue_nd_range(&self.queue)
                .ok()?;
        }

        let reduce_kernel = Kernel::create(&self.program, "opencl_msm_reduce_pairs").ok()?;
        let mut input_count = count;
        let mut input_is_primary = true;
        while input_count > 1 {
            let output_count = input_count.checked_add(1)?.checked_div(2)?;
            let input_count_arg = u64::try_from(input_count).ok()?;
            // SAFETY: source and destination buffers share the context, do not
            // alias, and both are sized for at least the original element count.
            unsafe {
                let mut launch = ExecuteKernel::new(&reduce_kernel);
                if input_is_primary {
                    launch
                        .set_arg(&term_buffer)
                        .set_arg(&valid_buffer)
                        .set_arg(&term_scratch)
                        .set_arg(&valid_scratch);
                } else {
                    launch
                        .set_arg(&term_scratch)
                        .set_arg(&valid_scratch)
                        .set_arg(&term_buffer)
                        .set_arg(&valid_buffer);
                }
                launch
                    .set_arg(&input_count_arg)
                    .set_global_work_size(output_count)
                    .enqueue_nd_range(&self.queue)
                    .ok()?;
            }
            input_count = output_count;
            input_is_primary = !input_is_primary;
        }
        let (final_terms, final_valid) = if input_is_primary {
            (&term_buffer, &valid_buffer)
        } else {
            (&term_scratch, &valid_scratch)
        };
        let finish_kernel = Kernel::create(&self.program, "opencl_msm_finish").ok()?;
        // SAFETY: the finish kernel reads one reduced element and writes the
        // fixed 17-word result. The blocking read waits for all queued kernels.
        unsafe {
            ExecuteKernel::new(&finish_kernel)
                .set_arg(final_terms)
                .set_arg(final_valid)
                .set_arg(&result_buffer)
                .set_global_work_size(1)
                .enqueue_nd_range(&self.queue)
                .ok()?;
            self.queue
                .enqueue_read_buffer(&result_buffer, CL_TRUE, 0, &mut result_words, &[])
                .ok()?;
        }
        if result_words[16] > 1 {
            return None;
        }
        decode_result(&result_words).map(|point| point.into_group())
    }

    /// Sorted-bucket MSM, on the device end to end: prepare points, signed
    /// digits with a bucket histogram, scatter into buckets, segment sums,
    /// bucket fold and a ranged window reduction. The host only scans the
    /// histogram (one entry per bucket) and combines the window ranges.
    fn run_sorted_chunk(
        &self,
        point_bytes: &[u8],
        encoding: Compress,
        scalars: &[Scalar],
    ) -> Option<G1Projective> {
        use rayon::prelude::*;
        let profile = std::env::var_os("XARK_OPENCL_PROFILE").is_some();
        let started = std::time::Instant::now();
        let mut lap = started;
        let queue = &self.queue;
        let mut mark = |stage: &str| {
            if profile {
                let _ = queue.finish();
                let now = std::time::Instant::now();
                eprintln!(
                    "  opencl {stage}: {:.1} ms",
                    (now - lap).as_secs_f64() * 1e3
                );
                lap = now;
            }
        };

        let count = scalars.len();
        let count_arg = u32::try_from(count).ok()?;
        let status = self.upload(&[0u32], CL_MEM_READ_WRITE)?;
        let (points, flags) = match encoding {
            Compress::No => {
                // On unified memory the mapped buffer is the GPU's: one parallel
                // copy, no staging and no driver copy behind it.
                let raw =
                    self.stage_with::<u8>("msm.raw", CL_MEM_READ_ONLY, point_bytes.len(), |dst| {
                        dst.par_chunks_mut(1 << 20)
                            .zip(point_bytes.par_chunks(1 << 20))
                            .for_each(|(d, s)| d.copy_from_slice(s))
                    })?;
                let raw = &*raw;
                let points =
                    self.lease::<u32>("msm.points", CL_MEM_READ_WRITE, count.checked_mul(16)?)?;
                let flags = self.lease::<u32>("msm.flags", CL_MEM_READ_WRITE, count)?;
                let kernel = Kernel::create(&self.program, "msm_prepare_uncompressed").ok()?;
                // SAFETY: argument order matches the kernel; one item per point.
                unsafe {
                    ExecuteKernel::new(&kernel)
                        .set_arg(raw)
                        .set_arg(&count_arg)
                        .set_arg(&*points)
                        .set_arg(&*flags)
                        .set_arg(&status)
                        .set_global_work_size(count)
                        .enqueue_nd_range(&self.queue)
                        .ok()?;
                }
                (points, flags)
            }
            Compress::Yes => {
                let point_size = G1Affine::generator().serialized_size(encoding);
                let decoded: Vec<G1Affine> = point_bytes
                    .par_chunks_exact(point_size)
                    .map(|bytes| {
                        let point =
                            xark_groth16::decode::point::<G1Affine>(bytes, encoding).ok()?;
                        point.is_on_curve().then_some(point)
                    })
                    .collect::<Option<_>>()?;
                let words = self.stage_with::<u32>(
                    "msm.words",
                    CL_MEM_READ_ONLY,
                    count.checked_mul(16)?,
                    |words| {
                        words
                            .par_chunks_mut(16)
                            .zip(decoded.par_iter())
                            .for_each(|(out, point)| {
                                if point.is_zero() {
                                    out.fill(0);
                                } else {
                                    out[..8].copy_from_slice(&montgomery_words(&point.x.0.0));
                                    out[8..].copy_from_slice(&montgomery_words(&point.y.0.0));
                                }
                            })
                    },
                )?;
                let flags =
                    self.stage_with::<u32>("msm.word_flags", CL_MEM_READ_ONLY, count, |flags| {
                        flags
                            .par_iter_mut()
                            .zip(decoded.par_iter())
                            .for_each(|(f, p)| *f = p.is_zero() as u32)
                    })?;
                (words, flags)
            }
        };
        let (points, flags) = (&*points, &*flags);
        let scalar_buffer = self.stage_with::<u64>(
            "msm.scalars",
            CL_MEM_READ_ONLY,
            count.checked_mul(4)?,
            |limbs| {
                limbs
                    .par_chunks_mut(4)
                    .zip(scalars.par_iter())
                    .for_each(|(out, scalar)| out.copy_from_slice(&scalar.0))
            },
        )?;
        let scalar_buffer = &*scalar_buffer;
        mark("upload+prepare");

        let bits = env_usize("XARK_OPENCL_WINDOW_BITS")
            .unwrap_or_else(|| (count.ilog2() as usize).saturating_sub(3))
            .clamp(4, 16);
        let seg_len = env_usize("XARK_OPENCL_SEGMENT").unwrap_or(32).max(1);
        let windows = 256usize.div_ceil(bits);
        let buckets = 1usize << (bits - 1);
        let bucket_total = windows * buckets;
        let (bits_arg, windows_arg) = (bits as u32, windows as u32);
        let counts =
            self.stage_with::<u32>("msm.counts", CL_MEM_READ_WRITE, bucket_total, |c| {
                c.par_iter_mut().for_each(|x| *x = 0)
            })?;
        let counts = &*counts;
        let digits =
            self.lease::<i16>("msm.digits", CL_MEM_READ_WRITE, count.checked_mul(windows)?)?;
        let digits = &*digits;
        let kernel = Kernel::create(&self.program, "msm_signed_digits").ok()?;
        // SAFETY: argument order matches the kernel; one item per scalar.
        unsafe {
            ExecuteKernel::new(&kernel)
                .set_arg(scalar_buffer)
                .set_arg(&count_arg)
                .set_arg(&bits_arg)
                .set_arg(&windows_arg)
                .set_arg(flags)
                .set_arg(digits)
                .set_arg(counts)
                .set_arg(&status)
                .set_global_work_size(count)
                .enqueue_nd_range(&self.queue)
                .ok()?;
        }
        mark("digits");
        if self.download(&status, 1)?[0] != 0 {
            return None;
        }
        // The scan reads the histogram where the GPU wrote it.
        let (starts, mut bounds, mut bucket_segments, total) =
            self.download_with(counts, bucket_total, |bucket_counts| {
                let mut starts = Vec::with_capacity(bucket_total);
                let mut bounds = Vec::new();
                let mut bucket_segments = Vec::with_capacity(bucket_total + 1);
                let mut total = 0u32;
                for &n in bucket_counts {
                    starts.push(total);
                    bucket_segments.push(u32::try_from(bounds.len()).ok()?);
                    let (mut lo, hi) = (total, total.checked_add(n)?);
                    while lo < hi {
                        bounds.push(lo);
                        lo = lo.saturating_add(seg_len as u32).min(hi);
                    }
                    total = hi;
                }
                Some((starts, bounds, bucket_segments, total))
            })??;
        if total == 0 {
            return Some(G1Projective::zero());
        }
        let segment_count = bounds.len();
        let segment_arg = u32::try_from(segment_count).ok()?;
        bucket_segments.push(segment_arg);
        bounds.push(total);
        // Longest segments first (a counting sort by length), so a SIMD group's
        // work items sum segments of about the same length.
        let mut by_length = vec![0u32; seg_len + 2];
        for w in bounds.windows(2) {
            by_length[seg_len - (w[1] - w[0]) as usize + 1] += 1;
        }
        for l in 1..by_length.len() {
            by_length[l] += by_length[l - 1];
        }
        let bounds = self.stage_with::<u32>(
            "msm.bounds",
            CL_MEM_READ_ONLY,
            segment_count.checked_mul(3)?,
            |segments| {
                for (k, w) in bounds.windows(2).enumerate() {
                    let at = &mut by_length[seg_len - (w[1] - w[0]) as usize];
                    segments[3 * *at as usize..3 * *at as usize + 3]
                        .copy_from_slice(&[w[0], w[1], k as u32]);
                    *at += 1;
                }
            },
        )?;
        let bounds = &*bounds;
        let cursor =
            self.stage_with::<u32>("msm.cursor", CL_MEM_READ_WRITE, starts.len(), |c| {
                c.copy_from_slice(&starts)
            })?;
        let cursor = &*cursor;
        let order = self.lease::<u32>("msm.order", CL_MEM_READ_WRITE, total as usize)?;
        let order = &*order;
        let bucket_segments_host = bucket_segments;
        mark("host scan+upload");
        let partials = self.lease::<u32>(
            "msm.partials",
            CL_MEM_READ_WRITE,
            segment_count.checked_mul(TERM_WORDS)?,
        )?;
        let partials = &*partials;
        let bucket_points = self.lease::<u32>(
            "msm.bucket_points",
            CL_MEM_READ_WRITE,
            bucket_total.checked_mul(TERM_WORDS)?,
        )?;
        let bucket_points = &*bucket_points;
        let span = 64usize;
        let ranges = buckets.div_ceil(span);
        let reduced = windows * ranges;
        let out = self.lease_host::<u32>("msm.out", CL_MEM_WRITE_ONLY, reduced * TERM_WORDS)?;
        let out = &*out;
        let (bucket_arg, span_arg, ranges_arg) = (bucket_total as u32, span as u32, ranges as u32);
        let per_window_arg = buckets as u32;
        let scatter = Kernel::create(&self.program, "msm_scatter").ok()?;
        let sums = Kernel::create(&self.program, "msm_segment_sums").ok()?;
        let fold = Kernel::create(&self.program, "msm_bucket_fold").ok()?;
        let reduce = Kernel::create(&self.program, "msm_window_reduce").ok()?;
        // SAFETY: argument orders match the kernels; every work item writes a
        // disjoint slot, and the in-order queue sequences the stages.
        unsafe {
            ExecuteKernel::new(&scatter)
                .set_arg(digits)
                .set_arg(&count_arg)
                .set_arg(&bits_arg)
                .set_arg(&windows_arg)
                .set_arg(cursor)
                .set_arg(order)
                .set_global_work_size(count)
                .enqueue_nd_range(&self.queue)
                .ok()?;
        }
        mark("scatter");
        // SAFETY: as above.
        unsafe {
            ExecuteKernel::new(&sums)
                .set_arg(points)
                .set_arg(order)
                .set_arg(bounds)
                .set_arg(&segment_arg)
                .set_arg(partials)
                .set_global_work_size(segment_count)
                .enqueue_nd_range(&self.queue)
                .ok()?;
        }
        mark("segment sums");
        // Heavy buckets (a sparse witness puts most points in a few) fold in
        // rounds of at most `group` partials, so no work item runs a long
        // serial chain; the last round leaves each bucket ≤ `group` partials.
        let group = 16u32;
        let mut folded: Option<Buffer<u32>> = None;
        let mut per_bucket = bucket_segments_host;
        while per_bucket.windows(2).any(|w| w[1] - w[0] > group) {
            let mut bounds = Vec::new();
            let mut next = Vec::with_capacity(per_bucket.len());
            for w in per_bucket.windows(2) {
                next.push(u32::try_from(bounds.len()).ok()?);
                let mut lo = w[0];
                while lo < w[1] {
                    bounds.push(lo);
                    lo = (lo + group).min(w[1]);
                }
            }
            let groups = u32::try_from(bounds.len()).ok()?;
            next.push(groups);
            bounds.push(*per_bucket.last()?);
            let bounds = self.upload(&bounds, CL_MEM_READ_ONLY)?;
            let out = self.alloc::<u32>(CL_MEM_READ_WRITE, groups as usize * TERM_WORDS)?;
            // SAFETY: argument order matches the kernel; each work item sums one
            // disjoint range of the previous level into its own slot.
            let level = folded.as_ref().unwrap_or(partials);
            unsafe {
                ExecuteKernel::new(&fold)
                    .set_arg(level)
                    .set_arg(&bounds)
                    .set_arg(&groups)
                    .set_arg(&out)
                    .set_global_work_size(groups as usize)
                    .enqueue_nd_range(&self.queue)
                    .ok()?;
            }
            folded = Some(out);
            per_bucket = next;
        }
        let bucket_segments = self.stage_with::<u32>(
            "msm.bucket_segments",
            CL_MEM_READ_ONLY,
            per_bucket.len(),
            |b| b.copy_from_slice(&per_bucket),
        )?;
        let bucket_segments = &*bucket_segments;
        let level = folded.as_ref().unwrap_or(partials);
        // SAFETY: as above.
        unsafe {
            ExecuteKernel::new(&fold)
                .set_arg(level)
                .set_arg(bucket_segments)
                .set_arg(&bucket_arg)
                .set_arg(bucket_points)
                .set_global_work_size(bucket_total)
                .enqueue_nd_range(&self.queue)
                .ok()?;
        }
        mark("bucket fold");
        // SAFETY: as above.
        unsafe {
            ExecuteKernel::new(&reduce)
                .set_arg(bucket_points)
                .set_arg(&per_window_arg)
                .set_arg(&span_arg)
                .set_arg(&ranges_arg)
                .set_arg(&windows_arg)
                .set_arg(out)
                .set_global_work_size(reduced)
                .enqueue_nd_range(&self.queue)
                .ok()?;
        }
        let words = self.download(out, reduced * TERM_WORDS)?;
        mark("window reduce");

        let mut result = G1Projective::zero();
        for window in (0..windows).rev() {
            for _ in 0..bits {
                result.double_in_place();
            }
            for r in 0..ranges {
                let t = window * ranges + r;
                result += jacobian_from_words(&words[t * TERM_WORDS..(t + 1) * TERM_WORDS]);
            }
        }
        mark("host combine");
        if profile {
            eprintln!(
                "  opencl chunk: {count} points, c={bits}, {total} entries, {segment_count} segments, {:.1} ms",
                started.elapsed().as_secs_f64() * 1e3
            );
        }
        Some(result)
    }

    /// A device-owned buffer of `len` elements.
    pub(crate) fn alloc<T>(&self, flags: u64, len: usize) -> Option<Buffer<T>> {
        // SAFETY: a null host pointer requests a device-owned allocation.
        unsafe { Buffer::<T>::create(&self.context, flags, len.max(1), std::ptr::null_mut()) }.ok()
    }

    /// Lease and touch every buffer a proof over `domain_size` points uses
    /// (the H MSM of an uncompressed key and the quotient's transforms), so
    /// its pages are in place before the proof (see [`pool`]). Sizes that
    /// depend on the scalars take their bounds.
    fn prewarm(&self, domain_size: usize) {
        let count = domain_size.saturating_sub(1).max(1);
        let bits = env_usize("XARK_OPENCL_WINDOW_BITS")
            .unwrap_or_else(|| (count.ilog2() as usize).saturating_sub(3))
            .clamp(4, 16);
        let seg_len = env_usize("XARK_OPENCL_SEGMENT").unwrap_or(32).max(1);
        let windows = 256usize.div_ceil(bits);
        let bucket_total = windows << (bits - 1);
        let entries = count * windows;
        let segments = entries / seg_len + bucket_total;
        let host: [(&'static str, u64, usize); 3] = [
            ("msm.scalars", CL_MEM_READ_ONLY, count * 4),
            ("fft.a", CL_MEM_READ_WRITE, domain_size * 4),
            ("fft.b", CL_MEM_READ_WRITE, domain_size * 4),
        ];
        for (role, flags, len) in host {
            drop(self.stage_with::<u64>(role, flags, len, |b| b.fill(0)));
        }
        drop(self.stage_with::<u8>("msm.raw", CL_MEM_READ_ONLY, count * 64, |b| b.fill(0)));
        let host32: [(&'static str, u64, usize); 5] = [
            ("msm.out", CL_MEM_WRITE_ONLY, 1 << 16),
            ("msm.counts", CL_MEM_READ_WRITE, bucket_total),
            ("msm.cursor", CL_MEM_READ_WRITE, bucket_total),
            ("msm.bounds", CL_MEM_READ_ONLY, segments * 3),
            ("msm.bucket_segments", CL_MEM_READ_ONLY, bucket_total + 1),
        ];
        for (role, flags, len) in host32 {
            drop(self.stage_with::<u32>(role, flags, len, |b| b.fill(0)));
        }
        let device: [(&'static str, usize); 5] = [
            ("msm.points", count * 16),
            ("msm.flags", count),
            ("msm.order", entries),
            ("msm.partials", segments * TERM_WORDS),
            ("msm.bucket_points", bucket_total * TERM_WORDS),
        ];
        for (role, len) in device {
            if let Some(mut b) = self.lease::<u32>(role, CL_MEM_READ_WRITE, len) {
                // SAFETY: the fill covers the leased buffer, which nothing else
                // uses until it is given back.
                let _ = unsafe {
                    self.queue
                        .enqueue_fill_buffer(&mut b, &[0u32], 0, len * 4, &[])
                };
            }
        }
        if let Some(mut b) = self.lease::<i16>("msm.digits", CL_MEM_READ_WRITE, entries) {
            // SAFETY: as above.
            let _ = unsafe {
                self.queue
                    .enqueue_fill_buffer(&mut b, &[0i16], 0, entries * 2, &[])
            };
        }
        let _ = self.queue.finish();
    }

    /// A device-only buffer of at least `len` elements for `role`, kept from
    /// call to call (see [`pool`]).
    pub(crate) fn lease<T: Send + 'static>(
        &self,
        role: &'static str,
        flags: u64,
        len: usize,
    ) -> Option<pool::Lease<'_, T>> {
        self.pool.lease(&self.context, role, flags, len)
    }

    /// [`lease`](Self::lease) in host-visible memory the host can map (shared
    /// with the GPU on unified memory), when mapping is enabled.
    pub(crate) fn lease_host<T: Send + 'static>(
        &self,
        role: &'static str,
        flags: u64,
        len: usize,
    ) -> Option<pool::Lease<'_, T>> {
        let host = if mapped_enabled() {
            CL_MEM_ALLOC_HOST_PTR
        } else {
            0
        };
        self.pool.lease(&self.context, role, flags | host, len)
    }

    /// [`lease_host`](Self::lease_host), its first `len` elements written in
    /// place by `fill` (through a staging copy when mapping is disabled).
    pub(crate) fn stage_with<T: Clone + Default + Send + 'static>(
        &self,
        role: &'static str,
        flags: u64,
        len: usize,
        fill: impl FnOnce(&mut [T]),
    ) -> Option<pool::Lease<'_, T>> {
        let mut buffer = self.lease_host::<T>(role, flags, len)?;
        if len == 0 {
            return Some(buffer);
        }
        if !mapped_enabled() {
            let mut staging = zeroed_vec(len, T::default())?;
            fill(&mut staging);
            // SAFETY: `staging` covers the start of the buffer and the write
            // blocks until the copy completes.
            unsafe {
                self.queue
                    .enqueue_write_buffer(&mut buffer, CL_TRUE, 0, &staging, &[])
                    .ok()?;
            }
            return Some(buffer);
        }
        let mut ptr = std::ptr::null_mut();
        // SAFETY: a blocking map of the first `len` elements for writing; the
        // slice lives until the unmap below, and nothing else touches them.
        unsafe {
            self.queue
                .enqueue_map_buffer(
                    &*buffer,
                    CL_TRUE,
                    CL_MAP_WRITE_INVALIDATE_REGION,
                    0,
                    len * std::mem::size_of::<T>(),
                    &mut ptr,
                    &[],
                )
                .ok()?;
            fill(std::slice::from_raw_parts_mut(ptr.cast::<T>(), len));
            self.queue
                .enqueue_unmap_mem_object(buffer.get(), ptr, &[])
                .ok()?;
        }
        Some(buffer)
    }

    /// `read` over the first `len` elements of `buffer`, after all queued work.
    pub(crate) fn download_with<T: Clone + Default, R>(
        &self,
        buffer: &Buffer<T>,
        len: usize,
        read: impl FnOnce(&[T]) -> R,
    ) -> Option<R> {
        if !mapped_enabled() || len == 0 {
            return Some(read(&self.download(buffer, len)?));
        }
        let mut ptr = std::ptr::null_mut();
        // SAFETY: a blocking map of `len` elements for reading; the slice
        // lives until the unmap below.
        unsafe {
            self.queue
                .enqueue_map_buffer(
                    buffer,
                    CL_TRUE,
                    CL_MAP_READ,
                    0,
                    len * std::mem::size_of::<T>(),
                    &mut ptr,
                    &[],
                )
                .ok()?;
            let out = read(std::slice::from_raw_parts(ptr.cast::<T>(), len));
            self.queue
                .enqueue_unmap_mem_object(buffer.get(), ptr, &[])
                .ok()?;
            self.queue.finish().ok()?;
            Some(out)
        }
    }

    /// A device buffer holding a copy of `data` (blocking write).
    pub(crate) fn upload<T>(&self, data: &[T], flags: u64) -> Option<Buffer<T>> {
        let mut buffer = self.alloc::<T>(flags, data.len())?;
        if !data.is_empty() {
            // SAFETY: the slice covers the start of the allocation and the
            // write blocks until the copy completes.
            unsafe {
                self.queue
                    .enqueue_write_buffer(&mut buffer, CL_TRUE, 0, data, &[])
                    .ok()?;
            }
        }
        Some(buffer)
    }

    /// The first `len` elements of `buffer` (blocking read, after all queued work).
    pub(crate) fn download<T: Clone + Default>(
        &self,
        buffer: &Buffer<T>,
        len: usize,
    ) -> Option<Vec<T>> {
        let mut out = zeroed_vec(len, T::default())?;
        // SAFETY: `out` holds exactly `len` elements of the buffer's type.
        unsafe {
            self.queue
                .enqueue_read_buffer(buffer, CL_TRUE, 0, &mut out, &[])
                .ok()?;
        }
        Some(out)
    }

    fn bucket_scratch_fits(&self, scalar_count: usize) -> bool {
        let bucket_bytes = BUCKET_WINDOWS
            .checked_mul(BUCKET_COUNT)
            .and_then(|slots| slots.checked_mul(TERM_WORDS))
            .and_then(|words| words.checked_mul(std::mem::size_of::<u32>()));
        let digit_bytes = scalar_count.checked_mul(BUCKET_WINDOWS);
        bucket_bytes.is_some_and(|bytes| bytes <= self.max_alloc_bytes)
            && digit_bytes.is_some_and(|bytes| bytes <= self.max_alloc_bytes)
    }

    fn run_bucket_chunk(
        &self,
        point_bytes: &[u8],
        encoding: Compress,
        scalars: &[Scalar],
    ) -> Option<G1Projective> {
        let (point_words, scalar_limbs) = prepare_inputs(point_bytes, encoding, scalars)?;
        let count = scalars.len();
        let bucket_slots = BUCKET_WINDOWS.checked_mul(BUCKET_COUNT)?;
        let digit_count = count.checked_mul(BUCKET_WINDOWS)?;
        let bucket_words = bucket_slots.checked_mul(TERM_WORDS)?;
        let window_words = BUCKET_WINDOWS.checked_mul(TERM_WORDS)?;
        let mut result_words = [0u32; POINT_WORDS];

        // SAFETY: every allocation length comes from checked dimensions and all
        // buffers are owned by this runtime's OpenCL context.
        let mut point_buffer = unsafe {
            Buffer::<u32>::create(
                &self.context,
                CL_MEM_READ_ONLY,
                point_words.len(),
                std::ptr::null_mut(),
            )
        }
        .ok()?;
        let prepared_buffer = unsafe {
            Buffer::<u32>::create(
                &self.context,
                CL_MEM_READ_WRITE,
                point_words.len(),
                std::ptr::null_mut(),
            )
        }
        .ok()?;
        let mut scalar_buffer = unsafe {
            Buffer::<u64>::create(
                &self.context,
                CL_MEM_READ_ONLY,
                scalar_limbs.len(),
                std::ptr::null_mut(),
            )
        }
        .ok()?;
        let valid_buffer = unsafe {
            Buffer::<u32>::create(
                &self.context,
                CL_MEM_READ_WRITE,
                count,
                std::ptr::null_mut(),
            )
        }
        .ok()?;
        let digits_buffer = unsafe {
            Buffer::<u8>::create(
                &self.context,
                CL_MEM_READ_WRITE,
                digit_count,
                std::ptr::null_mut(),
            )
        }
        .ok()?;
        let bucket_buffer = unsafe {
            Buffer::<u32>::create(
                &self.context,
                CL_MEM_READ_WRITE,
                bucket_words,
                std::ptr::null_mut(),
            )
        }
        .ok()?;
        let window_buffer = unsafe {
            Buffer::<u32>::create(
                &self.context,
                CL_MEM_READ_WRITE,
                window_words,
                std::ptr::null_mut(),
            )
        }
        .ok()?;
        let result_buffer = unsafe {
            Buffer::<u32>::create(
                &self.context,
                CL_MEM_WRITE_ONLY,
                result_words.len(),
                std::ptr::null_mut(),
            )
        }
        .ok()?;

        // SAFETY: host slices cover the full destination buffers. Blocking
        // writes complete before kernels consume their input.
        unsafe {
            self.queue
                .enqueue_write_buffer(&mut point_buffer, CL_TRUE, 0, &point_words, &[])
                .ok()?;
            self.queue
                .enqueue_write_buffer(&mut scalar_buffer, CL_TRUE, 0, &scalar_limbs, &[])
                .ok()?;
        }

        let count_arg = u64::try_from(count).ok()?;
        let validate = Kernel::create(&self.program, "opencl_msm_validate_bucket_inputs").ok()?;
        // SAFETY: argument order matches the kernel; global size covers each
        // scalar exactly once.
        unsafe {
            ExecuteKernel::new(&validate)
                .set_arg(&point_buffer)
                .set_arg(&scalar_buffer)
                .set_arg(&count_arg)
                .set_arg(&prepared_buffer)
                .set_arg(&valid_buffer)
                .set_arg(&digits_buffer)
                .set_global_work_size(count)
                .enqueue_nd_range(&self.queue)
                .ok()?;
        }
        let buckets = Kernel::create(&self.program, "opencl_msm_buckets").ok()?;
        // SAFETY: each work item writes one disjoint 24-word bucket slot.
        unsafe {
            ExecuteKernel::new(&buckets)
                .set_arg(&prepared_buffer)
                .set_arg(&digits_buffer)
                .set_arg(&valid_buffer)
                .set_arg(&count_arg)
                .set_arg(&bucket_buffer)
                .set_global_work_size(bucket_slots)
                .enqueue_nd_range(&self.queue)
                .ok()?;
        }
        let reduce = Kernel::create(&self.program, "opencl_msm_bucket_windows").ok()?;
        // SAFETY: each work item reduces one disjoint window into its output.
        unsafe {
            ExecuteKernel::new(&reduce)
                .set_arg(&bucket_buffer)
                .set_arg(&window_buffer)
                .set_global_work_size(BUCKET_WINDOWS)
                .enqueue_nd_range(&self.queue)
                .ok()?;
        }
        let finish = Kernel::create(&self.program, "opencl_msm_bucket_finish").ok()?;
        // SAFETY: one work item validates all inputs and writes the fixed-size
        // result; the blocking read waits for all queued kernels.
        unsafe {
            ExecuteKernel::new(&finish)
                .set_arg(&window_buffer)
                .set_arg(&valid_buffer)
                .set_arg(&count_arg)
                .set_arg(&result_buffer)
                .set_global_work_size(1)
                .enqueue_nd_range(&self.queue)
                .ok()?;
            self.queue
                .enqueue_read_buffer(&result_buffer, CL_TRUE, 0, &mut result_words, &[])
                .ok()?;
        }
        if result_words[16] > 1 {
            return None;
        }
        decode_result(&result_words).map(|point| point.into_group())
    }
}

fn estimated_chunk_bytes(count: usize, buckets: bool) -> Option<usize> {
    let word_bytes = std::mem::size_of::<u32>();
    let point_bytes = count.checked_mul(POINT_WORDS)?.checked_mul(word_bytes)?;
    let scalar_bytes = count
        .checked_mul(4)?
        .checked_mul(std::mem::size_of::<u64>())?;
    let valid_bytes = count.checked_mul(word_bytes)?;
    let result_bytes = POINT_WORDS.checked_mul(word_bytes)?;
    let fixed_bytes = if buckets {
        BUCKET_WINDOWS
            .checked_mul(BUCKET_COUNT)?
            .checked_mul(TERM_WORDS)?
            .checked_mul(word_bytes)?
            .checked_add(
                BUCKET_WINDOWS
                    .checked_mul(TERM_WORDS)?
                    .checked_mul(word_bytes)?,
            )?
            .checked_add(count.checked_mul(BUCKET_WINDOWS)?)?
    } else {
        count
            .checked_mul(TERM_WORDS)?
            .checked_mul(word_bytes)?
            .checked_mul(2)?
            .checked_add(valid_bytes)?
    };
    let point_copies = if buckets {
        point_bytes.checked_mul(2)?
    } else {
        point_bytes
    };
    point_copies
        .checked_add(scalar_bytes)?
        .checked_add(valid_bytes)?
        .checked_add(fixed_bytes)?
        .checked_add(result_bytes)
}

fn estimated_host_chunk_bytes(point_bytes: usize, scalar_count: usize) -> Option<usize> {
    let scalar_bytes = scalar_count.checked_mul(std::mem::size_of::<Scalar>())?;
    let prepared_bytes = scalar_count
        .checked_mul(POINT_WORDS.checked_mul(std::mem::size_of::<u32>())?)?
        .checked_add(
            scalar_count
                .checked_mul(4)?
                .checked_mul(std::mem::size_of::<u64>())?,
        )?;
    point_bytes
        .checked_add(scalar_bytes)?
        .checked_add(prepared_bytes)
}

/// Montgomery limbs as 32-bit words (arkworks and the kernels share R = 2^256).
fn montgomery_words(limbs: &[u64; 4]) -> [u32; 8] {
    std::array::from_fn(|i| (limbs[i / 2] >> (32 * (i % 2))) as u32)
}

fn montgomery_field(words: &[u32]) -> Fq {
    Fq::new_unchecked(BigInt(std::array::from_fn(|i| {
        u64::from(words[2 * i]) | (u64::from(words[2 * i + 1]) << 32)
    })))
}

/// A kernel's Jacobian point (x, y, z, 8 Montgomery words each); arkworks'
/// short Weierstrass projective form is Jacobian too.
fn jacobian_from_words(words: &[u32]) -> G1Projective {
    G1Projective::new_unchecked(
        montgomery_field(&words[..8]),
        montgomery_field(&words[8..16]),
        montgomery_field(&words[16..24]),
    )
}

/// `XARK_OPENCL_SPARSE_CPU=0` sends witness-sized MSMs to the GPU too.
/// A witness-sized MSM (most scalars bits, bytes or limbs) costs the CPU
/// almost nothing per point; the GPU's fixed per-point upload and prepare cost
/// does not shrink with the scalars. Leave those to the CPU.
fn prefers_cpu(scalars: &[Scalar]) -> bool {
    if !sparse_to_cpu() || scalars.len() < BUCKET_THRESHOLD {
        return false;
    }
    let wide = scalars
        .iter()
        .filter(|s| s.0[1] | s.0[2] | s.0[3] != 0)
        .count();
    wide * 4 < scalars.len()
}

fn sparse_to_cpu() -> bool {
    std::env::var("XARK_OPENCL_SPARSE_CPU").map_or(true, |v| v != "0")
}

/// `XARK_OPENCL_FFT=0` keeps the quotient transforms on the CPU.
/// Host-visible mapped buffers for inputs and outputs (`XARK_OPENCL_MAPPED=0`
/// copies through device-owned buffers instead).
fn mapped_enabled() -> bool {
    std::env::var("XARK_OPENCL_MAPPED").map_or(true, |v| v != "0")
}

fn gpu_fft_enabled() -> bool {
    std::env::var("XARK_OPENCL_FFT").map_or(true, |v| v != "0")
}

fn env_usize(name: &str) -> Option<usize> {
    std::env::var(name).ok()?.parse().ok()
}

fn find_device(device_type: cl_device_type, device_index: usize) -> Option<(Device, usize)> {
    let platforms = get_platforms().ok()?;
    let mut matching_index = 0;
    for platform in platforms {
        let Ok(devices) = platform.get_devices(device_type) else {
            continue;
        };
        for id in devices {
            let device = Device::new(id);
            if device.available().unwrap_or(false) && device.compiler_available().unwrap_or(false) {
                if matching_index == device_index {
                    return Some((device, id as usize));
                }
                matching_index += 1;
            }
        }
    }
    None
}

fn field_words(value: Fq) -> [u32; 8] {
    let limbs = value.into_bigint().0;
    std::array::from_fn(|index| {
        let word = limbs[index / 2];
        if index % 2 == 0 {
            word as u32
        } else {
            (word >> 32) as u32
        }
    })
}

fn prepare_inputs(
    points: &[u8],
    encoding: Compress,
    scalars: &[Scalar],
) -> Option<(Vec<u32>, Vec<u64>)> {
    let point_size = G1Affine::generator().serialized_size(encoding);
    if points.len() != scalars.len().checked_mul(point_size)? {
        return None;
    }
    let mut point_words = zeroed_vec(scalars.len().checked_mul(POINT_WORDS)?, 0u32)?;
    let mut scalar_limbs = zeroed_vec(scalars.len().checked_mul(4)?, 0u64)?;
    for (index, (bytes, scalar)) in points.chunks_exact(point_size).zip(scalars).enumerate() {
        let point = xark_groth16::decode::point::<G1Affine>(bytes, encoding).ok()?;
        if !point.is_on_curve() || Fr::from_bigint(BigInt(scalar.0)).is_none() {
            return None;
        }
        let words = &mut point_words[index * POINT_WORDS..(index + 1) * POINT_WORDS];
        if point.is_zero() {
            words[16] = 1;
        } else {
            words[..8].copy_from_slice(&field_words(point.x));
            words[8..16].copy_from_slice(&field_words(point.y));
        }
        for limb in 0..4 {
            scalar_limbs[limb * scalars.len() + index] = scalar.0[limb];
        }
    }
    Some((point_words, scalar_limbs))
}

fn decode_result(words: &[u32; POINT_WORDS]) -> Option<G1Affine> {
    if words[16] > 1 {
        return None;
    }
    if words[16] == 1 {
        if words[..16].iter().any(|word| *word != 0) {
            return None;
        }
        return Some(G1Affine::zero());
    }
    let to_field = |limbs: &[u32]| {
        let words =
            std::array::from_fn(|i| u64::from(limbs[2 * i]) | (u64::from(limbs[2 * i + 1]) << 32));
        Fq::from_bigint(BigInt(words))
    };
    let x = to_field(&words[..8])?;
    let y = to_field(&words[8..16])?;
    let point = G1Affine::new_unchecked(x, y);
    point.is_on_curve().then_some(point)
}

fn serialize_point(point: G1Affine) -> Option<Vec<u8>> {
    let mut output = Vec::new();
    point.serialize_uncompressed(&mut output).ok()?;
    Some(output)
}

fn zeroed_vec<T: Clone>(len: usize, value: T) -> Option<Vec<T>> {
    let mut values = Vec::new();
    values.try_reserve_exact(len).ok()?;
    values.resize(len, value);
    Some(values)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn kernel_source_has_the_expected_opencl_entry_points() {
        assert!(MSM_SOURCE.contains("opencl_msm_terms"));
        assert!(MSM_SOURCE.contains("opencl_msm_reduce_pairs"));
        assert!(MSM_SOURCE.contains("opencl_msm_finish"));
        assert!(MSM_SOURCE.contains("validate_msm_scalars"));
        assert!(MSM_SOURCE.contains("opencl_msm_buckets"));
        assert!(MSM_SOURCE.contains("opencl_msm_bucket_windows"));
        assert!(MSM_SOURCE.contains("opencl_msm_bucket_finish"));
    }

    #[test]
    fn empty_g1_msm_returns_the_identity_without_a_device() {
        let mut backend = OpenClMsm::new();
        let result = backend.msm(false, &[], false, &[]).unwrap();
        let decoded = xark_groth16::decode::point::<G1Affine>(&result, Compress::No).unwrap();
        assert!(decoded.is_zero());
    }

    #[test]
    fn malformed_point_buffer_is_declined() {
        let mut backend = OpenClMsm::new();
        let scalar = BigInt([1, 0, 0, 0]);
        assert!(backend.msm(false, &[0; 17], false, &[scalar]).is_none());
    }

    #[test]
    fn chunk_memory_estimates_cover_both_execution_paths() {
        let pointwise = estimated_chunk_bytes(256, false).unwrap();
        let bucket = estimated_chunk_bytes(256, true).unwrap();
        assert!(pointwise > 256 * 17 * 4);
        assert!(bucket > 256 * 17 * 8);
        assert!(bucket > pointwise);
        assert!(estimated_chunk_bytes(usize::MAX, true).is_none());
        assert_eq!(estimated_host_chunk_bytes(32, 1), Some(32 + 32 + 68 + 32));
        assert!(estimated_host_chunk_bytes(usize::MAX, 2).is_none());
    }

    #[test]
    fn msm_kernels_compile_as_opencl_12_when_clang_is_available() {
        // Honor an explicit Makefile compiler override, including wrappers.
        if std::env::var_os("CLANG").is_none()
            && std::process::Command::new("clang")
                .arg("--version")
                .output()
                .is_err_and(|error| error.kind() == std::io::ErrorKind::NotFound)
        {
            eprintln!("skipping the offline syntax check because clang is unavailable");
            return;
        }
        let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("kernels");
        let output = std::process::Command::new("make")
            .arg("-C")
            .arg(directory)
            .arg("test")
            .output();
        let Ok(output) = output else {
            return;
        };
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}
