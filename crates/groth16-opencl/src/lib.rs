//! Optional OpenCL BN254 G1 MSM backend for Xark's Groth16 prover.
//!
//! Small inputs use independent scalar-point products. Inputs of 256 or more
//! scalars use a 4-bit bucket MSM. The dispatch point is an initial heuristic,
//! not a measured crossover; run `cargo run --release --example msm_bench
//! --manifest-path crates/groth16-opencl/Cargo.toml` on the target GPU before
//! treating it as a performance choice. Both kernels are variable-time.
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
//! GPU work exposes input-dependent timing and device/driver memory residency.
//! Neither OpenCL nor CUDA is claimed constant-time or guaranteed to erase device
//! memory. Use CPU proving for secret inputs on shared or untrusted hardware.

use std::ops::Range;

use ark_bn254::{Fq, Fr, G1Affine, G1Projective};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{BigInt, PrimeField, Zero};
use ark_serialize::{CanonicalSerialize, Compress};
use opencl3::{
    command_queue::CommandQueue,
    context::Context,
    device::{CL_DEVICE_TYPE_ALL, CL_DEVICE_TYPE_GPU, Device},
    kernel::{ExecuteKernel, Kernel},
    memory::{Buffer, CL_MEM_READ_ONLY, CL_MEM_READ_WRITE, CL_MEM_WRITE_ONLY, CL_TRUE},
    platform::get_platforms,
    program::Program,
    types::cl_device_type,
};
use xark_groth16::{Accelerator, msm::Scalar};
mod scheduler;
use scheduler::DeviceScheduler;

const MSM_SOURCE: &str = concat!(
    include_str!("../../groth16/opencl/msm_pointwise.cl"),
    "\n",
    include_str!("../../groth16/opencl/msm_digits.cl"),
    "\n",
    include_str!("../../groth16/opencl/msm_bucket.cl"),
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
    runtime: Option<Runtime>,
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
        let device_type = match kind {
            OpenClDeviceKind::Gpu => CL_DEVICE_TYPE_GPU,
            OpenClDeviceKind::Any => CL_DEVICE_TYPE_ALL,
        };
        Self {
            device_type,
            runtime: None,
        }
    }

    /// Load the device and build the kernels. Returns false when the runtime
    /// or compiler is unavailable, allowing callers to report a clean fallback.
    pub fn initialize(&mut self) -> bool {
        self.runtime().is_some()
    }

    fn runtime(&mut self) -> Option<&mut Runtime> {
        if self.runtime.is_none() {
            self.runtime = Runtime::new(self.device_type);
        }
        self.runtime.as_mut()
    }
}

impl Accelerator for OpenClMsm {
    fn wants_msm(&self) -> bool {
        find_device(self.device_type).is_some()
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
}

impl Runtime {
    fn new(device_type: cl_device_type) -> Option<Self> {
        let (device, device_id) = find_device(device_type)?;
        let context = Context::from_device(&device).ok()?;
        let queue = CommandQueue::create_default(&context, 0).ok()?;
        let program =
            Program::create_and_build_from_source(&context, MSM_SOURCE, "-cl-std=CL1.2").ok()?;
        let max_alloc_bytes = usize::try_from(device.max_mem_alloc_size().ok()?).ok()?;
        let global_mem_bytes = usize::try_from(device.global_mem_size().ok()?).ok()?;
        let scheduler = scheduler::for_device(device_id, global_mem_bytes)?;
        Some(Self {
            context,
            queue,
            program,
            max_alloc_bytes,
            scheduler,
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
            && self.bucket_scratch_fits()
            && bucket_bytes.is_some_and(|bytes| bytes <= self.scheduler.memory_budget_bytes());
        let host_bytes = estimated_host_chunk_bytes(point_bytes.len(), scalars.len())?;
        let _permit = self.scheduler.acquire(
            estimated_chunk_bytes(scalars.len(), use_buckets)?,
            host_bytes,
        )?;
        if use_buckets {
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

    fn bucket_scratch_fits(&self) -> bool {
        BUCKET_WINDOWS
            .checked_mul(BUCKET_COUNT)
            .and_then(|slots| slots.checked_mul(TERM_WORDS))
            .and_then(|words| words.checked_mul(std::mem::size_of::<u32>()))
            .is_some_and(|bytes| bytes <= self.max_alloc_bytes)
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
                .set_global_work_size(count)
                .enqueue_nd_range(&self.queue)
                .ok()?;
        }
        let buckets = Kernel::create(&self.program, "opencl_msm_buckets").ok()?;
        // SAFETY: each work item writes one disjoint 24-word bucket slot.
        unsafe {
            ExecuteKernel::new(&buckets)
                .set_arg(&prepared_buffer)
                .set_arg(&scalar_buffer)
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

fn find_device(device_type: cl_device_type) -> Option<(Device, usize)> {
    let platforms = get_platforms().ok()?;
    for platform in platforms {
        let Ok(devices) = platform.get_devices(device_type) else {
            continue;
        };
        for id in devices {
            let device = Device::new(id);
            if device.available().unwrap_or(false) && device.compiler_available().unwrap_or(false) {
                return Some((device, id as usize));
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
        let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../groth16/opencl");
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
