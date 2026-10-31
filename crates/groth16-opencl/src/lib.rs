//! Optional OpenCL BN254 G1 MSM backend for Xark's Groth16 prover.
//!
//! The first kernel version computes each scalar-point product independently,
//! then reduces the projective terms on device. This is a correctness baseline;
//! performance needs measurement before moving this backend to windowed buckets.

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

const MSM_SOURCE: &str = concat!(
    include_str!("../../groth16/opencl/msm_pointwise.cl"),
    "\n",
    include_str!("../../groth16/opencl/msm_digits.cl"),
);
const POINT_WORDS: usize = 17;
const TERM_WORDS: usize = 24;

/// OpenCL backend. Its scalar multiplication is variable-time and may expose
/// scalar-dependent timing; use it only when the device is trusted. The default
/// constructor selects a GPU; `with_any_device` also permits CPU OpenCL runtimes
/// for correctness testing.
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
    global_mem_bytes: usize,
}

impl Runtime {
    fn new(device_type: cl_device_type) -> Option<Self> {
        let device = find_device(device_type)?;
        let context = Context::from_device(&device).ok()?;
        let queue = CommandQueue::create_default(&context, 0).ok()?;
        let program =
            Program::create_and_build_from_source(&context, MSM_SOURCE, "-cl-std=CL1.2").ok()?;
        let max_alloc_bytes = usize::try_from(device.max_mem_alloc_size().ok()?).ok()?;
        let global_mem_bytes = usize::try_from(device.global_mem_size().ok()?).ok()?;
        Some(Self {
            context,
            queue,
            program,
            max_alloc_bytes,
            global_mem_bytes,
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
        let by_global = self.global_mem_bytes.checked_div(live_bytes_per_point)?;
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
}

fn find_device(device_type: cl_device_type) -> Option<Device> {
    let platforms = get_platforms().ok()?;
    for platform in platforms {
        let Ok(devices) = platform.get_devices(device_type) else {
            continue;
        };
        for id in devices {
            let device = Device::new(id);
            if device.available().unwrap_or(false) && device.compiler_available().unwrap_or(false) {
                return Some(device);
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
        let scalar = Scalar([1, 0, 0, 0]);
        assert!(backend.msm(false, &[0; 17], false, &[scalar]).is_none());
    }

    #[test]
    fn pointwise_kernel_compiles_as_opencl_12_when_clang_is_available() {
        let source = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../groth16/opencl/msm_pointwise.cl");
        let output = std::process::Command::new("clang")
            .args(["-x", "cl", "-cl-std=CL1.2", "-Werror", "-fsyntax-only"])
            .arg(source)
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
