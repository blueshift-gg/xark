//! CUDA device for xark's Groth16 prover, built the way the OpenCL device
//! (`xark-groth16-opencl`) is: the quotient's three transforms and the dense
//! (H) MSM on an NVIDIA GPU while the CPU takes the witness-sized MSMs, a
//! proof from a 2^18-point domain on ([`DEFAULT_MIN_DOMAIN`]), tables and
//! buffers made during the witness solve ([`Accelerator::prepare`]) and kept
//! from call to call, inputs staged in page-locked host memory.
//!
//! The MSM is the OpenCL device's sorted-bucket pipeline (`kernels/msm_sorted.cu`):
//! points checked and converted on the device, signed digits with a window that
//! grows with the input, the points scattered into bucket order, buckets cut into
//! short segments summed one thread each, then folded and reduced per window.
//! The transforms are its radix-2 Stockham passes (`kernels/fft.cu`).
//!
//! Without the `cuda` feature the crate builds anywhere and the device declines
//! everything, so the prover runs on the CPU. With it, [`CudaMsm::from_env`]
//! reads `XARK_CUDA_MIN_DOMAIN` (the smallest domain it takes a proof for),
//! `XARK_CUDA_FFT=0` (keep the transforms on the CPU), `XARK_CUDA_SPARSE_CPU=0`
//! (offer witness-sized MSMs to the GPU too) and `XARK_CUDA_WINDOW_BITS`.
//!
//! GPU work exposes input-dependent timing and device/driver memory residency:
//! use CPU proving for secret inputs on shared or untrusted hardware.

use ark_bn254::{Fr, G1Affine};
use ark_ec::{AffineRepr, CurveGroup};
use ark_serialize::CanonicalSerialize;
use xark_groth16::{Accelerator, Domain, msm::Scalar};

/// The smallest QAP domain the device takes a proof for, by default, as the
/// OpenCL device's.
pub const DEFAULT_MIN_DOMAIN: usize = 1 << 18;

/// A vector this short is never left to the CPU for being witness-sized.
const BUCKET_THRESHOLD: usize = 256;

/// The NVIDIA GPU the CUDA runtime lists first.
pub struct CudaMsm {
    min_domain: usize,
    /// The device's name, once [`initialize`](Self::initialize) has found it.
    name: Option<String>,
    #[cfg_attr(not(feature = "cuda"), allow(dead_code))]
    tables: std::collections::HashSet<usize>,
}

impl Default for CudaMsm {
    fn default() -> Self {
        Self::new()
    }
}

impl CudaMsm {
    pub fn new() -> Self {
        CudaMsm {
            min_domain: DEFAULT_MIN_DOMAIN,
            name: None,
            tables: Default::default(),
        }
    }

    /// The device `xark prove --prover cuda` uses: [`DEFAULT_MIN_DOMAIN`]
    /// unless `XARK_CUDA_MIN_DOMAIN` says otherwise.
    pub fn from_env() -> Self {
        let min = env_usize("XARK_CUDA_MIN_DOMAIN").unwrap_or(DEFAULT_MIN_DOMAIN);
        Self::new().with_min_domain(min)
    }

    pub fn min_domain(&self) -> usize {
        self.min_domain
    }

    pub fn with_min_domain(mut self, points: usize) -> Self {
        self.min_domain = points;
        self
    }

    /// Finds the GPU and creates its context; false without one (or without the
    /// `cuda` feature).
    pub fn initialize(&mut self) -> bool {
        if self.name.is_none() {
            self.name = gpu::device_name();
        }
        self.name.is_some()
    }

    pub fn device_name(&self) -> Option<&str> {
        self.name.as_deref()
    }

    #[cfg(feature = "cuda")]
    fn transform(&mut self, dom: &Domain, buf: &mut [Fr], kind: gpu::Transform) -> bool {
        self.name.is_some()
            && env_flag("XARK_CUDA_FFT")
            && gpu::transform(&mut self.tables, dom, buf, kind).is_some()
    }

    #[cfg(not(feature = "cuda"))]
    fn transform(&mut self, _: &Domain, _: &mut [Fr], _: gpu::Transform) -> bool {
        false
    }
}

impl Accelerator for CudaMsm {
    fn wants_proof(&self, domain_size: usize) -> bool {
        domain_size >= self.min_domain
    }

    fn to_coset(&mut self, dom: &Domain, buf: &mut [Fr]) -> bool {
        self.transform(dom, buf, gpu::Transform::ToCoset)
    }

    fn from_coset_to_t(&mut self, dom: &Domain, buf: &mut [Fr]) -> bool {
        self.transform(dom, buf, gpu::Transform::FromCosetToT)
    }

    fn ifft_to_t(&mut self, dom: &Domain, buf: &mut [Fr]) -> bool {
        self.transform(dom, buf, gpu::Transform::IfftToT)
    }

    /// Builds the domain's tables, allocates the H MSM's buffers and runs each
    /// kernel once on a few points, so the proof's first launches don't pay
    /// for it (this runs beside the witness solve).
    fn prepare(&mut self, domain_size: usize) {
        if self.name.is_none() {
            return;
        }
        #[cfg(feature = "cuda")]
        gpu::prepare(&mut self.tables, domain_size, env_flag("XARK_CUDA_FFT"));
        #[cfg(not(feature = "cuda"))]
        let _ = domain_size;
    }

    fn wants_msm(&self) -> bool {
        self.name.is_some()
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
        if g2 || self.name.is_none() {
            return None;
        }
        let sum = if scalars.is_empty() {
            G1Affine::zero()
        } else {
            gpu::msm(points, compressed, scalars)?.into_affine()
        };
        let mut out = Vec::new();
        sum.serialize_uncompressed(&mut out).ok()?;
        Some(out)
    }
}

/// A witness-sized MSM (most scalars bits, bytes or limbs) costs the CPU almost
/// nothing per point, while the GPU's upload and prepare cost per point doesn't
/// shrink with the scalars: leave those to the CPU, as the OpenCL device does.
fn prefers_cpu(scalars: &[Scalar]) -> bool {
    if !env_flag("XARK_CUDA_SPARSE_CPU") || scalars.len() < BUCKET_THRESHOLD {
        return false;
    }
    let wide = scalars
        .iter()
        .filter(|s| s.0[1] | s.0[2] | s.0[3] != 0)
        .count();
    wide * 4 < scalars.len()
}

/// Unset or anything but `0`: on.
fn env_flag(name: &str) -> bool {
    std::env::var(name).map_or(true, |v| v != "0")
}

fn env_usize(name: &str) -> Option<usize> {
    std::env::var(name).ok()?.parse().ok()
}

#[cfg(not(feature = "cuda"))]
mod gpu {
    #[derive(Clone, Copy)]
    pub(crate) enum Transform {
        ToCoset,
        FromCosetToT,
        IfftToT,
    }

    pub(crate) fn device_name() -> Option<String> {
        None
    }

    pub(crate) fn msm(
        _: &[u8],
        _: bool,
        _: &[xark_groth16::msm::Scalar],
    ) -> Option<ark_bn254::G1Projective> {
        None
    }
}

#[cfg(feature = "cuda")]
mod gpu {
    use std::collections::HashSet;
    use std::ffi::c_void;
    use std::sync::Mutex;

    use ark_bn254::{Fq, Fr, G1Affine, G1Projective};
    use ark_ec::AffineRepr;
    use ark_ff::{AdditiveGroup, BigInt, FftField, Field, One, Zero};
    use ark_serialize::{CanonicalSerialize, Compress};
    use rayon::prelude::*;
    use xark_groth16::{Domain, msm::Scalar};

    unsafe extern "C" {
        fn xark_cuda_device(name: *mut std::ffi::c_char, len: usize) -> i32;
        fn xark_cuda_pinned(slot: u32, bytes: usize) -> *mut c_void;
        fn xark_cuda_msm_reserve(count: usize, bits: u32, seg_len: u32, span: u32) -> i32;
        fn xark_cuda_sorted_msm_g1(
            points: *const c_void,
            flags: *const u32,
            mode: i32,
            scalars: *const u64,
            count: usize,
            bits: u32,
            seg_len: u32,
            span: u32,
            out: *mut u32,
            out_words: usize,
        ) -> i32;
        fn xark_cuda_fft_tables(
            n: usize,
            forward: *const u64,
            inverse: *const u64,
            to_coset: *const u64,
            from_coset: *const u64,
            n_inv: *const u64,
        ) -> i32;
        fn xark_cuda_fft(n: usize, n1: usize, n2: usize, kind: i32, data: *mut u64) -> i32;
    }

    /// Entries per segment a thread sums (the OpenCL device's `seg_len`).
    const SEGMENT: usize = 32;
    /// Buckets per window-reduce thread (the OpenCL device's `span`).
    const SPAN: usize = 64;
    /// Domains below this keep their transforms on the CPU (launch and copy
    /// overhead win), as the OpenCL device's.
    const MIN_GPU_FFT: usize = 1 << 12;
    /// The prover's default MSM chunk (`ProverConfig::msm_chunk`): the largest
    /// MSM a proof hands the device in one call.
    const MSM_CHUNK: usize = 1 << 19;
    const POWER_CHUNK: usize = 1 << 12;

    /// Held while the page-locked staging buffers are in use.
    static STAGING: Mutex<()> = Mutex::new(());

    #[derive(Clone, Copy)]
    pub(crate) enum Transform {
        ToCoset = 0,
        FromCosetToT = 1,
        IfftToT = 2,
    }

    pub(crate) fn device_name() -> Option<String> {
        let mut name = [0 as std::ffi::c_char; 256];
        // SAFETY: the buffer is writable for its length; the function writes a
        // NUL-terminated name within it.
        if unsafe { xark_cuda_device(name.as_mut_ptr(), name.len()) } != 0 {
            return None;
        }
        // SAFETY: NUL-terminated within the buffer (see above).
        let name = unsafe { std::ffi::CStr::from_ptr(name.as_ptr()) };
        Some(name.to_string_lossy().into_owned())
    }

    /// Staging buffer `slot` as `len` `T`s. Callers hold [`STAGING`] while the
    /// slice lives: the native side keeps each slot's buffer until a larger
    /// request for that slot, which only a later holder of the lock makes.
    ///
    /// # Safety
    /// `STAGING` must be held for the slice's lifetime, and a slot borrowed once
    /// at a time.
    unsafe fn staging<'a, T: Copy>(slot: u32, len: usize) -> Option<&'a mut [T]> {
        let bytes = len.checked_mul(std::mem::size_of::<T>())?;
        // SAFETY: plain allocation call; null on failure.
        let ptr = unsafe { xark_cuda_pinned(slot, bytes) }.cast::<T>();
        if ptr.is_null() {
            return None;
        }
        // SAFETY: page-aligned (so aligned for T), at least `bytes` long, and
        // exclusive per the function's contract.
        Some(unsafe { std::slice::from_raw_parts_mut(ptr, len) })
    }

    fn window_bits(count: usize) -> usize {
        super::env_usize("XARK_CUDA_WINDOW_BITS")
            .unwrap_or_else(|| (count.max(1).ilog2() as usize).saturating_sub(3))
            .clamp(4, 16)
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

    pub(crate) fn msm(points: &[u8], compressed: bool, scalars: &[Scalar]) -> Option<G1Projective> {
        let count = scalars.len();
        let bits = window_bits(count);
        let windows = 256usize.div_ceil(bits);
        let ranges = (1usize << (bits - 1)).div_ceil(SPAN);
        let mut out = vec![0u32; windows.checked_mul(ranges)?.checked_mul(24)?];
        let _held = STAGING.lock().ok()?;
        // SAFETY: STAGING is held; each slot is borrowed once.
        let limbs = unsafe { staging::<u64>(1, count.checked_mul(4)?) }?;
        limbs
            .par_chunks_mut(4)
            .zip(scalars.par_iter())
            .for_each(|(dst, s)| dst.copy_from_slice(&s.0));
        let (input, flags, mode): (*const c_void, *const u32, i32) = if compressed {
            let size = G1Affine::generator().serialized_size(Compress::Yes);
            if points.len() != count.checked_mul(size)? {
                return None;
            }
            // SAFETY: as above.
            let words = unsafe { staging::<u32>(0, count.checked_mul(16)?) }?;
            // SAFETY: as above.
            let flags = unsafe { staging::<u32>(3, count) }?;
            words
                .par_chunks_mut(16)
                .zip(flags.par_iter_mut())
                .zip(points.par_chunks_exact(size))
                .try_for_each(|((words, flag), bytes)| {
                    let point =
                        xark_groth16::decode::point::<G1Affine>(bytes, Compress::Yes).ok()?;
                    if !point.is_on_curve() {
                        return None;
                    }
                    *flag = u32::from(point.is_zero());
                    if !point.is_zero() {
                        words[..8].copy_from_slice(&montgomery_words(&point.x.0.0));
                        words[8..].copy_from_slice(&montgomery_words(&point.y.0.0));
                    }
                    Some(())
                })?;
            (words.as_ptr().cast(), flags.as_ptr(), 1)
        } else {
            if points.len() != count.checked_mul(64)? {
                return None;
            }
            // SAFETY: as above.
            let raw = unsafe { staging::<u8>(0, points.len()) }?;
            raw.par_chunks_mut(1 << 20)
                .zip(points.par_chunks(1 << 20))
                .for_each(|(dst, src)| dst.copy_from_slice(src));
            (raw.as_ptr().cast(), std::ptr::null(), 0)
        };
        // SAFETY: `input` holds `count` points in the layout `mode` names,
        // `flags` (mode 1) `count` words, `limbs` 4 per scalar, `out` exactly
        // windows × ranges × 24 words; the call keeps no pointer.
        let status = unsafe {
            xark_cuda_sorted_msm_g1(
                input,
                flags,
                mode,
                limbs.as_ptr(),
                count,
                bits as u32,
                SEGMENT as u32,
                SPAN as u32,
                out.as_mut_ptr(),
                out.len(),
            )
        };
        if status != 0 {
            return None;
        }
        let mut result = G1Projective::zero();
        for window in (0..windows).rev() {
            for _ in 0..bits {
                result.double_in_place();
            }
            for r in 0..ranges {
                let words = &out[(window * ranges + r) * 24..][..24];
                result += G1Projective::new_unchecked(
                    montgomery_field(&words[..8]),
                    montgomery_field(&words[8..16]),
                    montgomery_field(&words[16..]),
                );
            }
        }
        Some(result)
    }

    pub(crate) fn transform(
        tables: &mut HashSet<usize>,
        dom: &Domain,
        buf: &mut [Fr],
        kind: Transform,
    ) -> Option<()> {
        let n = dom.n;
        if !n.is_power_of_two() || n < MIN_GPU_FFT || buf.len() != n || dom.n1 * dom.n2 != n {
            return None;
        }
        let _held = STAGING.lock().ok()?;
        if !tables.contains(&n) {
            upload_tables(n)?;
            tables.insert(n);
        }
        // SAFETY: STAGING is held; the slot is borrowed once.
        let data = unsafe { staging::<u64>(2, n.checked_mul(4)?) }?;
        data.par_chunks_mut(4)
            .zip(buf.par_iter())
            .for_each(|(dst, x)| dst.copy_from_slice(&x.0.0));
        // SAFETY: `data` holds n elements of 4 limbs; the call keeps no pointer.
        let status = unsafe { xark_cuda_fft(n, dom.n1, dom.n2, kind as i32, data.as_mut_ptr()) };
        if status != 0 {
            return None;
        }
        buf.par_iter_mut()
            .zip(data.par_chunks(4))
            .for_each(|(x, l)| *x = Fr::new_unchecked(BigInt([l[0], l[1], l[2], l[3]])));
        Some(())
    }

    /// Twiddles and coset factors for domain size `n`, as the OpenCL device's.
    fn upload_tables(n: usize) -> Option<()> {
        let omega = Fr::get_root_of_unity(n as u64)?;
        let g = Fr::GENERATOR;
        let n_inv = Fr::from(n as u64).inverse()?;
        let forward = powers(omega, Fr::one(), n / 2);
        let inverse = powers(omega.inverse()?, Fr::one(), n / 2);
        let to_coset = powers(g, n_inv, n);
        let from_coset = powers(g.inverse()?, n_inv, n);
        let one = powers(Fr::one(), n_inv, 1);
        // SAFETY: each table holds the element count the function reads.
        let status = unsafe {
            xark_cuda_fft_tables(
                n,
                forward.as_ptr(),
                inverse.as_ptr(),
                to_coset.as_ptr(),
                from_coset.as_ptr(),
                one.as_ptr(),
            )
        };
        (status == 0).then_some(())
    }

    /// `scale·base^j` for `j < count`, as Montgomery limbs, built in parallel chunks.
    fn powers(base: Fr, scale: Fr, count: usize) -> Vec<u64> {
        let mut out = vec![0u64; count * 4];
        out.par_chunks_mut(POWER_CHUNK * 4)
            .enumerate()
            .for_each(|(chunk, limbs)| {
                let mut x = scale * base.pow([(chunk * POWER_CHUNK) as u64]);
                for l in limbs.chunks_mut(4) {
                    l.copy_from_slice(&x.0.0);
                    x *= base;
                }
            });
        out
    }

    pub(crate) fn prepare(tables: &mut HashSet<usize>, domain_size: usize, fft: bool) {
        if fft && domain_size.is_power_of_two() && domain_size >= MIN_GPU_FFT {
            if let Ok(_held) = STAGING.lock()
                && !tables.contains(&domain_size)
                && upload_tables(domain_size).is_some()
            {
                tables.insert(domain_size);
            }
            if let Some(dom) = Domain::new(MIN_GPU_FFT, Default::default()) {
                let mut buf = vec![Fr::from(1u64); dom.n];
                for kind in [
                    Transform::ToCoset,
                    Transform::FromCosetToT,
                    Transform::IfftToT,
                ] {
                    let _ = transform(tables, &dom, &mut buf, kind);
                }
            }
        }
        // The H MSM's buffers, device and staging, at the size it will come in.
        let count = domain_size.saturating_sub(1).clamp(1, MSM_CHUNK);
        // SAFETY: plain allocation call.
        let _ = unsafe {
            xark_cuda_msm_reserve(
                count,
                window_bits(count) as u32,
                SEGMENT as u32,
                SPAN as u32,
            )
        };
        if let Ok(_held) = STAGING.lock() {
            // SAFETY: STAGING is held; the slices are dropped at once.
            unsafe {
                let _ = staging::<u8>(0, count * 64);
                let _ = staging::<u64>(1, count * 4);
            }
        }
        let count = super::BUCKET_THRESHOLD * 2;
        let mut points = Vec::new();
        for _ in 0..count {
            let _ = G1Affine::generator().serialize_uncompressed(&mut points);
        }
        let scalars: Vec<Scalar> = (0..count as u64)
            .map(|i| BigInt([i.wrapping_mul(0x9e37_79b9_7f4a_7c15), i, i ^ 0x5555, 1]))
            .collect();
        let _ = msm(&points, false, &scalars);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::{BigInt, UniformRand};
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    #[test]
    fn witness_sized_vectors_stay_on_the_cpu() {
        let narrow = vec![BigInt([3, 0, 0, 0]); 1024];
        let mut wide = narrow.clone();
        for s in wide.iter_mut().step_by(2) {
            s.0[2] = 1;
        }
        assert!(prefers_cpu(&narrow));
        assert!(!prefers_cpu(&wide));
        assert!(!prefers_cpu(&narrow[..BUCKET_THRESHOLD - 1]));
    }

    #[test]
    fn the_device_declines_small_domains() {
        let device = CudaMsm::new().with_min_domain(1 << 10);
        assert!(!device.wants_proof(1 << 9));
        assert!(device.wants_proof(1 << 10));
    }

    /// The GPU, or `None` where there is none (a failure under
    /// `XARK_CUDA_REQUIRED`).
    fn gpu() -> Option<CudaMsm> {
        let mut device = CudaMsm::new();
        if device.initialize() {
            return Some(device);
        }
        assert!(
            std::env::var_os("XARK_CUDA_REQUIRED").is_none(),
            "XARK_CUDA_REQUIRED is set but no CUDA device was found"
        );
        None
    }

    #[test]
    fn msm_matches_the_cpu() {
        use ark_bn254::G1Projective;
        use ark_ec::CurveGroup;
        use ark_ff::PrimeField;
        use ark_serialize::{CanonicalSerialize, Compress};
        let Some(mut device) = gpu() else {
            return;
        };
        let mut rng = ChaCha20Rng::seed_from_u64(7);
        for n in [1usize, 255, 256, 3000, 70_000] {
            let mut points: Vec<G1Affine> = (0..n)
                .map(|_| (G1Affine::generator() * Fr::rand(&mut rng)).into_affine())
                .collect();
            let mut scalars: Vec<Scalar> =
                (0..n).map(|_| Fr::rand(&mut rng).into_bigint()).collect();
            if n > 2 {
                points[1] = G1Affine::zero();
                scalars[2] = BigInt([0; 4]);
                // A point that appears twice in one bucket (the doubling path).
                points[0] = points[n - 1];
                scalars[0] = scalars[n - 1];
            }
            let expected = xark_groth16::msm::msm::<G1Projective>(&points, &scalars).into_affine();
            for compress in [Compress::Yes, Compress::No] {
                let mut bytes = Vec::new();
                for p in &points {
                    p.serialize_with_mode(&mut bytes, compress).unwrap();
                }
                let out = device
                    .msm(false, &bytes, compress == Compress::Yes, &scalars)
                    .expect("the GPU declined a valid MSM");
                let mut want = Vec::new();
                expected.serialize_uncompressed(&mut want).unwrap();
                let compressed = compress == Compress::Yes;
                assert_eq!(out, want, "n = {n}, compressed = {compressed}");
            }
        }
    }

    #[test]
    fn msm_declines_a_point_off_the_curve() {
        use ark_serialize::CanonicalSerialize;
        let Some(mut device) = gpu() else {
            return;
        };
        let mut bytes = Vec::new();
        G1Affine::generator()
            .serialize_uncompressed(&mut bytes)
            .unwrap();
        bytes[3] ^= 1;
        assert!(
            device
                .msm(false, &bytes, false, &[BigInt([5, 0, 0, 0])])
                .is_none()
        );
    }

    #[test]
    fn transforms_match_the_cpu() {
        use ark_ff::{FftField, Field};
        let Some(mut device) = gpu() else {
            return;
        };
        let mut rng = ChaCha20Rng::seed_from_u64(11);
        for log in [12u32, 13, 16] {
            let dom = Domain::new(1 << log, Default::default()).unwrap();
            let input: Vec<Fr> = (0..dom.n).map(|_| Fr::rand(&mut rng)).collect();
            let g = Fr::GENERATOR;
            for kind in 0..3 {
                let mut want = input.clone();
                let mut got = input.clone();
                let (name, taken) = match kind {
                    0 => {
                        dom.to_coset(&mut want, g);
                        ("to_coset", device.to_coset(&dom, &mut got))
                    }
                    1 => {
                        dom.from_coset_to_t(&mut want, g.inverse().unwrap());
                        ("from_coset_to_t", device.from_coset_to_t(&dom, &mut got))
                    }
                    _ => {
                        dom.ifft_to_t(&mut want);
                        ("ifft_to_t", device.ifft_to_t(&dom, &mut got))
                    }
                };
                assert!(taken, "{name} declined at 2^{log}");
                assert!(got == want, "{name} differs at 2^{log}");
            }
        }
    }
}
