//! OpenCL coset transforms for the Groth16 quotient (power-of-two domains).
//!
//! Radix-2 Stockham passes keep natural order in and out; the coset scaling
//! (with the `1/n` of the inverse transform folded in) and the T-layout
//! transpose are one element-wise kernel each. Twiddles and coset factors are
//! built on the host once per domain size and kept on the device for the life
//! of the runtime.

use ark_bn254::Fr;
use ark_ff::{FftField, Field, One};
use opencl3::{
    kernel::ExecuteKernel, kernel::Kernel, memory::Buffer, memory::CL_MEM_READ_ONLY,
    memory::CL_MEM_READ_WRITE,
};
use rayon::prelude::*;
use xark_groth16::Domain;

use crate::Runtime;

/// Domains below this size stay on the CPU (transfer and launch overhead win).
pub(crate) const MIN_GPU_FFT: usize = 1 << 12;

/// Elements per parallel chunk when building power tables.
const POWER_CHUNK: usize = 1 << 12;

/// Device tables for one domain size.
pub(crate) struct Tables {
    /// ω^j and ω^-j for j < n/2.
    forward: Buffer<u64>,
    inverse: Buffer<u64>,
    /// (1/n)·g^i and (1/n)·g^-i for i < n.
    to_coset: Buffer<u64>,
    from_coset: Buffer<u64>,
    /// 1/n, for the plain inverse DFT.
    n_inv: Buffer<u64>,
}

/// The three transforms the quotient asks of the device.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Transform {
    /// Evaluations → coset evaluations, natural order.
    ToCoset,
    /// Coset evaluations → coefficients in the domain's T-layout.
    FromCosetToT,
    /// Evaluations → coefficients in the domain's T-layout.
    IfftToT,
}

impl Runtime {
    /// `buf` through `transform`: an inverse DFT, a scaling (by the coset's
    /// factors with the `1/n` folded in, or `1/n` alone), then a forward DFT
    /// onto the coset or a transpose into T-layout.
    pub(crate) fn coset_transform(
        &mut self,
        dom: &Domain,
        buf: &mut [Fr],
        transform: Transform,
    ) -> Option<()> {
        let to_coset = transform == Transform::ToCoset;
        let n = dom.n;
        if !n.is_power_of_two() || n < MIN_GPU_FFT || buf.len() != n || dom.n1 * dom.n2 != n {
            return None;
        }
        let n_arg = u32::try_from(n).ok()?;
        let started = std::time::Instant::now();
        let profile = std::env::var_os("XARK_OPENCL_PROFILE").is_some();
        let mut lap = started;
        let mark = |stage: &str, lap: &mut std::time::Instant| {
            if profile {
                let _ = self.queue.finish();
                let now = std::time::Instant::now();
                eprintln!(
                    "    opencl fft {stage}: {:.2} ms",
                    (now - *lap).as_secs_f64() * 1e3
                );
                *lap = now;
            }
        };
        if !self.twiddles.contains_key(&n) {
            let tables = self.tables(n)?;
            self.twiddles.insert(n, tables);
        }
        mark("tables", &mut lap);
        let tables = self.twiddles.get(&n)?;

        let words = n.checked_mul(4)?;
        let input = self.upload_with::<u64>(CL_MEM_READ_WRITE, words, |limbs| {
            limbs
                .par_chunks_mut(4)
                .zip(buf.par_iter())
                .for_each(|(out, x)| out.copy_from_slice(&x.0.0))
        })?;
        let buffers = [input, self.alloc_io::<u64>(words)?];
        mark("upload", &mut lap);
        let mut current = self.passes(&buffers, 0, &tables.inverse, n)?;
        mark("inverse passes", &mut lap);
        let (factors, scale) = match transform {
            Transform::ToCoset => (&tables.to_coset, "fr_scale"),
            Transform::FromCosetToT => (&tables.from_coset, "fr_scale"),
            Transform::IfftToT => (&tables.n_inv, "fr_scale_one"),
        };
        let kernel = Kernel::create(&self.program, scale).ok()?;
        // SAFETY: argument order matches the kernel; one item per element.
        unsafe {
            ExecuteKernel::new(&kernel)
                .set_arg(&buffers[current])
                .set_arg(factors)
                .set_arg(&n_arg)
                .set_global_work_size(n)
                .enqueue_nd_range(&self.queue)
                .ok()?;
        }
        mark("scale", &mut lap);
        if to_coset {
            current = self.passes(&buffers, current, &tables.forward, n)?;
        } else if dom.n1 > 1 {
            let kernel = Kernel::create(&self.program, "fr_transpose").ok()?;
            let (n1, n2) = (dom.n1 as u32, dom.n2 as u32);
            // SAFETY: argument order matches the kernel; one item per element
            // of the destination, which is disjoint from the source.
            unsafe {
                ExecuteKernel::new(&kernel)
                    .set_arg(&buffers[current])
                    .set_arg(&buffers[1 - current])
                    .set_arg(&n1)
                    .set_arg(&n2)
                    .set_global_work_size(n)
                    .enqueue_nd_range(&self.queue)
                    .ok()?;
            }
            current = 1 - current;
        }
        mark("forward passes", &mut lap);
        self.download_with(&buffers[current], words, |limbs| {
            buf.par_iter_mut()
                .zip(limbs.par_chunks(4))
                .for_each(|(x, l)| *x = Fr::new_unchecked(ark_ff::BigInt([l[0], l[1], l[2], l[3]])))
        })?;
        mark("download", &mut lap);
        if profile {
            eprintln!(
                "  opencl {}: n=2^{} {:.1} ms",
                match transform {
                    Transform::ToCoset => "to_coset",
                    Transform::FromCosetToT => "from_coset_to_t",
                    Transform::IfftToT => "ifft_to_t",
                },
                n.trailing_zeros(),
                started.elapsed().as_secs_f64() * 1e3
            );
        }
        Some(())
    }

    pub(crate) fn tables(&self, n: usize) -> Option<Tables> {
        let omega = Fr::get_root_of_unity(n as u64)?;
        let g = Fr::GENERATOR;
        let n_inv = Fr::from(n as u64).inverse()?;
        let table =
            |base: Fr, scale: Fr, count| self.upload(&powers(base, scale, count), CL_MEM_READ_ONLY);
        Some(Tables {
            forward: table(omega, Fr::one(), n / 2)?,
            inverse: table(omega.inverse()?, Fr::one(), n / 2)?,
            to_coset: table(g, n_inv, n)?,
            from_coset: table(g.inverse()?, n_inv, n)?,
            n_inv: table(Fr::one(), n_inv, 1)?,
        })
    }

    /// log₂ n Stockham passes ping-ponging between `buffers`; returns the
    /// index holding the result.
    fn passes(
        &self,
        buffers: &[Buffer<u64>; 2],
        mut current: usize,
        twiddles: &Buffer<u64>,
        n: usize,
    ) -> Option<usize> {
        let kernel = Kernel::create(&self.program, "fr_fft_radix2").ok()?;
        let half = (n / 2) as u32;
        let mut p = 1u32;
        while p <= half {
            // SAFETY: argument order matches the kernel; each pass reads one
            // buffer and writes the other.
            unsafe {
                ExecuteKernel::new(&kernel)
                    .set_arg(&buffers[current])
                    .set_arg(&buffers[1 - current])
                    .set_arg(twiddles)
                    .set_arg(&p)
                    .set_arg(&half)
                    .set_global_work_size(n / 2)
                    .enqueue_nd_range(&self.queue)
                    .ok()?;
            }
            current = 1 - current;
            p <<= 1;
        }
        Some(current)
    }
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
