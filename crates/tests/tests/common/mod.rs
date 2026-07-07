//! Shared test support for this crate's integration tests:
//!
//! * [`build_valid_ptau`] — a programmatic Powers-of-Tau builder (snarkjs binary
//!   layout) so the ceremony/ptau tests need no snarkjs and no committed
//!   multi-hundred-MiB `.ptau`. The toxic waste (`τ, α, β`) is known to the test
//!   by construction — these tests check pipeline *correctness*, not *secrecy*.
//! * [`fixture_dir`] / [`tempdir`] / [`run`] — the fixture, temp-dir, and `xark`
//!   binary-runner helpers shared by the CLI integration tests.
//! * [`assert_circuit_proves`] — the in-process Groth16 setup→prove→verify
//!   pipeline used by the per-circuit tests (no subprocess, no stdout parsing).
#![allow(dead_code)] // each integration-test binary uses only a subset of these.

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use ark_bn254::{Fq, Fr, G1Affine, G2Affine};
use ark_ec::{AdditiveGroup, AffineRepr, CurveGroup, PrimeGroup};
use ark_ff::{BigInteger, Field, PrimeField, UniformRand};
use ark_std::rand::SeedableRng;
use rand_chacha::ChaCha20Rng;

use xark_backend::ptau::__fq_to_le_mont_bytes_for_tests as fq_to_mont;

/// Build a programmatic ptau file by sampling a τ, α, β ∈ Fr, computing the
/// expected powers, and serializing them in the snarkjs binary layout.
///
/// `power` must satisfy `2^power >= constraint-system domain size` for whatever
/// circuit consumes the transcript. Keep it small (1–4) so the buffer stays a
/// few kilobytes.
pub fn build_valid_ptau(power: u32) -> Vec<u8> {
    let mut rng = ChaCha20Rng::seed_from_u64(0x00C0_FFEE_F00D);
    let tau = Fr::rand(&mut rng);
    let alpha = Fr::rand(&mut rng);
    let beta = Fr::rand(&mut rng);

    let two_to_p = 1usize << power;
    let g1 = ark_bn254::G1Projective::generator();
    let g2 = ark_bn254::G2Projective::generator();

    // [τ^0]G1... [τ^(2·2^p - 2)]G1
    let n_tau_g1 = 2 * two_to_p - 1;
    let mut tau_g1 = Vec::with_capacity(n_tau_g1);
    let mut acc = Fr::ONE;
    for _ in 0..n_tau_g1 {
        tau_g1.push((g1 * acc).into_affine());
        acc *= tau;
    }

    // [τ^0]G2... [τ^(2^p - 1)]G2
    let mut tau_g2 = Vec::with_capacity(two_to_p);
    acc = Fr::ONE;
    for _ in 0..two_to_p {
        tau_g2.push((g2 * acc).into_affine());
        acc *= tau;
    }

    // [α·τ^i]G1
    let mut alpha_tau_g1 = Vec::with_capacity(two_to_p);
    acc = alpha;
    for _ in 0..two_to_p {
        alpha_tau_g1.push((g1 * acc).into_affine());
        acc *= tau;
    }

    // [β·τ^i]G1
    let mut beta_tau_g1 = Vec::with_capacity(two_to_p);
    acc = beta;
    for _ in 0..two_to_p {
        beta_tau_g1.push((g1 * acc).into_affine());
        acc *= tau;
    }

    let beta_g2 = (g2 * beta).into_affine();

    serialize_ptau(
        power,
        &tau_g1,
        &tau_g2,
        &alpha_tau_g1,
        &beta_tau_g1,
        &beta_g2,
    )
}

fn serialize_ptau(
    power: u32,
    tau_g1: &[G1Affine],
    tau_g2: &[G2Affine],
    alpha_tau_g1: &[G1Affine],
    beta_tau_g1: &[G1Affine],
    beta_g2: &G2Affine,
) -> Vec<u8> {
    let mut out = Vec::new();
    // Magic, version, num_sections.
    out.extend_from_slice(b"ptau");
    out.extend_from_slice(&1u32.to_le_bytes()); // version
    out.extend_from_slice(&7u32.to_le_bytes()); // 6 data sections + 1 contributions section

    // Section 1: header.
    let modulus_bytes = Fq::MODULUS.to_bytes_le(); // 32 bytes LE
    let mut header_payload = Vec::new();
    header_payload.extend_from_slice(&32u32.to_le_bytes()); // n8
    header_payload.extend_from_slice(&modulus_bytes); // p
    header_payload.extend_from_slice(&power.to_le_bytes());
    header_payload.extend_from_slice(&power.to_le_bytes()); // ceremony_power (mirrors `power`)
    write_section(&mut out, 1, &header_payload);

    // Section 2: tau_g1.
    write_section(&mut out, 2, &serialize_g1_vec(tau_g1));
    // Section 3: tau_g2.
    write_section(&mut out, 3, &serialize_g2_vec(tau_g2));
    // Section 4: alpha_tau_g1.
    write_section(&mut out, 4, &serialize_g1_vec(alpha_tau_g1));
    // Section 5: beta_tau_g1.
    write_section(&mut out, 5, &serialize_g1_vec(beta_tau_g1));
    // Section 6: beta_g2.
    write_section(&mut out, 6, &serialize_g2_vec(&[*beta_g2]));
    // Section 7: contributions (empty).
    write_section(&mut out, 7, &[]);

    out
}

fn write_section(out: &mut Vec<u8>, ty: u32, payload: &[u8]) {
    out.extend_from_slice(&ty.to_le_bytes());
    out.extend_from_slice(&(payload.len() as u64).to_le_bytes());
    out.extend_from_slice(payload);
}

fn serialize_g1_vec(points: &[G1Affine]) -> Vec<u8> {
    let mut out = Vec::with_capacity(points.len() * 64);
    for p in points {
        let (x, y) = if p.is_zero() {
            (Fq::from(0u64), Fq::from(0u64))
        } else {
            p.xy().expect("g1 not zero")
        };
        out.extend_from_slice(&fq_to_mont(x));
        out.extend_from_slice(&fq_to_mont(y));
    }
    out
}

fn serialize_g2_vec(points: &[G2Affine]) -> Vec<u8> {
    let mut out = Vec::with_capacity(points.len() * 128);
    for p in points {
        let (x, y) = if p.is_zero() {
            (ark_bn254::Fq2::ZERO, ark_bn254::Fq2::ZERO)
        } else {
            p.xy().expect("g2 not zero")
        };
        out.extend_from_slice(&fq_to_mont(x.c0));
        out.extend_from_slice(&fq_to_mont(x.c1));
        out.extend_from_slice(&fq_to_mont(y.c0));
        out.extend_from_slice(&fq_to_mont(y.c1));
    }
    out
}

// ----------------------------------------------------------------------------
// Fixtures, temp dirs, and the `xark` binary runner (shared by the CLI tests).
// ----------------------------------------------------------------------------

/// The committed fixtures directory: `crates/tests/fixtures/`.
pub fn fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures")
}

/// The Solana-export fixtures directory: `crates/tests/fixtures/groth16/`.
pub fn groth16_fixture_dir() -> PathBuf {
    fixture_dir().join("groth16")
}

/// The built `xark` CLI binary (built on demand by [`xark_tests::xark_bin`]).
pub fn xark_bin() -> PathBuf {
    xark_tests::xark_bin()
}

/// A purpose-built circuit crate under `crates/tests/examples/<name>`.
pub fn circuit_crate(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples").join(name)
}

/// `xark build <circuit-crate> --out <out>` with an isolated `CARGO_TARGET_DIR`
/// (so cargo can't replay a cached, non-extracting compile). Returns
/// `(success, stderr)`.
pub fn xark_build(name: &str, out: &Path, target: &Path) -> (bool, String) {
    let o = Command::new(xark_bin())
        .arg("build")
        .arg(circuit_crate(name))
        .arg("--out")
        .arg(out)
        .env("CARGO_TARGET_DIR", target)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .expect("spawn xark build");
    (o.status.success(), String::from_utf8_lossy(&o.stderr).into_owned())
}

/// `xark prove <out-dir> --input k=v ...` (solve witness + Groth16 prove/verify).
/// Returns `(success, stderr)`.
pub fn xark_prove(out: &Path, inputs: &[(&str, &str)]) -> (bool, String) {
    let mut c = Command::new(xark_bin());
    c.arg("prove").arg(out);
    for (k, v) in inputs {
        c.arg("--input").arg(format!("{k}={v}"));
    }
    let o = c
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .expect("spawn xark prove");
    (o.status.success(), String::from_utf8_lossy(&o.stderr).into_owned())
}

/// Run the `xark` binary with `args`, returning `(success, stdout, stderr)`.
pub fn run(args: &[&str]) -> (bool, String, String) {
    let output = Command::new(xark_bin())
        .args(args)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .expect("invoke xark");
    (
        output.status.success(),
        String::from_utf8_lossy(&output.stdout).into_owned(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

/// A throwaway directory, removed when this guard drops.
pub struct TempDir {
    path: PathBuf,
}

impl TempDir {
    pub fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.path);
    }
}

/// Create a unique temp directory (removed when the returned guard drops).
pub fn tempdir() -> TempDir {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static COUNTER: AtomicUsize = AtomicUsize::new(0);
    let n = COUNTER.fetch_add(1, Ordering::SeqCst);
    let pid = std::process::id();
    let path = std::env::temp_dir().join(format!("xark-test-{pid}-{n}"));
    std::fs::create_dir_all(&path).expect("mkdir tempdir");
    TempDir { path }
}
