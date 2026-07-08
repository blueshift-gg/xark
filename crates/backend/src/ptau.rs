//! Parser for the snarkjs / Hermez Powers-of-Tau (`.ptau`) binary format.
//!
//! This module is **read-only**: it deserializes a `.ptau` transcript into an
//! in-memory [`PtauFile`] of arkworks BN254 points so that downstream code
//! (e.g. a phase-2 contribution) can consume the powers `[τ^i]G1`,
//! `[τ^i]G2`, `[α·τ^i]G1`, `[β·τ^i]G1`, and `[β]G2` produced by a public
//! phase-1 ceremony.
//!
//! # Binary layout
//!
//! The format is the one produced by snarkjs' `powersoftau new` /
//! `powersoftau contribute` commands. Multi-byte integers are little-endian.
//!
//! ```text
//! +---------+--------+---------+---------------------+
//! | "ptau" | u32 v | u32 #s | sections... |
//! +---------+--------+---------+---------------------+
//! ```
//!
//! Each section is `(u32 type, u64 size, [u8; size] payload)`. Known section
//! types:
//!
//! | type | name | payload |
//! |------|------------------|------------------------------------------------------|
//! | 1 | header | `u32 n8`, `n8 byte` prime modulus, `u32 power`,... |
//! | 2 | tau_g1 | `2 * 2^power - 1` G1 points |
//! | 3 | tau_g2 | `2^power` G2 points |
//! | 4 | alpha_tau_g1 | `2^power` G1 points |
//! | 5 | beta_tau_g1 | `2^power` G1 points |
//! | 6 | beta_g2 | 1 G2 point |
//! | 7 | contributions | opaque, skipped |
//!
//! # Field encoding
//!
//! snarkjs serializes Fq elements as `n8` little-endian bytes **in
//! Montgomery form** (i.e. `R · x mod p`, the same internal representation
//! arkworks stores). This is the relevant detail when converting raw bytes
//! into [`ark_bn254::Fq`]: we use [`Fp::new_unchecked`] on the parsed
//! `BigInt`, **not** `from_bigint` (the latter would Montgomery-reduce
//! a second time).
//!
//! For Fq2 (used on G2), the encoding is `(c0 || c1)` — both halves Mont LE,
//! same as arkworks' canonical layout.
//!
//! # Point validation
//!
//! Every parsed point is checked to lie on the curve. Subgroup membership is
//! implied for G1 (BN254 has cofactor 1 on G1) and is checked for G2.
//! The point at infinity is encoded as `(0, 0)` per the snarkjs convention.
//!
//! # Where this is consumed
//!
//! The phase-2 circuit-specific setup that turns a [`PtauFile`] into Groth16
//! keys lives in [`crate::setup_phase2::setup_from_ptau`] (re-exported here as
//! [`setup_from_ptau`]); `xark setup --ptau-file` and the `xark ceremony`
//! commands drive it. See `docs/trusted-setup.md`.

use std::convert::TryFrom;

use ark_bn254::{Bn254, Fq, Fq2, Fr, G1Affine, G1Projective, G2Affine, G2Projective};
use ark_ec::{pairing::Pairing, AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::{BigInt, BigInteger, Fp, One, PrimeField, Zero};
use num_bigint::BigUint;
use sha2::{Digest, Sha256};
use thiserror::Error;

/// The number of bytes used to encode a single Fq element in a BN254 ptau.
///
/// snarkjs writes `n8 = ceil(field_modulus_bits / 8) = 32` for BN254. We
/// reject anything else.
const BN254_FQ_BYTES: usize = 32;

/// Magic prefix for snarkjs ptau files: the ASCII bytes `"ptau"`.
const PTAU_MAGIC: [u8; 4] = *b"ptau";

/// Highest section type number we know how to interpret. Unknown types are
/// skipped (forward-compat with snarkjs adding new sections), but we always
/// require types 1..=6 to be present.
const SECTION_HEADER: u32 = 1;
const SECTION_TAU_G1: u32 = 2;
const SECTION_TAU_G2: u32 = 3;
const SECTION_ALPHA_TAU_G1: u32 = 4;
const SECTION_BETA_TAU_G1: u32 = 5;
const SECTION_BETA_G2: u32 = 6;
const SECTION_CONTRIBUTIONS: u32 = 7;

/// Result of running the phase-2 admissibility check
/// ([`check_ptau_covers_circuit`]).
#[derive(Debug, Clone, Copy)]
pub struct Phase2Coverage {
    /// `2^power` available constraint-domain size.
    pub max_domain_size: usize,
    /// The actual circuit's required domain size
    /// (`num_constraints + num_instance_variables`, next power of two).
    pub required_domain_size: usize,
}

/// Errors specific to the phase-2 deterministic setup path.
#[derive(Debug, Error)]
pub enum Phase2Error {
    /// The ptau transcript's power is too small for the circuit.
    #[error(
        "phase-2 setup: ptau covers domain size 2^{ptau_power} = {max_domain_size}, \
 but circuit requires {required_domain_size}. Use a larger.ptau file."
    )]
    PtauTooSmall {
        ptau_power: u32,
        max_domain_size: usize,
        required_domain_size: usize,
    },

    /// The circuit synthesizer returned an error during Setup-mode
    /// generation. This usually means the circuit's `generate_constraints`
    /// allocated a public/witness variable with a non-`None` value-closure
    /// in setup mode and the closure returned `AssignmentMissing`.
    #[error("phase-2 setup: circuit synthesizer failed during Setup-mode generation: {0}")]
    CircuitSynthesis(String),

    /// FFT domain construction failed because the required domain size
    /// has no appropriate radix-2 sub-group in BN254 Fr.
    #[error("phase-2 setup: FFT domain construction failed for requested size {0}")]
    DomainConstruction(usize),

    /// A ptau section holds fewer points than the QAP domain size `n` requires.
    /// A transcript from [`parse_ptau`](crate::parse_ptau) always has
    /// consistent section lengths; this fires only on a hand-built or otherwise
    /// malformed [`PtauFile`] whose vectors are too short — caught here so the
    /// per-variable QAP loop cannot index out of bounds and panic.
    #[error(
        "phase-2 setup: ptau section `{section}` holds {actual} points but the circuit's \
 QAP domain requires at least {needed}"
    )]
    PtauSectionTooShort {
        section: &'static str,
        needed: usize,
        actual: usize,
    },

    /// The powers-of-tau transcript is not internally consistent: the G1/G2
    /// powers do not form a single geometric τ-ladder, or the α/β powers are not
    /// consistent multiples of it. A transcript that fails this check would
    /// yield keys with a trapdoor the transcript's author knows.
    #[error(
        "phase-2 setup: powers-of-tau transcript failed the consistency check \
 (`{stage}`) — it is not a valid geometric ladder; do not use it"
    )]
    InconsistentPowers { stage: &'static str },
}

/// Verify that `ptau` covers a circuit with the given constraint count.
/// Returns the (max, required) domain sizes for diagnostic display.
///
/// `required_size = (num_constraints + num_instance_variables).next_power_of_two()`.
/// Per Groth16: the QAP polynomial domain must accommodate one row per
/// R1CS constraint plus one row per instance variable (Lagrange basis).
pub fn check_ptau_covers_circuit(
    ptau: &PtauFile,
    num_constraints: usize,
    num_instance_variables: usize,
) -> Result<Phase2Coverage, Phase2Error> {
    let required_unrounded = num_constraints + num_instance_variables;
    let required = required_unrounded.next_power_of_two().max(2);
    let max = 1usize << ptau.power;
    if required > max {
        return Err(Phase2Error::PtauTooSmall {
            ptau_power: ptau.power,
            max_domain_size: max,
            required_domain_size: required,
        });
    }
    Ok(Phase2Coverage {
        max_domain_size: max,
        required_domain_size: required,
    })
}

/// Re-export the implementation from [`crate::setup_phase2::setup_from_ptau`].
///
/// The function consumes the circuit synthesizer in Setup mode, evaluates
/// the QAP polynomials at τ using the ptau powers in the group (no scalar
/// τ is ever materialized), derives `γ, δ` deterministically from the
/// user-supplied `randomness_seed` via ChaCha20, and assembles a
/// `Groth16Keys` bundle ready for [`crate::prove::prove`] / [`crate::verify::verify`].
///
/// See `docs/security.md` for the production-readiness checklist and the
/// audit boundary around the phase-2 logic.
pub fn setup_from_ptau<C: ark_relations::gr1cs::ConstraintSynthesizer<ark_bn254::Fr>>(
    circuit: C,
    ptau: &PtauFile,
    randomness_seed: &[u8; 32],
) -> Result<crate::keys::Groth16Keys, Phase2Error> {
    crate::setup_phase2::setup_from_ptau(circuit, ptau, randomness_seed)
}

/// Verify the powers-of-tau transcript is internally consistent: the G1 and G2
/// powers form a single geometric τ-ladder, and the α/β powers are consistent
/// multiples of it (`beta_g2` sharing β with `beta_tau_g1`). `parse_ptau` only
/// checks each point is on-curve / in-subgroup, so without this a structurally
/// valid but *malicious* transcript (arbitrary or backdoored points) would be
/// turned into keys with a trapdoor its author knows.
///
/// This is the standard powers-of-tau verification (à la snarkjs
/// `powersOfTau verify`), batching each ladder with a Fiat-Shamir challenge
/// `ρ = H(all points)` and its powers, so the cost is a few MSMs + pairings
/// rather than `O(n)` pairings. It does **not** verify the contribution chain —
/// that is a separate concern handled by `xark ceremony`.
///
/// Called by the phase-2 setup, so every transcript actually used to derive
/// keys is verified. `parse_ptau` stays a pure structural parser.
pub(crate) fn verify_powers_consistency(ptau: &PtauFile) -> Result<(), Phase2Error> {
    let fail = |stage: &'static str| Phase2Error::InconsistentPowers { stage };

    let g1 = G1Affine::generator();
    let g2 = G2Affine::generator();

    // (1) Normalization: both ladders start at the generators.
    if ptau.tau_g1.len() < 2 || ptau.tau_g2.len() < 2 {
        return Err(fail("too-short"));
    }
    if ptau.tau_g1[0] != g1 || ptau.tau_g2[0] != g2 {
        return Err(fail("generators"));
    }

    // Reject a known-trapdoor transcript: τ ∈ {0,1}, α = 0, β = 0 all pass the
    // pairing ladders below (τ = 0 makes each 1 == 1) but are fully backdoored.
    if ptau.alpha_tau_g1.is_empty() || ptau.beta_tau_g1.is_empty() {
        return Err(fail("missing-alpha-beta"));
    }
    if ptau.tau_g1[1] == G1Affine::zero() || ptau.tau_g1[1] == g1 {
        return Err(fail("degenerate-tau")); // τ = 0 or τ = 1
    }
    if ptau.alpha_tau_g1[0] == G1Affine::zero() {
        return Err(fail("degenerate-alpha")); // α = 0
    }
    if ptau.beta_tau_g1[0] == G1Affine::zero() || ptau.beta_g2 == G2Affine::zero() {
        return Err(fail("degenerate-beta")); // β = 0
    }

    // (2) τ links G1 and G2: e(τ·g1, g2) == e(g1, τ·g2).
    if Bn254::pairing(ptau.tau_g1[1], g2) != Bn254::pairing(g1, ptau.tau_g2[1]) {
        return Err(fail("tau-link"));
    }

    // Fiat-Shamir challenge and its powers, used to batch each ladder.
    let rho = fiat_shamir_challenge(ptau);
    let tau_lo = ptau.tau_g2[0]; // g2
    let tau_hi = ptau.tau_g2[1]; // τ·g2

    // A G1 τ-ladder check: with A = Σρⁱ Pᵢ, B = Σρⁱ Pᵢ₊₁, verify
    // e(B, g2) == e(A, τ·g2)  ⇔  B = τ·A  ⇔  every step multiplies by τ.
    let g1_ladder_ok = |points: &[G1Affine]| -> bool {
        let m = points.len();
        if m < 2 {
            return true;
        }
        let scalars = powers_of(rho, m - 1);
        let a = match G1Projective::msm(&points[..m - 1], &scalars) {
            Ok(a) => a,
            Err(_) => return false,
        };
        let b = match G1Projective::msm(&points[1..], &scalars) {
            Ok(b) => b,
            Err(_) => return false,
        };
        Bn254::pairing(b.into_affine(), tau_lo) == Bn254::pairing(a.into_affine(), tau_hi)
    };

    // (3) G1 τ-ladder; (5) α and β ladders share the same τ.
    if !g1_ladder_ok(&ptau.tau_g1) {
        return Err(fail("tau-g1-ladder"));
    }
    if !g1_ladder_ok(&ptau.alpha_tau_g1) {
        return Err(fail("alpha-ladder"));
    }
    if !g1_ladder_ok(&ptau.beta_tau_g1) {
        return Err(fail("beta-ladder"));
    }

    // (4) G2 τ-ladder: with C = Σρⁱ Qᵢ, D = Σρⁱ Qᵢ₊₁, verify
    // e(g1, D) == e(τ·g1, C)  ⇔  D = τ·C.
    {
        let m = ptau.tau_g2.len();
        let scalars = powers_of(rho, m - 1);
        let c = G2Projective::msm(&ptau.tau_g2[..m - 1], &scalars).map_err(|_| fail("g2-msm"))?;
        let d = G2Projective::msm(&ptau.tau_g2[1..], &scalars).map_err(|_| fail("g2-msm"))?;
        if Bn254::pairing(ptau.tau_g1[0], d.into_affine())
            != Bn254::pairing(ptau.tau_g1[1], c.into_affine())
        {
            return Err(fail("tau-g2-ladder"));
        }
    }

    // (6) β links G1 and G2: e(β·g1, g2) == e(g1, β·g2).
    if Bn254::pairing(ptau.beta_tau_g1[0], g2) != Bn254::pairing(g1, ptau.beta_g2) {
        return Err(fail("beta-link"));
    }

    Ok(())
}

/// Derive the Fiat-Shamir batching challenge from every transcript point, so a
/// transcript cannot be crafted for a known challenge. Hashed incrementally
/// (bounded memory even for a `2^28` transcript).
fn fiat_shamir_challenge(ptau: &PtauFile) -> Fr {
    use ark_serialize::CanonicalSerialize;
    let mut h = Sha256::new();
    h.update(b"xark-ptau-consistency-v1");
    let mut buf = Vec::new();
    for p in &ptau.tau_g1 {
        buf.clear();
        p.serialize_compressed(&mut buf).expect("serialize g1");
        h.update(&buf);
    }
    for p in &ptau.alpha_tau_g1 {
        buf.clear();
        p.serialize_compressed(&mut buf).expect("serialize g1");
        h.update(&buf);
    }
    for p in &ptau.beta_tau_g1 {
        buf.clear();
        p.serialize_compressed(&mut buf).expect("serialize g1");
        h.update(&buf);
    }
    for p in &ptau.tau_g2 {
        buf.clear();
        p.serialize_compressed(&mut buf).expect("serialize g2");
        h.update(&buf);
    }
    buf.clear();
    ptau.beta_g2.serialize_compressed(&mut buf).expect("serialize g2");
    h.update(&buf);
    Fr::from_be_bytes_mod_order(&h.finalize())
}

/// `[ρ⁰, ρ¹, …, ρ^(n-1)]`.
fn powers_of(rho: Fr, n: usize) -> Vec<Fr> {
    let mut out = Vec::with_capacity(n);
    let mut cur = Fr::one();
    for _ in 0..n {
        out.push(cur);
        cur *= rho;
    }
    out
}

/// An in-memory representation of a parsed Powers-of-Tau transcript.
///
/// All vectors are stored in arkworks affine BN254 form and have lengths
/// determined by `power`. See module-level docs for the section layout.
#[derive(Debug, Clone)]
pub struct PtauFile {
    /// `2^power` is the maximum constraint-domain size this transcript
    /// supports.
    pub power: u32,
    /// `[τ^0]G1, [τ^1]G1,..., [τ^(2·2^power - 2)]G1` (length `2·2^p - 1`).
    pub tau_g1: Vec<G1Affine>,
    /// `[τ^0]G2,..., [τ^(2^power - 1)]G2` (length `2^p`).
    pub tau_g2: Vec<G2Affine>,
    /// `[α·τ^0]G1,..., [α·τ^(2^power - 1)]G1` (length `2^p`).
    pub alpha_tau_g1: Vec<G1Affine>,
    /// `[β·τ^0]G1,..., [β·τ^(2^power - 1)]G1` (length `2^p`).
    pub beta_tau_g1: Vec<G1Affine>,
    /// `[β]G2` — a single G2 point used in phase 2.
    pub beta_g2: G2Affine,
}

/// Errors produced by [`parse_ptau`].
#[derive(Debug, Error)]
pub enum PtauError {
    /// The file does not start with the ASCII bytes `"ptau"`.
    #[error("invalid ptau magic: expected b\"ptau\", got {0:?}")]
    BadMagic([u8; 4]),

    /// The version field is not one we know how to read. snarkjs currently
    /// writes version `1`.
    #[error("unsupported ptau version {0} (expected 1)")]
    UnsupportedVersion(u32),

    /// The file is shorter than the bytes its headers say it should contain.
    #[error("ptau truncated: needed {needed} bytes at offset {offset}, only {remaining} left")]
    Truncated {
        offset: usize,
        needed: usize,
        remaining: usize,
    },

    /// A required section (header / `tau_g1` / `tau_g2` /...) is missing
    /// from the file entirely.
    #[error("ptau missing required section {0} ({1})")]
    MissingSection(u32, &'static str),

    /// The header section declares a different field modulus than BN254's.
    #[error("ptau is not for BN254 (modulus mismatch)")]
    WrongCurve,

    /// The header section declares `n8 != 32`.
    #[error("ptau field byte length {0} is not 32 (BN254 expects 32-byte Fq elements)")]
    WrongFieldByteLength(u32),

    /// A section's payload is not the size we computed from `power` and the
    /// section's point-count contract.
    #[error("section {ty} ({name}) has size {actual} bytes, expected {expected}")]
    BadSectionSize {
        ty: u32,
        name: &'static str,
        expected: usize,
        actual: usize,
    },

    /// A parsed point does not lie on the BN254 curve, or (for G2) is not in
    /// the correct prime-order subgroup.
    #[error("invalid point in section {section} at index {index}: {detail}")]
    InvalidPoint {
        section: &'static str,
        index: usize,
        detail: &'static str,
    },

    /// `power` is absurd (e.g. >= 32, which would mean a `2^32`-sized
    /// domain — pointless and very memory-hungry).
    #[error("ptau power {0} is out of range (must be in 1..=28)")]
    PowerOutOfRange(u32),
}

/// Parse a `.ptau` byte buffer into a [`PtauFile`].
///
/// See the module-level docs for the binary layout. Sections 1..=6 are
/// required; section 7 (contributions) is recognized but skipped; any other
/// section type is also skipped for forward-compatibility with future
/// snarkjs versions.
pub fn parse_ptau(bytes: &[u8]) -> Result<PtauFile, PtauError> {
    let mut cursor = Cursor::new(bytes);

    let magic = cursor.read_array::<4>()?;
    if magic != PTAU_MAGIC {
        return Err(PtauError::BadMagic(magic));
    }
    let version = cursor.read_u32()?;
    if version != 1 {
        return Err(PtauError::UnsupportedVersion(version));
    }
    let num_sections = cursor.read_u32()?;

    // Index sections by type (snarkjs writes them in order; we don't rely on
    // that). Not `with_capacity(num_sections)` — that u32 is attacker-controlled
    // (a 12-byte file could request ~100 GB); the loop is bounded by real content.
    let mut sections: Vec<(u32, &[u8])> = Vec::new();
    for _ in 0..num_sections {
        let ty = cursor.read_u32()?;
        let size = cursor.read_u64()? as usize;
        let payload = cursor.read_slice(size)?;
        sections.push((ty, payload));
    }

    let find = |ty: u32, name: &'static str| -> Result<&[u8], PtauError> {
        sections
            .iter()
            .find(|(t, _)| *t == ty)
            .map(|(_, p)| *p)
            .ok_or(PtauError::MissingSection(ty, name))
    };

    // Header.
    let header_bytes = find(SECTION_HEADER, "header")?;
    let mut hc = Cursor::new(header_bytes);
    let n8 = hc.read_u32()?;
    if n8 as usize != BN254_FQ_BYTES {
        return Err(PtauError::WrongFieldByteLength(n8));
    }
    let modulus_bytes = hc.read_slice(n8 as usize)?;
    if !modulus_matches_bn254(modulus_bytes) {
        return Err(PtauError::WrongCurve);
    }
    let power = hc.read_u32()?;
    // snarkjs writes a `ceremony_power` after `power`. We tolerate it being
    // absent for non-snarkjs producers, and ignore it when present.
    let _ceremony_power = hc.read_u32().ok();

    // Sanity-check the power. 2^28 would be a ~16 GiB tau_g1 section, which
    // is the largest snarkjs ever produced (Hermez 28). Bigger than that is
    // certainly a bug.
    if power == 0 || power > 28 {
        return Err(PtauError::PowerOutOfRange(power));
    }

    let two_to_p = 1usize << power;

    // tau_g1: 2*2^p - 1 G1 points.
    let tau_g1 = read_g1_section(
        find(SECTION_TAU_G1, "tau_g1")?,
        2 * two_to_p - 1,
        "tau_g1",
        SECTION_TAU_G1,
    )?;

    // tau_g2: 2^p G2 points.
    let tau_g2 = read_g2_section(
        find(SECTION_TAU_G2, "tau_g2")?,
        two_to_p,
        "tau_g2",
        SECTION_TAU_G2,
    )?;

    // alpha_tau_g1: 2^p G1.
    let alpha_tau_g1 = read_g1_section(
        find(SECTION_ALPHA_TAU_G1, "alpha_tau_g1")?,
        two_to_p,
        "alpha_tau_g1",
        SECTION_ALPHA_TAU_G1,
    )?;

    // beta_tau_g1: 2^p G1.
    let beta_tau_g1 = read_g1_section(
        find(SECTION_BETA_TAU_G1, "beta_tau_g1")?,
        two_to_p,
        "beta_tau_g1",
        SECTION_BETA_TAU_G1,
    )?;

    // beta_g2: 1 G2.
    let beta_g2_vec = read_g2_section(
        find(SECTION_BETA_G2, "beta_g2")?,
        1,
        "beta_g2",
        SECTION_BETA_G2,
    )?;
    let beta_g2 = beta_g2_vec[0];

    // Sanity-check that contributions, if present, is at least non-empty
    // semantics-wise. We don't actually verify the transcript — that's a
    // separate (and significantly harder) job that belongs in `xark
    // ceremony verify`. We just look at the section to know it's there.
    let _ = find(SECTION_CONTRIBUTIONS, "contributions"); // ignore error

    Ok(PtauFile {
        power,
        tau_g1,
        tau_g2,
        alpha_tau_g1,
        beta_tau_g1,
        beta_g2,
    })
}

// ---- internal helpers -------------------------------------------------------

/// Minimal cursor that yields slice-of-bytes reads and returns
/// [`PtauError::Truncated`] on EOF — no `std::io` involved, since we operate
/// on an in-memory byte slice.
struct Cursor<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> Cursor<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, pos: 0 }
    }

    fn read_slice(&mut self, n: usize) -> Result<&'a [u8], PtauError> {
        let end = self.pos.checked_add(n).ok_or(PtauError::Truncated {
            offset: self.pos,
            needed: n,
            remaining: self.bytes.len().saturating_sub(self.pos),
        })?;
        if end > self.bytes.len() {
            return Err(PtauError::Truncated {
                offset: self.pos,
                needed: n,
                remaining: self.bytes.len().saturating_sub(self.pos),
            });
        }
        let out = &self.bytes[self.pos..end];
        self.pos = end;
        Ok(out)
    }

    fn read_array<const N: usize>(&mut self) -> Result<[u8; N], PtauError> {
        let s = self.read_slice(N)?;
        let mut out = [0u8; N];
        out.copy_from_slice(s);
        Ok(out)
    }

    fn read_u32(&mut self) -> Result<u32, PtauError> {
        Ok(u32::from_le_bytes(self.read_array::<4>()?))
    }

    fn read_u64(&mut self) -> Result<u64, PtauError> {
        Ok(u64::from_le_bytes(self.read_array::<8>()?))
    }
}

/// Compare the `n8` bytes the header advertises against BN254's known Fq
/// modulus.
fn modulus_matches_bn254(modulus_le: &[u8]) -> bool {
    let parsed = BigUint::from_bytes_le(modulus_le);
    let expected: BigUint = Fq::MODULUS.into();
    parsed == expected
}

/// Decode one Fq element from `BN254_FQ_BYTES` LE-Montgomery bytes.
///
/// The snarkjs encoding is **Montgomery form** — the same internal layout
/// arkworks uses for [`Fq`]. We construct the field element via
/// [`Fp::new_unchecked`] which trusts the input is already in Montgomery
/// form; calling [`PrimeField::from_bigint`] here would apply a *second*
/// Montgomery reduction and silently scale every coordinate by `R⁻¹`.
fn fq_from_le_mont(bytes: &[u8]) -> Option<Fq> {
    debug_assert_eq!(bytes.len(), BN254_FQ_BYTES);
    let n = BigUint::from_bytes_le(bytes);
    // Reject a non-canonical encoding (Montgomery rep `>= p`): `new_unchecked`
    // would trust it, and it can otherwise slip past the representation-comparing
    // degeneracy checks.
    let modulus: BigUint = Fq::MODULUS.into();
    if n >= modulus {
        return None;
    }
    let bigint: BigInt<4> = BigInt::try_from(n).ok()?;
    Some(Fp::new_unchecked(bigint))
}

fn read_g1_section(
    payload: &[u8],
    count: usize,
    name: &'static str,
    ty: u32,
) -> Result<Vec<G1Affine>, PtauError> {
    let point_size = 2 * BN254_FQ_BYTES;
    let expected = count * point_size;
    if payload.len() != expected {
        return Err(PtauError::BadSectionSize {
            ty,
            name,
            expected,
            actual: payload.len(),
        });
    }
    let mut out = Vec::with_capacity(count);
    for i in 0..count {
        let off = i * point_size;
        let nc = || PtauError::InvalidPoint { section: name, index: i, detail: "non-canonical coordinate" };
        let x = fq_from_le_mont(&payload[off..off + BN254_FQ_BYTES]).ok_or_else(nc)?;
        let y = fq_from_le_mont(&payload[off + BN254_FQ_BYTES..off + point_size]).ok_or_else(nc)?;
        let p = if x.is_zero() && y.is_zero() {
            G1Affine::zero()
        } else {
            let candidate = G1Affine::new_unchecked(x, y);
            if !candidate.is_on_curve() {
                return Err(PtauError::InvalidPoint {
                    section: name,
                    index: i,
                    detail: "not on curve",
                });
            }
            // BN254 G1 has cofactor 1, so on-curve implies in-subgroup.
            candidate
        };
        out.push(p);
    }
    Ok(out)
}

fn read_g2_section(
    payload: &[u8],
    count: usize,
    name: &'static str,
    ty: u32,
) -> Result<Vec<G2Affine>, PtauError> {
    let point_size = 4 * BN254_FQ_BYTES;
    let expected = count * point_size;
    if payload.len() != expected {
        return Err(PtauError::BadSectionSize {
            ty,
            name,
            expected,
            actual: payload.len(),
        });
    }
    let mut out = Vec::with_capacity(count);
    for i in 0..count {
        let off = i * point_size;
        let nc = || PtauError::InvalidPoint { section: name, index: i, detail: "non-canonical coordinate" };
        let x_c0 = fq_from_le_mont(&payload[off..off + BN254_FQ_BYTES]).ok_or_else(nc)?;
        let x_c1 = fq_from_le_mont(&payload[off + BN254_FQ_BYTES..off + 2 * BN254_FQ_BYTES]).ok_or_else(nc)?;
        let y_c0 = fq_from_le_mont(&payload[off + 2 * BN254_FQ_BYTES..off + 3 * BN254_FQ_BYTES]).ok_or_else(nc)?;
        let y_c1 = fq_from_le_mont(&payload[off + 3 * BN254_FQ_BYTES..off + point_size]).ok_or_else(nc)?;
        let x = Fq2::new(x_c0, x_c1);
        let y = Fq2::new(y_c0, y_c1);
        let p = if x.is_zero() && y.is_zero() {
            G2Affine::zero()
        } else {
            let candidate = G2Affine::new_unchecked(x, y);
            if !candidate.is_on_curve() {
                return Err(PtauError::InvalidPoint {
                    section: name,
                    index: i,
                    detail: "not on curve",
                });
            }
            if !candidate.is_in_correct_subgroup_assuming_on_curve() {
                return Err(PtauError::InvalidPoint {
                    section: name,
                    index: i,
                    detail: "G2 point not in prime-order subgroup",
                });
            }
            candidate
        };
        out.push(p);
    }
    Ok(out)
}

/// Re-encode an [`Fq`] element back into the snarkjs ptau
/// little-endian-Montgomery byte layout. This is the exact inverse of
/// [`fq_from_le_mont`] and is the helper [`tests/ptau.rs`] uses to build
/// fixture bytes; it lives here so that the fixture-generator and the
/// parser cannot drift apart silently.
///
/// Visible at `pub(crate)` because there's no production use for it (real
/// `.ptau` files come from snarkjs, not from us) — but the integration
/// test in `tests/ptau.rs` needs it, so we re-export it from `lib.rs`
/// behind `#[doc(hidden)]`.
#[doc(hidden)]
pub fn __fq_to_le_mont_bytes_for_tests(f: Fq) -> [u8; BN254_FQ_BYTES] {
    // arkworks stores `Fq` internally in Montgomery form, and the field is
    // `pub`. `to_bytes_le` on the inner BigInt yields exactly those Mont
    // limbs as little-endian bytes — which is what ptau stores on disk.
    let mont_bigint = f.0;
    let v = mont_bigint.to_bytes_le();
    let mut out = [0u8; BN254_FQ_BYTES];
    out[..v.len()].copy_from_slice(&v);
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::UniformRand;

    #[test]
    fn modulus_matches_self() {
        let m_bytes = Fq::MODULUS.to_bytes_le();
        assert!(modulus_matches_bn254(&m_bytes));
    }

    #[test]
    fn cursor_truncation_is_caught() {
        let mut c = Cursor::new(b"abc");
        assert!(c.read_u32().is_err());
    }

    #[test]
    fn fq_mont_roundtrip_zero_one() {
        let zero_bytes = [0u8; BN254_FQ_BYTES];
        assert_eq!(fq_from_le_mont(&zero_bytes), Some(Fq::from(0u64)));

        let one = Fq::from(1u64);
        let one_bytes = __fq_to_le_mont_bytes_for_tests(one);
        assert_eq!(fq_from_le_mont(&one_bytes), Some(one));
    }

    #[test]
    fn fq_mont_roundtrip_random() {
        let mut rng = ark_std::test_rng();
        for _ in 0..16 {
            let f = Fq::rand(&mut rng);
            let bytes = __fq_to_le_mont_bytes_for_tests(f);
            assert_eq!(fq_from_le_mont(&bytes), Some(f));
        }
    }

    #[test]
    fn fq_mont_rejects_non_canonical() {
        // The all-ones 32-byte encoding is `2^256 − 1 ≥ p`: a non-canonical
        // Montgomery representation, which must be rejected rather than trusted.
        let all_ones = [0xFFu8; BN254_FQ_BYTES];
        assert_eq!(fq_from_le_mont(&all_ones), None);
    }
}
