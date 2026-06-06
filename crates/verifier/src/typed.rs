//! Typed, const-generic Groth16 verifier and proof.
//!
//! Most programs know their circuit — and therefore their verifying key —
//! at compile time. [`Verifier<N>`] captures that: `N` is the number of
//! public inputs, fixed in the type, so the IC vector is exactly `N + 1`
//! points and there is no runtime length to validate or `ic_count` to carry
//! on the wire. The whole key is fixed-size arrays, so it lives in a `const`
//! built straight from an embedded file:
//!
//! ```ignore
//! use xark_verifier::{Verifier, Proof, parse_public_inputs};
//!
//! const VERIFIER: Verifier<1> =
//! Verifier::from_le_bytes(include_bytes!("verifying_key.solana.bin"));
//! const PROOF: Proof = Proof::from_le_bytes(include_bytes!("proof.solana.bin"));
//! const INPUTS: [[u8; 32]; 1] = parse_public_inputs(include_bytes!("public_inputs.solana.bin"));
//!
//! assert!(VERIFIER.verify(&PROOF, &INPUTS));
//! ```
//!
//! The byte length is checked at compile time inside the `const fn`
//! constructors, so a fixture whose size doesn't match `N` is a build error,
//! not a runtime one. For the dynamic case (one program, many circuits, VK
//! loaded from an account) use [`verify_groth16`](crate::verify_groth16)
//! over `&[u8]` instead.

use solana_nostd_alt_bn128::{G1Point, G2Point};

use crate::verifier::{
    FR_BYTES, G1_BYTES, G2_BYTES, PROOF_BYTES, VK_FIXED_PREFIX_BYTES, VerifierError,
    coords_canonical, groth16_pairing_check,
};

// `const fn` slice→array readers (no `copy_from_slice` in const context).

const fn read_g1(bytes: &[u8], off: usize) -> [u8; G1_BYTES] {
    let mut out = [0u8; G1_BYTES];
    let mut i = 0;
    while i < G1_BYTES {
        out[i] = bytes[off + i];
        i += 1;
    }
    out
}

const fn read_g2(bytes: &[u8], off: usize) -> [u8; G2_BYTES] {
    let mut out = [0u8; G2_BYTES];
    let mut i = 0;
    while i < G2_BYTES {
        out[i] = bytes[off + i];
        i += 1;
    }
    out
}

const fn read_fr(bytes: &[u8], off: usize) -> [u8; FR_BYTES] {
    let mut out = [0u8; FR_BYTES];
    let mut i = 0;
    while i < FR_BYTES {
        out[i] = bytes[off + i];
        i += 1;
    }
    out
}

/// A Groth16 proof in the LE wire format: `A (G1) || B (G2) || C (G1)`,
/// 256 bytes. `A` is stored already-negated (the exporter pre-negates it),
/// matching what [`Verifier::verify`] feeds into the pairing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Proof {
    /// Proof element `A` (G1), already negated.
    pub a: [u8; G1_BYTES],
    /// Proof element `B` (G2).
    pub b: [u8; G2_BYTES],
    /// Proof element `C` (G1).
    pub c: [u8; G1_BYTES],
}

impl Proof {
    /// Parse the 256-byte LE proof blob (`A || B || C`). The fixed-size array
    /// argument makes a wrong-size file a compile-time *type* error — e.g.
    /// `expected &[u8; 256], found &[u8; 257]` — when fed an `include_bytes!`.
    pub const fn from_le_bytes(bytes: &[u8; PROOF_BYTES]) -> Self {
        Proof {
            a: read_g1(bytes, 0),
            b: read_g2(bytes, G1_BYTES),
            c: read_g1(bytes, G1_BYTES + G2_BYTES),
        }
    }
}

/// A Groth16 verifying key for a circuit with `N` public inputs, stored as
/// fixed-size LE arrays so it can be a compile-time `const`. The IC vector is
/// `ic0` (the constant term) plus one point per public input — `N + 1` total
/// — so no count is stored.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Verifier<const N: usize> {
    /// `α` (G1).
    pub alpha: [u8; G1_BYTES],
    /// `β` (G2).
    pub beta: [u8; G2_BYTES],
    /// `γ` (G2).
    pub gamma: [u8; G2_BYTES],
    /// `δ` (G2).
    pub delta: [u8; G2_BYTES],
    /// `ic[0]` — the constant term of the public-input linear combination.
    pub ic0: [u8; G1_BYTES],
    /// `ic[1..=N]` — one G1 point per public input.
    pub ic: [[u8; G1_BYTES]; N],
}

impl<const N: usize> Verifier<N> {
    /// Expected byte length of an `N`-input VK: fixed prefix + `(N + 1)` G1.
    pub const BYTES: usize = VK_FIXED_PREFIX_BYTES + (N + 1) * G1_BYTES;

    /// Parse the LE VK wire blob (`α || β || γ || δ || (N+1) × G1`) from an
    /// `include_bytes!`. The byte length `L` is taken from the file; if it
    /// doesn't match what a `Verifier<N>` needs (`448 + (N+1)·64` bytes), the
    /// `const` assertion fails at *compile time* — for any monomorphization,
    /// so even a runtime call is rejected. The failing instantiation names the
    /// actual length, e.g. `…from_le_bytes::<580>`.
    pub const fn from_le_bytes<const L: usize>(bytes: &[u8; L]) -> Self {
        const {
            assert!(
                L == VK_FIXED_PREFIX_BYTES + (N + 1) * G1_BYTES,
                "verifying-key file size does not match Verifier<N>: a Verifier<N> \
 needs exactly 448 + (N + 1) * 64 bytes — check that N equals the \
 circuit's public-input count and the file came from `xark export`"
            );
        }
        let mut ic = [[0u8; G1_BYTES]; N];
        let mut i = 0;
        while i < N {
            ic[i] = read_g1(bytes, VK_FIXED_PREFIX_BYTES + G1_BYTES + i * G1_BYTES);
            i += 1;
        }
        Verifier {
            alpha: read_g1(bytes, 0),
            beta: read_g2(bytes, G1_BYTES),
            gamma: read_g2(bytes, G1_BYTES + G2_BYTES),
            delta: read_g2(bytes, G1_BYTES + 2 * G2_BYTES),
            ic0: read_g1(bytes, VK_FIXED_PREFIX_BYTES),
            ic,
        }
    }

    /// Verify `proof` against `public_inputs`. Returns `false` on any
    /// failure — a non-holding pairing or a malformed point the syscall
    /// rejects. Use [`try_verify`](Self::try_verify) to distinguish them.
    pub fn verify(&self, proof: &Proof, public_inputs: &[[u8; FR_BYTES]; N]) -> bool {
        self.try_verify(proof, public_inputs).unwrap_or(false)
    }

    /// Like [`verify`](Self::verify) but surfaces the [`VerifierError`] from a
    /// rejected operand instead of collapsing it to `false`.
    pub fn try_verify(
        &self,
        proof: &Proof,
        public_inputs: &[[u8; FR_BYTES]; N],
    ) -> Result<bool, VerifierError> {
        // vk_x = ic[0] + Σ inputs[i] · ic[i+1]
        let mut acc = G1Point::from_le_bytes(self.ic0);
        let mut i = 0;
        while i < N {
            // Reject non-canonical (>= r) public inputs to prevent encoding
            // malleability — see `scalar_is_canonical`.
            if !crate::verifier::scalar_is_canonical(&public_inputs[i]) {
                return Err(VerifierError::NonCanonicalPublicInput { index: i as u32 });
            }
            let term = (G1Point::from_le_bytes(self.ic[i]) * public_inputs[i])?;
            acc = (acc + term)?;
            i += 1;
        }
        groth16_pairing_check(
            G1Point::from_le_bytes(proof.a),
            G2Point::from_le_bytes(proof.b),
            G1Point::from_le_bytes(self.alpha),
            G2Point::from_le_bytes(self.beta),
            acc,
            G2Point::from_le_bytes(self.gamma),
            G1Point::from_le_bytes(proof.c),
            G2Point::from_le_bytes(self.delta),
        )
    }

    /// Strict variant of [`verify`](Self::verify): additionally rejects any VK
    /// or proof coordinate whose 32-byte LE encoding is non-canonical (`>= q`).
    /// The syscall masks the unused top bits, so plain [`verify`](Self::verify)
    /// accepts byte-distinct encodings of the same point; use this when the
    /// proof's exact bytes matter (hashed, signed, or used as a replay key).
    /// See [`verify_groth16_strict`](crate::verify_groth16_strict).
    pub fn verify_strict(&self, proof: &Proof, public_inputs: &[[u8; FR_BYTES]; N]) -> bool {
        self.try_verify_strict(proof, public_inputs)
            .unwrap_or(false)
    }

    /// Like [`verify_strict`](Self::verify_strict) but surfaces the
    /// [`VerifierError`] instead of collapsing it to `false`.
    pub fn try_verify_strict(
        &self,
        proof: &Proof,
        public_inputs: &[[u8; FR_BYTES]; N],
    ) -> Result<bool, VerifierError> {
        // Every coordinate of the proof and the VK must be a canonical Fq
        // encoding. (Public inputs are Fr and checked inside `try_verify`.)
        let canonical = coords_canonical(&proof.a)
            && coords_canonical(&proof.b)
            && coords_canonical(&proof.c)
            && coords_canonical(&self.alpha)
            && coords_canonical(&self.beta)
            && coords_canonical(&self.gamma)
            && coords_canonical(&self.delta)
            && coords_canonical(&self.ic0)
            && self.ic.iter().all(|ic| coords_canonical(ic));
        if !canonical {
            return Err(VerifierError::NonCanonicalCoordinate);
        }
        self.try_verify(proof, public_inputs)
    }
}

/// Parse a concatenated LE public-inputs blob (`N × 32 B`) into a fixed array.
/// The byte length `L` is taken from the `include_bytes!`; if it doesn't equal
/// `N * 32` the `const` assertion fails at *compile time* (for any
/// monomorphization). `N` is inferred from the binding's array type.
pub const fn parse_public_inputs<const N: usize, const L: usize>(
    bytes: &[u8; L],
) -> [[u8; FR_BYTES]; N] {
    const {
        assert!(
            L == N * FR_BYTES,
            "public-inputs file size does not match the output array length \
 (a `[[u8; 32]; N]` needs exactly N * 32 bytes)"
        );
    }
    let mut out = [[0u8; FR_BYTES]; N];
    let mut i = 0;
    while i < N {
        out[i] = read_fr(bytes, i * FR_BYTES);
        i += 1;
    }
    out
}
