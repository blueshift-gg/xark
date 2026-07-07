//! Primitive circuit IR ("xark-ir") — the artifact the lowering backend consumes.
//!
//! This is a gadget-free representation: every gadget (SHA-256, Keccak, ECDSA,
//! …) lowers entirely into these primitives, so the backend never needs a
//! per-gadget solver. It splits a circuit into a constraint program and a
//! witness-generation (hint) program, unified into one self-contained artifact:
//!
//! * [`Expression`] constraints are `expression == 0` (a degree-≤2 polynomial
//!   over variables). The backend lowers these to R1CS.
//! * [`WitnessGen`] ops are the **hint program**: an ordered list that computes
//!   every derived/hint variable from the inputs, using a small fixed set of
//!   primitives (products + modular inverse + bit-decomposition + div/rem).
//!   Running it top-to-bottom yields the full witness — no gadget-specific
//!   witness logic required.
//!
//! The constraints are the *check*; the witness-gen ops are the *hint*. Every
//! hint output must be pinned by constraints (the soundness invariant).

use serde::{Deserialize, Serialize};

use crate::field::FieldConst;
use crate::linear_combination::{LinearCombination, VarId};

/// The role of a circuit variable.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum VarRole {
    /// A public input, supplied by both prover and verifier.
    PublicInput,
    /// A private input, supplied by the prover.
    PrivateInput,
    /// Computed by the witness-generation program (multiplication outputs and
    /// hint outputs).
    Derived,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Var {
    pub id: VarId,
    pub name: String,
    pub role: VarRole,
}

/// A quadratic term `coeff * left * right` in an [`Expression`].
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MulTerm {
    pub coeff: FieldConst,
    pub left: VarId,
    pub right: VarId,
}

/// A linear term `coeff * var`.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LinearTerm {
    pub coeff: FieldConst,
    pub var: VarId,
}

/// An AssertZero-style constraint: `Σ mul_terms + Σ linear_terms + constant == 0`.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Expression {
    pub mul_terms: Vec<MulTerm>,
    pub linear_terms: Vec<LinearTerm>,
    pub constant: FieldConst,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub note: Option<String>,
}

/// A single witness-generation instruction. Evaluating it (against the
/// assignment built so far) fills in its output variable(s).
///
/// Linear combinations reference only already-computed variables.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "op", rename_all = "snake_case")]
pub enum WitnessGen {
    /// `out = eval(left) * eval(right)` — a multiplication-gate output.
    Product {
        out: VarId,
        left: LinearCombination,
        right: LinearCombination,
    },
    /// `out = eval(lc)` — names a linear combination as a fresh variable (used to
    /// bound the size of linear combinations in long bitwise chains).
    Linear { out: VarId, lc: LinearCombination },
    /// `out = eval(a) + eval(b) - 2·eval(a)·eval(b)` — boolean XOR, produced as a
    /// single variable via one fused constraint `(2a)·b = a + b - out`.
    Xor {
        out: VarId,
        a: LinearCombination,
        b: LinearCombination,
    },
    /// `out = eval(a) + eval(b) - eval(a)·eval(b)` — boolean OR, via the fused
    /// constraint `a·b = a + b - out`.
    Or {
        out: VarId,
        a: LinearCombination,
        b: LinearCombination,
    },
    /// `out = 1 / eval(input)` — modular inverse hint (`input` must be nonzero).
    Inverse { out: VarId, input: LinearCombination },
    /// `out = the `index`-th least-significant bit of eval(input)` — one bit of a
    /// bit-decomposition hint (gadgets emit one per bit).
    Bit {
        out: VarId,
        input: LinearCombination,
        index: u32,
    },
    /// `q = eval(num) / eval(den)`, `r = eval(num) % eval(den)` over the
    /// integers on the canonical representatives — quotient/remainder hint.
    DivRem {
        q: VarId,
        r: VarId,
        num: LinearCombination,
        den: LinearCombination,
    },
    /// Big-integer non-native multiply-reduce hint. Reconstructs `A`, `B`, `M`
    /// from their little-endian `limb_bits`-bit limbs, computes `P = A·B`, and
    /// outputs `q = P / M` and `r = P % M` split back into limbs. This is the
    /// primitive that makes foreign-field (e.g. secp256k1) multiplication
    /// solvable: `a·b` overflows a single field element, so it can't be done
    /// with the scalar `product`/`div_rem` hints.
    MulModDivMod {
        /// Quotient output limbs (little-endian).
        q: Vec<VarId>,
        /// Remainder output limbs (little-endian).
        r: Vec<VarId>,
        a: Vec<LinearCombination>,
        b: Vec<LinearCombination>,
        modulus: Vec<LinearCombination>,
        limb_bits: u32,
    },
    /// Big-integer modular inverse hint: reconstructs `A` and (prime) `M` from
    /// their little-endian limbs and outputs `A⁻¹ mod M` split into limbs. Pin
    /// the output `w` with a non-native `A·w == 1 (mod M)` check. Errors if
    /// `A ≡ 0`.
    ModInverse {
        out: Vec<VarId>,
        a: Vec<LinearCombination>,
        modulus: Vec<LinearCombination>,
        limb_bits: u32,
    },
    /// Linear multi-subtract hint for the fused subtract `(a - b - c) mod m`.
    /// Reconstructs `a`, `b`, `c`, `m` from little-endian limbs, computes the
    /// signed `val = a - b - c ∈ (-2m, m)`, and outputs the canonical remainder
    /// `r = val mod m ∈ [0,m)` (as limbs) plus `qabs = (r - val)/m ∈ {0,1,2}`.
    /// Pin with the linear identity `a + qabs·m == b + c + r`.
    Sub2 {
        qabs: VarId,
        r: Vec<VarId>,
        a: Vec<LinearCombination>,
        b: Vec<LinearCombination>,
        c: Vec<LinearCombination>,
        modulus: Vec<LinearCombination>,
        limb_bits: u32,
    },
}

/// The prime field the circuit is defined over.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FieldSpec {
    pub name: String,
    pub modulus_decimal: String,
}

impl FieldSpec {
    /// BN254 scalar field (`Fr`).
    pub fn bn254() -> Self {
        FieldSpec {
            name: "bn254".to_string(),
            modulus_decimal:
                "21888242871839275222246405745257275088548364400416034343698204186575808495617"
                    .to_string(),
        }
    }
}

/// The whole primitive circuit IR program.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PrimitiveProgram {
    pub field: FieldSpec,
    pub vars: Vec<Var>,
    /// AssertZero-style constraints (`expression == 0`).
    pub constraints: Vec<Expression>,
    /// Ordered witness-generation program (the hint program).
    pub witness_gen: Vec<WitnessGen>,
}

pub fn to_json_pretty(program: &PrimitiveProgram) -> String {
    serde_json::to_string_pretty(program).expect("PrimitiveProgram is always serializable")
}

/// Parse a primitive program from JSON (the inverse of [`to_json_pretty`]).
pub fn from_json(s: &str) -> Result<PrimitiveProgram, serde_json::Error> {
    serde_json::from_str(s)
}
