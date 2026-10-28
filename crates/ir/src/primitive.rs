//! Primitive circuit IR ("xark-ir") — the artifact the lowering backend consumes.
//!
//! This is a function-free representation: every function (SHA-256, Keccak, ECDSA,
//! …) lowers entirely into these primitives, so the backend never needs a
//! per-function solver. It splits a circuit into a constraint program and a
//! witness-generation (hint) program, unified into one self-contained artifact:
//!
//! * [`Expression`] constraints are `expression == 0` (a degree-≤2 polynomial
//!   over variables). The backend lowers these to R1CS.
//! * [`WitnessGen`] ops are the **hint program**: an ordered list that computes
//!   every derived/hint variable from the inputs, using a small fixed set of
//!   primitives (products + modular inverse + bit-decomposition + div/rem).
//!   Running it top-to-bottom yields the full witness — no function-specific
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

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Var {
    pub id: VarId,
    pub name: String,
    pub role: VarRole,
}

/// A quadratic term `coeff * left * right` in an [`Expression`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MulTerm {
    pub coeff: FieldConst,
    pub left: VarId,
    pub right: VarId,
}

/// A linear term `coeff * var`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LinearTerm {
    pub coeff: FieldConst,
    pub var: VarId,
}

/// An AssertZero-style constraint: `Σ mul_terms + Σ linear_terms + constant == 0`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Expression {
    pub mul_terms: Vec<MulTerm>,
    pub linear_terms: Vec<LinearTerm>,
    pub constant: FieldConst,
    /// Human-readable debug annotation (e.g. `secret * secret = t0`). Not part
    /// of the persisted circuit — `#[serde(skip)]` keeps it out of `circuit.json`
    /// (it's set during lowering for in-process diagnostics only).
    #[serde(skip)]
    pub note: Option<String>,
}

/// A single witness-generation instruction. Evaluating it (against the
/// assignment built so far) fills in its output variable(s).
///
/// Linear combinations reference only already-computed variables. `L` and `V`
/// are the LC and output-variable types: the IR's own, or the solver's compiled
/// template-local forms.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "op", rename_all = "snake_case")]
pub enum WitnessGen<L = LinearCombination, V = VarId> {
    /// `out = eval(left) * eval(right)` — a multiplication-gate output.
    Product { out: V, left: L, right: L },
    /// `out = eval(lc)` — names a linear combination as a fresh variable (used to
    /// bound the size of linear combinations in long bitwise chains).
    Linear { out: V, lc: L },
    /// `out = eval(a) + eval(b) - 2·eval(a)·eval(b)` — boolean XOR, produced as a
    /// single variable via one fused constraint `(2a)·b = a + b - out`.
    Xor { out: V, a: L, b: L },
    /// `out = eval(a) + eval(b) - eval(a)·eval(b)` — boolean OR, via the fused
    /// constraint `a·b = a + b - out`.
    Or { out: V, a: L, b: L },
    /// `out = 1 / eval(input)` — modular inverse hint (`input` must be nonzero).
    Inverse { out: V, input: L },
    /// `out = 1 / eval(input)` if `input ≠ 0`, else `0` — backs the `is_zero` function.
    InverseOrZero { out: V, input: L },
    /// `out = the `index`-th least-significant bit of eval(input)` — one bit of a
    /// bit-decomposition hint (functions emit one per bit).
    Bit { out: V, input: L, index: u32 },
    /// Batched bit-decomposition: `outs[i] = i-th least-significant bit of
    /// eval(input)`. Like emitting one `Bit` per `i`, but serializes the shared
    /// `input` once (major size win for bit-heavy circuits).
    Bits { outs: Vec<V>, input: L },
    /// `q = eval(num) / eval(den)`, `r = eval(num) % eval(den)` over the
    /// integers on the canonical representatives — quotient/remainder hint.
    DivRem { q: V, r: V, num: L, den: L },
    /// Big-integer non-native multiply-reduce hint. Reconstructs `A`, `B`, `M`
    /// from their little-endian `limb_bits`-bit limbs, computes `P = A·B`, and
    /// outputs `q = P / M`, `r = P % M` split back into limbs. Makes foreign-field
    /// (e.g. secp256k1) multiplication solvable, where `a·b` overflows one field
    /// element and the scalar `product`/`div_rem` hints don't suffice.
    MulModDivMod {
        /// Quotient output limbs (little-endian).
        q: Vec<V>,
        /// Remainder output limbs (little-endian).
        r: Vec<V>,
        a: Vec<L>,
        b: Vec<L>,
        modulus: Vec<L>,
        limb_bits: u32,
    },
    /// Big-integer modular inverse hint: reconstructs `A` and (prime) `M` from
    /// their little-endian limbs and outputs `A⁻¹ mod M` split into limbs. Pin
    /// the output `w` with a non-native `A·w == 1 (mod M)` check. Errors if
    /// `A ≡ 0`.
    ModInverse {
        out: Vec<V>,
        a: Vec<L>,
        modulus: Vec<L>,
        limb_bits: u32,
    },
    /// Linear multi-subtract hint for the fused subtract `(a - b - c) mod m`.
    /// Reconstructs `a`, `b`, `c`, `m` from little-endian limbs, computes the
    /// signed `val = a - b - c ∈ (-2m, m)`, and outputs the canonical remainder
    /// `r = val mod m ∈ [0,m)` (as limbs) plus `qabs = (r - val)/m ∈ {0,1,2}`.
    /// Pin with the linear identity `a + qabs·m == b + c + r`.
    Sub2 {
        qabs: V,
        r: Vec<V>,
        a: Vec<L>,
        b: Vec<L>,
        c: Vec<L>,
        modulus: Vec<L>,
        limb_bits: u32,
    },
}

impl<L, V> WitnessGen<L, V> {
    /// The same op with every input LC mapped by `lc` and every output var by `var`.
    pub(crate) fn map<L2, V2>(
        &self,
        mut lc: impl FnMut(&L) -> L2,
        mut var: impl FnMut(&V) -> V2,
    ) -> WitnessGen<L2, V2> {
        let mut lcs = |v: &[L]| v.iter().map(&mut lc).collect();
        match self {
            WitnessGen::Product { out, left, right } => WitnessGen::Product {
                out: var(out),
                left: lc(left),
                right: lc(right),
            },
            WitnessGen::Linear { out, lc: l } => WitnessGen::Linear {
                out: var(out),
                lc: lc(l),
            },
            WitnessGen::Xor { out, a, b } => WitnessGen::Xor {
                out: var(out),
                a: lc(a),
                b: lc(b),
            },
            WitnessGen::Or { out, a, b } => WitnessGen::Or {
                out: var(out),
                a: lc(a),
                b: lc(b),
            },
            WitnessGen::Inverse { out, input } => WitnessGen::Inverse {
                out: var(out),
                input: lc(input),
            },
            WitnessGen::InverseOrZero { out, input } => WitnessGen::InverseOrZero {
                out: var(out),
                input: lc(input),
            },
            WitnessGen::Bit { out, input, index } => WitnessGen::Bit {
                out: var(out),
                input: lc(input),
                index: *index,
            },
            WitnessGen::Bits { outs, input } => WitnessGen::Bits {
                outs: outs.iter().map(&mut var).collect(),
                input: lc(input),
            },
            WitnessGen::DivRem { q, r, num, den } => WitnessGen::DivRem {
                q: var(q),
                r: var(r),
                num: lc(num),
                den: lc(den),
            },
            WitnessGen::MulModDivMod {
                q,
                r,
                a,
                b,
                modulus,
                limb_bits,
            } => WitnessGen::MulModDivMod {
                q: q.iter().map(&mut var).collect(),
                r: r.iter().map(&mut var).collect(),
                a: lcs(a),
                b: lcs(b),
                modulus: lcs(modulus),
                limb_bits: *limb_bits,
            },
            WitnessGen::ModInverse {
                out,
                a,
                modulus,
                limb_bits,
            } => WitnessGen::ModInverse {
                out: out.iter().map(&mut var).collect(),
                a: lcs(a),
                modulus: lcs(modulus),
                limb_bits: *limb_bits,
            },
            WitnessGen::Sub2 {
                qabs,
                r,
                a,
                b,
                c,
                modulus,
                limb_bits,
            } => WitnessGen::Sub2 {
                qabs: var(qabs),
                r: r.iter().map(&mut var).collect(),
                a: lcs(a),
                b: lcs(b),
                c: lcs(c),
                modulus: lcs(modulus),
                limb_bits: *limb_bits,
            },
        }
    }
}

/// The prime field the circuit is defined over.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
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
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrimitiveProgram {
    pub field: FieldSpec,
    pub vars: Vec<Var>,
    /// AssertZero-style constraints (`expression == 0`).
    pub constraints: Vec<Expression>,
    /// Ordered witness-generation program (the hint program).
    pub witness_gen: Vec<WitnessGen>,
}

/// Serialize a primitive program to **compact** JSON (the on-disk `circuit.json`
/// form). Round-trips through [`from_json`] identically to [`to_json_pretty`].
pub fn to_json(program: &PrimitiveProgram) -> String {
    serde_json::to_string(program).expect("PrimitiveProgram is always serializable")
}

pub fn to_json_pretty(program: &PrimitiveProgram) -> String {
    serde_json::to_string_pretty(program).expect("PrimitiveProgram is always serializable")
}

/// Serialize compact JSON straight into `w` (a file/`BufWriter`), never building
/// the whole JSON string in memory first — the multi-GB `circuit.json` write on
/// heavy circuits is otherwise a full extra copy of the program.
pub fn write_json<W: std::io::Write>(program: &PrimitiveProgram, w: W) -> std::io::Result<()> {
    serde_json::to_writer(w, program).map_err(std::io::Error::from)
}

/// Parse a primitive program from JSON (the inverse of [`to_json`]).
pub fn from_json(s: &str) -> Result<PrimitiveProgram, serde_json::Error> {
    serde_json::from_str(s)
}
