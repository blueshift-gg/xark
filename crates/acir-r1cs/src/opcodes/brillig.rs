//! Lowering arm for `Opcode::BrilligCall` (ROADMAP step **WS-C.2**).
//!
//! Brillig is Noir's unconstrained VM used to compute *hint* witnesses
//! (modular inverses, bit decompositions, division quotient/remainder, etc.).
//! Per the design note `docs/brillig.md` we adopt the **trust-outputs**
//! strategy: we do not re-execute the Brillig bytecode and we do not emit
//! any constraint for the call itself. Instead, we simply ensure every
//! declared output witness is allocated in the constraint system so it is
//! pinned to whatever value the witness map already contains at proving
//! time.
//!
//! Soundness rests on Noir's compiler contract that every Brillig output is
//! also referenced by at least one surrounding `Opcode::AssertZero` that
//! constrains its value relative to other witnesses. Those `AssertZero`
//! opcodes are lowered normally by `lower_assert_zero` and form the
//! check-half of the hint/check pattern. See `docs/brillig.md` for the
//! full soundness argument, predicate-handling rationale, and the
//! compiler-bug fence (i.e. what happens when the (SI) invariant is
//! violated).
//!
//! The `predicate` field of `Opcode::BrilligCall` is intentionally not
//! consumed here: Noir guarantees the surrounding `AssertZero` opcodes are
//! already gated on the same predicate (typically via
//! `predicate * residual = 0` rewrites in the compiler), so the predicate's
//! effect is already encoded in the ACIR we lower.

use acir::circuit::brillig::BrilligOutputs;
use ark_relations::r1cs::SynthesisError;

use crate::artifact::WitnessIndex;
use crate::r1cs_builder::R1csBuilder;

/// Lower an `Opcode::BrilligCall` via the trust-outputs strategy.
///
/// For every declared output (`Simple` or `Array`), allocate the
/// corresponding ACIR witness in the constraint system if it has not been
/// allocated already. `R1csBuilder::alloc_witness` is idempotent — if the
/// witness has already been referenced by an earlier opcode it returns the
/// existing `Variable` without re-allocating — so this is safe to call
/// regardless of opcode ordering. No additional constraints are emitted;
/// the surrounding `AssertZero` opcodes are responsible for pinning the
/// outputs (see module docs and `docs/brillig.md`).
pub fn lower_brillig_call(
    builder: &mut R1csBuilder<'_>,
    outputs: &[BrilligOutputs],
) -> Result<(), SynthesisError> {
    for out in outputs {
        match out {
            BrilligOutputs::Simple(w) => {
                let _ = builder.alloc_witness(WitnessIndex::from_witness(*w))?;
            }
            BrilligOutputs::Array(ws) => {
                for w in ws {
                    let _ = builder.alloc_witness(WitnessIndex::from_witness(*w))?;
                }
            }
        }
    }
    Ok(())
}
