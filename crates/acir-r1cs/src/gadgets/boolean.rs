//! Boolean enforcement.

use ark_bn254::Fr;
use ark_ff::One;
use ark_relations::gr1cs::{LinearCombination, SynthesisError, Variable};

use crate::r1cs_builder::R1csBuilder;

/// Enforce `var * (var - 1) = 0`.
///
/// Holds iff `var ∈ {0, 1}` as field elements.
pub fn enforce_boolean(builder: &R1csBuilder<'_>, var: Variable) -> Result<(), SynthesisError> {
    let lc_x = LinearCombination::from((Fr::one(), var));
    let lc_x_minus_1 = LinearCombination(vec![(Fr::one(), var), (-Fr::one(), Variable::One)]);
    builder.enforce(lc_x, lc_x_minus_1, builder.zero_lc())
}
