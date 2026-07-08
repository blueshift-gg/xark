//! Linear combinations over circuit variables.
//!
//! A [`LinearCombination`] is `constant + sum(coeff_i * var_i)`. The lowering
//! keeps additions/subtractions/negations as linear combinations and only
//! allocates a fresh variable when a genuine multiplication happens, keeping the
//! emitted R1CS compact.

use serde::{Deserialize, Serialize};

use crate::field::FieldConst;

pub type VarId = u32;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Term {
    pub coeff: FieldConst,
    pub var: VarId,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LinearCombination {
    pub constant: FieldConst,
    pub terms: Vec<Term>,
}

impl LinearCombination {
    pub fn zero() -> Self {
        LinearCombination {
            constant: FieldConst::zero(),
            terms: Vec::new(),
        }
    }

    pub fn one() -> Self {
        LinearCombination {
            constant: FieldConst::one(),
            terms: Vec::new(),
        }
    }

    pub fn var(var: VarId) -> Self {
        LinearCombination {
            constant: FieldConst::zero(),
            terms: vec![Term {
                coeff: FieldConst::one(),
                var,
            }],
        }
    }

    pub fn constant(decimal: impl Into<String>) -> Self {
        LinearCombination {
            constant: FieldConst {
                decimal: decimal.into(),
            },
            terms: Vec::new(),
        }
    }

    /// Multiply the whole linear combination by a field constant.
    ///
    /// This is the key "linear" operation: `c * (a·x + b·y + k)` stays a linear
    /// combination `(c·a)·x + (c·b)·y + c·k`, so a constant-by-variable product
    /// never needs a multiplication gate.
    pub fn scale(mut self, scalar: &FieldConst) -> Self {
        self.constant = self.constant.mul(scalar);
        for term in &mut self.terms {
            term.coeff = term.coeff.mul(scalar);
        }
        self.simplified()
    }

    /// Is this LC a bare constant (no variable terms)?
    pub fn is_constant(&self) -> bool {
        self.terms.is_empty()
    }

    /// Is this LC exactly the constant zero?
    pub fn is_zero(&self) -> bool {
        self.terms.is_empty() && self.constant.is_zero()
    }

    /// Combine duplicate variables, drop zero-coefficient terms, and sort terms
    /// by `VarId` for deterministic output.
    pub fn simplified(mut self) -> Self {
        self.terms.sort_by_key(|t| t.var);

        let mut merged: Vec<Term> = Vec::with_capacity(self.terms.len());
        for term in self.terms.drain(..) {
            if let Some(last) = merged.last_mut() {
                if last.var == term.var {
                    last.coeff = last.coeff.add(&term.coeff);
                    continue;
                }
            }
            merged.push(term);
        }
        merged.retain(|t| !t.coeff.is_zero());

        self.terms = merged;
        self
    }
}

impl std::ops::Add for LinearCombination {
    type Output = LinearCombination;

    fn add(mut self, rhs: Self) -> Self {
        self.constant = self.constant.add(&rhs.constant);
        self.terms.extend(rhs.terms);
        self.simplified()
    }
}

impl std::ops::Sub for LinearCombination {
    type Output = LinearCombination;

    fn sub(self, rhs: Self) -> Self {
        self + (-rhs)
    }
}

impl std::ops::Neg for LinearCombination {
    type Output = LinearCombination;

    fn neg(mut self) -> Self {
        self.constant = self.constant.neg();
        for term in &mut self.terms {
            term.coeff = term.coeff.neg();
        }
        self
    }
}
