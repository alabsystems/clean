// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pseudo-Boolean Constraint Verification and VeriPB Proof Kernel
//!
//! Implements pseudo-Boolean (PB) constraint types, proof derivation rules with
//! soundness guarantees, and a compiler to the VeriPB proof format.
//!
//! ## PB Constraints
//!
//! A pseudo-Boolean constraint has the form:
//!   a_1 * l_1 + a_2 * l_2 + ... + a_n * l_n >= k
//!
//! where each l_i is a literal (positive = variable, negative = negation) and
//! a_i are integer coefficients. SAT clauses are the special case where all
//! coefficients are 1 and k = 1.
//!
//! ## Proof Rules
//!
//! The PB proof system extends cutting planes with:
//! - **Addition**: sum two constraints coefficient-wise
//! - **Scalar multiplication**: multiply by a positive integer
//! - **Division**: divide by positive integer, ceiling on all terms
//! - **Saturation**: cap each coefficient at the degree
//! - **Rounding**: divide all coefficients and degree by their GCD, ceiling
//! - **Generalized resolution**: resolve two PB constraints on a variable
//!
//! ## VeriPB Format
//!
//! Compiles proofs to the VeriPB specification for external checker
//! interoperability (MaxSAT Evaluation, PB Competition, SAT-COMP proof track).
//!
//! ## References
//!
//! - Elffers & Nordstrom, "Divide and Conquer: Towards Faster Pseudo-Boolean
//!   Solving", IJCAI 2018
//! - Gocht, McCreesh, Nordstrom, "Certifying Solvers for Clique and Maximum
//!   Common (Connected) Subgraph Problems", CP 2020
//! - VeriPB: <https://github.com/StephanGocht/VeriPB>

pub(crate) mod certificate;
pub(crate) mod cnf_bridge;
pub(crate) mod conflict_analysis;
pub(crate) mod normalize;
pub(crate) mod opb_format;
pub(crate) mod rules;
pub(crate) mod soundness;
pub(crate) mod types;
pub(crate) mod veripb;
pub(crate) mod veripb_parser;

#[cfg(test)]
mod tests;

#[cfg(test)]
mod tests_saturation_regression;

#[cfg(test)]
mod tests_deletion_regression;

pub(crate) use opb_format::parse_opb;
pub(crate) use rules::{verify_rule, PbRule};
pub(crate) use types::{PbConstraint, PbFormula};

// 2026-07-31: these re-exports have no production consumer — the crate's own
// `#[cfg(test)]` fuzz and proptest modules reach the PB surface through this
// module root, while production code goes to the submodules directly. Gated on
// `cfg(test)` rather than exported unconditionally so the non-test `lib` build
// does not carry an unused import.
#[cfg(test)]
pub(crate) use cnf_bridge::cnf_to_pb;
#[cfg(test)]
pub(crate) use normalize::{is_tautology, normalize};
#[cfg(test)]
pub(crate) use opb_format::write_opb;
#[cfg(test)]
pub(crate) use veripb::{VeriPbProof, VeriPbStep};
#[cfg(test)]
pub(crate) use veripb_parser::parse_veripb;

use thiserror::Error;

/// Errors from pseudo-Boolean proof verification.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum PbError {
    /// Referenced constraint index is out of bounds.
    #[error("constraint index {index} out of bounds (have {count} constraints)")]
    IndexOutOfBounds { index: usize, count: usize },

    /// Scalar multiplier must be positive.
    #[error("scalar must be positive, got {0}")]
    NonPositiveScalar(i64),

    /// Divisor must be positive.
    #[error("divisor must be positive, got {0}")]
    NonPositiveDivisor(i64),

    /// Variable index out of range for the formula.
    #[error("variable {var} out of range for formula with {num_vars} variables")]
    VariableOutOfRange { var: u32, num_vars: u32 },

    /// Generalized resolution requires the variable to appear with opposite
    /// signs in the two constraints.
    #[error(
        "variable {var} does not appear with opposite signs in constraints {left} and {right}"
    )]
    ResolutionSignMismatch { var: u32, left: usize, right: usize },

    /// Generalized resolution requires that each constraint contains the
    /// resolution variable in only one polarity. If the left constraint
    /// contains both `+v` and `-v`, or the right contains both, the
    /// cancellation arithmetic would be wrong.
    #[error(
        "variable {var} appears in both polarities in constraint {constraint_idx} (mixed polarity)"
    )]
    ResolutionMixedPolarity { var: u32, constraint_idx: usize },

    /// Saturation requires all coefficients to be non-negative.
    ///
    /// Saturation (`min(a_i, k)`) is only sound when all coefficients are
    /// non-negative. With negative coefficients, capping positive coefficients
    /// at the degree can incorrectly strengthen the inequality. For example,
    /// `100*x1 + (-89)*x2 >= 10` saturated to `10*x1 + (-89)*x2 >= 10` loses
    /// the assignment x1=1, x2=1 (original: 11 >= 10, saturated: -79 < 10).
    ///
    /// Normalize the constraint first to eliminate negative coefficients.
    #[error("saturation unsound: coefficient {coeff} on literal {literal} is negative")]
    NegativeCoefficientInSaturation { coeff: i64, literal: i32 },

    /// Proof did not derive the empty constraint (contradiction).
    #[error("proof does not derive a contradiction")]
    NoContradiction,

    /// Conversion from cutting planes failed.
    #[error("cutting planes conversion: {0}")]
    ConversionError(String),

    /// An input constraint references a literal outside the formula.
    #[error("literal {literal} references variable outside formula bounds")]
    LiteralOutOfBounds { literal: i32 },
}
