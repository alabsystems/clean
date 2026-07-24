// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Edit Algebra Formalization for Verified Neural Network Weight Surgery
//!
//! This module formalizes the mathematical properties of rank-1 weight edits
//! used in verified live weight surgery (dashvoice). The formalization covers:
//!
//! - **Edit invertibility**: Rank-1 updates can be exactly undone in exact
//!   arithmetic, and approximately undone in IEEE-754 with bounded error.
//! - **Bound propagation**: CROWN-verified bounds propagate through edited
//!   weights with Lipschitz-bounded degradation.
//! - **Certificate soundness**: The certificate verification logic is sound
//!   (if `verify_certificate` returns true, the stated property holds).
//! - **Edit chain composition**: Composing N edits preserves accumulated
//!   guarantees minus accumulated floating-point error.
//!
//! ## Mathematical Background
//!
//! A rank-1 weight edit is: W' = W + u * v^T where u, v are column vectors.
//! This is the fundamental operation in low-rank adapter (LoRA) fine-tuning
//! and verified weight surgery. The key algebraic properties are:
//!
//! 1. Rank-1 updates form an abelian group under addition (commutativity,
//!    associativity, identity, inverse).
//! 2. Under IEEE-754 arithmetic, exact inverses degrade to approximate
//!    inverses with error bounded by machine epsilon times condition number.
//! 3. Lipschitz continuity of the network function bounds output perturbation
//!    from weight perturbation.
//!
//! ## Cross-References
//!
//! - dashvoice `designs/2026-03-10-verified-live-weight-surgery.md`
//! - gamma-crown: delta verification for bound propagation
//! - mly: weight surgery epic (mly#1819)
//! - TorchLean (arXiv:2602.22631): formalizes models in Lean 4

mod bound_propagation;
mod certificate_logic;
mod edit_algebra;
mod edit_chain;

pub use bound_propagation::{BoundPropagationSpec, LipschitzBound, OutputBound};
pub use certificate_logic::{CertificateSpec, CertificateVerdict, EditCertificate};
pub use edit_algebra::{EditAlgebraSpec, RankOneUpdate};
pub use edit_chain::{EditChainSpec, EditSequence};

/// Error type for neural surgery formalization operations.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum NeuralSurgeryError {
    /// A theorem statement failed to verify.
    #[error("theorem verification failed: {name}: {reason}")]
    TheoremVerificationFailed {
        /// Name of the theorem that failed.
        name: String,
        /// Reason for failure.
        reason: String,
    },

    /// An algebraic property does not hold for the given inputs.
    #[error("algebraic property violated: {property}")]
    AlgebraicPropertyViolated {
        /// Description of the violated property.
        property: String,
    },

    /// Floating-point error exceeds the proven bound.
    #[error("floating-point error bound exceeded: computed={computed}, bound={bound}")]
    ErrorBoundExceeded {
        /// The computed error.
        computed: f64,
        /// The proven upper bound.
        bound: f64,
    },
}

/// Machine epsilon for IEEE-754 f32 arithmetic.
///
/// This is the smallest value such that 1.0 + EPSILON != 1.0 in f32.
pub const F32_MACHINE_EPSILON: f64 = f32::EPSILON as f64;

/// Machine epsilon for IEEE-754 f64 arithmetic.
pub const F64_MACHINE_EPSILON: f64 = f64::EPSILON;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_module_exports_accessible() {
        // Verify all public types are accessible
        let _update = RankOneUpdate::new(vec![1.0], vec![1.0]);
        let _spec = EditAlgebraSpec::new();
        let _bound = LipschitzBound::new(1.0);
        let _bspec = BoundPropagationSpec::new();
        let _cert = CertificateSpec::new();
        let _chain = EditChainSpec::new();
    }

    #[test]
    fn test_machine_epsilon_constants() {
        // These bounds are guaranteed at compile time. Using `const` assertion
        // blocks makes the constant-folded nature explicit (clippy flags plain
        // `assert!` on constant operands) while still verifying the real bounds:
        // F32 epsilon (~1.19e-7) is in (0, 1e-6) and F64 epsilon (~2.22e-16) is
        // in (0, 1e-15).
        const {
            assert!(F32_MACHINE_EPSILON > 0.0);
            assert!(F32_MACHINE_EPSILON < 1e-6);
            assert!(F64_MACHINE_EPSILON > 0.0);
            assert!(F64_MACHINE_EPSILON < 1e-15);
        }
    }
}
