// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bootstrap Trust Chain: Lean 4 Verification of clean Kernel Correctness
//!
//! This module implements the foundation for a formal bootstrap trust chain:
//! Lean 4 proves that clean's type checker kernel is correct, creating
//! transitive trust from Lean 4's verified metatheory through to clean's
//! self-verification.
//!
//! ## Architecture
//!
//! The bootstrap operates in three stages:
//!
//! 1. **Kernel Model** (`kernel_model`): A simplified formal model of clean's
//!    kernel expressed in clean's own Rust type system. This model captures
//!    the core type-checking algorithm (Sort, BVar, App, Lam, Pi, Let, Const)
//!    with explicit typing judgments and definitional equality.
//!
//! 2. **Lean 4 Bridge** (`lean4_bridge`): Generates Lean 4 source code that
//!    encodes the kernel model as Lean 4 inductive types and recursive
//!    functions. Formal soundness statements are emitted as Lean 4 theorems.
//!
//! 3. **Trust Chain** (`trust_chain`): Tracks the verification status of the
//!    bootstrap proof: which theorems have been proved in Lean 4, which are
//!    self-verified by clean, and the transitive trust implications.
//!
//! ## Key Insight
//!
//! clean can encode a model of its own kernel as typed data, then emit that
//! model as Lean 4 source for external verification. This is analogous to
//! Godel numbering but using dependent types instead of arithmetic: the
//! model is a first-class citizen in both clean's Rust representation and
//! Lean 4's type theory.
//!
//! ## References
//!
//! - Carneiro, M. (2019). "The type theory of Lean". MS Thesis, CMU.
//!   <https://github.com/digama0/lean-type-theory>
//! - de Moura, L. et al. (2021). "The Lean 4 theorem prover and programming
//!   language". CADE-28. <https://doi.org/10.1007/978-3-030-79876-5_37>
//! - Barras, B. (1999). "Auto-validation d'un systeme de preuves avec
//!   familles inductives". PhD Thesis, Paris 7. (Self-verification of Coq)

pub mod kernel_model;
pub mod lean4_bridge;
mod spec_registration;
pub mod trust_chain;

pub use kernel_model::{KernelEnv, KernelExpr, KernelLevel, ModelError, TypeInferenceResult};
pub use lean4_bridge::{Lean4EmitError, Lean4Emitter};
pub use trust_chain::{
    BootstrapTrustLevel, TrustChainReport, TrustChainStatus, TrustChainVerifier,
};

#[cfg(test)]
mod tests {
    use super::kernel_model::*;
    use super::lean4_bridge::*;
    use super::trust_chain::*;

    // ── Kernel model: type inference ────────────────────────────────────

    #[test]
    fn test_model_infer_sort_type() {
        let env = KernelEnv::empty();
        // Sort(0) = Prop : Sort(1) = Type
        let result = model_infer_type(&env, &KernelExpr::Sort(0), &[]);
        assert_eq!(
            result.expect("Sort(0) should type-check"),
            KernelExpr::Sort(1)
        );

        // Sort(1) = Type : Sort(2)
        let result = model_infer_type(&env, &KernelExpr::Sort(1), &[]);
        assert_eq!(
            result.expect("Sort(1) should type-check"),
            KernelExpr::Sort(2)
        );
    }

    #[test]
    fn test_model_infer_bvar_in_context() {
        let env = KernelEnv::empty();
        // In context [Prop], BVar(0) : Prop
        let ctx = vec![KernelExpr::Sort(0)];
        let result = model_infer_type(&env, &KernelExpr::BVar(0), &ctx);
        assert_eq!(
            result.expect("BVar(0) in [Prop] should type-check"),
            KernelExpr::Sort(0)
        );
    }

    #[test]
    fn test_model_infer_bvar_unbound_error() {
        let env = KernelEnv::empty();
        let result = model_infer_type(&env, &KernelExpr::BVar(0), &[]);
        assert!(result.is_err(), "BVar(0) in empty context should fail");
    }

    #[test]
    fn test_model_infer_pi_type() {
        let env = KernelEnv::empty();
        // Pi(Prop, Prop) : Sort(imax(1, 1)) = Sort(1) = Type
        let pi = KernelExpr::Pi(Box::new(KernelExpr::Sort(0)), Box::new(KernelExpr::Sort(0)));
        let result = model_infer_type(&env, &pi, &[]);
        assert_eq!(
            result.expect("Pi(Prop, Prop) should type-check"),
            KernelExpr::Sort(1)
        );
    }

    #[test]
    fn test_model_infer_pi_into_prop() {
        let env = KernelEnv::empty();
        // Pi(Type, Prop) : Sort(imax(2, 1)) = Sort(2)
        // But since codomain Sort(0) = Prop, imax(2, 0) = 0 (impredicative)
        // Actually: Pi(Sort(1), Sort(0)) means domain_ty = Sort(2) so domain_level = 2,
        // codomain context has Sort(1), codomain is Sort(0) so codomain_ty = Sort(1),
        // codomain_level = 1. imax(2, 1) = 2.
        //
        // For impredicativity: Pi(Type, BVar(0)) where BVar(0) : Prop would give
        // imax(2, 0) = 0.
        let pi = KernelExpr::Pi(
            Box::new(KernelExpr::Sort(1)), // domain = Type
            Box::new(KernelExpr::Sort(0)), // codomain = Prop
        );
        let result = model_infer_type(&env, &pi, &[]);
        // domain_level = 2 (Sort(1) : Sort(2)), codomain_level = 1 (Sort(0) : Sort(1))
        // imax(2, 1) = 2
        assert_eq!(
            result.expect("Pi(Type, Prop) should type-check"),
            KernelExpr::Sort(2)
        );
    }

    #[test]
    fn test_model_infer_lam_type() {
        let env = KernelEnv::empty();
        // Lam(Prop, BVar(0)) : Pi(Prop, Prop) — the identity on Prop
        let lam = KernelExpr::Lam(Box::new(KernelExpr::Sort(0)), Box::new(KernelExpr::BVar(0)));
        let result = model_infer_type(&env, &lam, &[]);
        let expected = KernelExpr::Pi(Box::new(KernelExpr::Sort(0)), Box::new(KernelExpr::Sort(0)));
        assert_eq!(
            result.expect("identity on Prop should type-check"),
            expected
        );
    }

    #[test]
    fn test_model_infer_app_beta() {
        let env = KernelEnv::empty();
        // App(Lam(Type, BVar(0)), Prop) : Type
        // The identity on Type applied to Prop should give Type (the type of Prop)
        let app = KernelExpr::App(
            Box::new(KernelExpr::Lam(
                Box::new(KernelExpr::Sort(1)), // domain = Type
                Box::new(KernelExpr::BVar(0)), // body = x
            )),
            Box::new(KernelExpr::Sort(0)), // arg = Prop
        );
        let result = model_infer_type(&env, &app, &[]);
        // fun (x : Type) => x applied to Prop: type is instantiate(Type, Prop)
        // The return type of the lambda is Pi(Type, Type) (inferred from body BVar(0) : Type)
        // Wait: body BVar(0) has type = the domain = Sort(1) = Type, lifted.
        // So the lambda type is Pi(Sort(1), Sort(1)).
        // Applying to Sort(0): codomain is Sort(1), instantiate(Sort(1), Sort(0)) = Sort(1).
        assert_eq!(
            result.expect("identity applied to Prop should type-check"),
            KernelExpr::Sort(1)
        );
    }

    #[test]
    fn test_model_infer_let() {
        let env = KernelEnv::empty();
        // let x : Type := Prop in x => Prop, which has type Type
        // Actually: let desugars to substitution, so we infer type of body[val/x].
        // body = BVar(0), val = Sort(0), so body[val/0] = Sort(0). Type of Sort(0) = Sort(1).
        let let_expr = KernelExpr::Let(
            Box::new(KernelExpr::Sort(1)), // type annotation: Type
            Box::new(KernelExpr::Sort(0)), // value: Prop
            Box::new(KernelExpr::BVar(0)), // body: x
        );
        let result = model_infer_type(&env, &let_expr, &[]);
        assert_eq!(
            result.expect("let x : Type := Prop in x should type-check"),
            KernelExpr::Sort(1)
        );
    }

    #[test]
    fn test_model_infer_let_rejects_value_annotation_mismatch() {
        let env = KernelEnv::empty();
        // Prop has type Type, not Prop. The old model inferred both sides but
        // never compared them, so this invalid annotated let was accepted.
        let let_expr = KernelExpr::Let(
            Box::new(KernelExpr::Sort(0)),
            Box::new(KernelExpr::Sort(0)),
            Box::new(KernelExpr::BVar(0)),
        );
        assert!(
            matches!(
                model_infer_type(&env, &let_expr, &[]),
                Err(ModelError::TypeMismatch { .. })
            ),
            "a let value must have its declared annotation"
        );
    }

    #[test]
    fn test_model_infer_let_rejects_annotation_whose_type_is_not_a_sort() {
        let mut env = KernelEnv::empty();
        env.add_const(
            "NotAType",
            KernelExpr::Const("OpaqueNonSort".to_string(), vec![]),
            None,
        );
        let let_expr = KernelExpr::Let(
            Box::new(KernelExpr::Const("NotAType".to_string(), vec![])),
            Box::new(KernelExpr::Sort(0)),
            Box::new(KernelExpr::BVar(0)),
        );
        assert!(
            matches!(
                model_infer_type(&env, &let_expr, &[]),
                Err(ModelError::ExpectedSort(_))
            ),
            "a let annotation must itself inhabit a sort"
        );
    }

    #[test]
    fn test_model_infer_const_in_env() {
        let mut env = KernelEnv::empty();
        env.add_const("Nat", KernelExpr::Sort(1), None);
        let result = model_infer_type(&env, &KernelExpr::Const("Nat".to_string(), vec![]), &[]);
        assert_eq!(
            result.expect("Nat constant should type-check"),
            KernelExpr::Sort(1)
        );
    }

    #[test]
    fn test_model_infer_unknown_const_error() {
        let env = KernelEnv::empty();
        let result = model_infer_type(&env, &KernelExpr::Const("Unknown".to_string(), vec![]), &[]);
        assert!(result.is_err(), "Unknown constant should fail");
    }

    // ── Kernel model: definitional equality ─────────────────────────────

    #[test]
    fn test_model_def_eq_reflexive() {
        let env = KernelEnv::empty();
        let expr = KernelExpr::Sort(0);
        assert!(model_is_def_eq(&env, &expr, &expr));
    }

    #[test]
    fn test_model_def_eq_beta_reduction() {
        let env = KernelEnv::empty();
        // (fun (x : Type) => x) Prop  =β  Prop
        let app = KernelExpr::App(
            Box::new(KernelExpr::Lam(
                Box::new(KernelExpr::Sort(1)),
                Box::new(KernelExpr::BVar(0)),
            )),
            Box::new(KernelExpr::Sort(0)),
        );
        assert!(model_is_def_eq(&env, &app, &KernelExpr::Sort(0)));
    }

    #[test]
    fn test_model_def_eq_different_sorts() {
        let env = KernelEnv::empty();
        assert!(!model_is_def_eq(
            &env,
            &KernelExpr::Sort(0),
            &KernelExpr::Sort(1)
        ));
    }

    #[test]
    fn test_model_def_eq_delta_reduction() {
        let mut env = KernelEnv::empty();
        env.add_const("myProp", KernelExpr::Sort(1), Some(KernelExpr::Sort(0)));
        // myProp  =δ  Prop  (via constant unfolding)
        let c = KernelExpr::Const("myProp".to_string(), vec![]);
        assert!(model_is_def_eq(&env, &c, &KernelExpr::Sort(0)));
    }

    // ── Lean 4 emitter ──────────────────────────────────────────────────

    #[test]
    fn test_lean4_emitter_kernel_model_contains_kexpr() {
        let emitter = Lean4Emitter::new();
        let output = emitter.emit_kernel_model();
        assert!(
            output.contains("inductive KExpr"),
            "output should contain KExpr definition"
        );
        assert!(
            output.contains("inductive Level"),
            "output should contain Level definition"
        );
        assert!(
            output.contains("| sort"),
            "output should contain sort constructor"
        );
        assert!(
            output.contains("| bvar"),
            "output should contain bvar constructor"
        );
        assert!(
            output.contains("| app"),
            "output should contain app constructor"
        );
        assert!(
            output.contains("| lam"),
            "output should contain lam constructor"
        );
        assert!(
            output.contains("| pi"),
            "output should contain pi constructor"
        );
    }

    #[test]
    fn test_lean4_emitter_soundness_contains_theorems() {
        let emitter = Lean4Emitter::new();
        let output = emitter.emit_soundness_statements();
        assert!(
            output.contains("theorem type_preservation"),
            "output should contain type_preservation"
        );
        assert!(
            output.contains("theorem progress"),
            "output should contain progress"
        );
        assert!(
            output.contains("theorem confluence"),
            "output should contain confluence"
        );
    }

    #[test]
    fn test_lean4_emitter_with_namespace() {
        let emitter = Lean4Emitter::with_namespace("clean.Bootstrap");
        let output = emitter.emit_kernel_model();
        assert!(
            output.contains("namespace clean.Bootstrap"),
            "output should contain namespace"
        );
        assert!(
            output.contains("end clean.Bootstrap"),
            "output should contain end namespace"
        );
    }

    #[test]
    fn test_lean4_emitter_contains_lift_and_instantiate() {
        let emitter = Lean4Emitter::new();
        let output = emitter.emit_kernel_model();
        assert!(
            output.contains("def liftAt"),
            "output should contain liftAt"
        );
        assert!(
            output.contains("def instantiateAt"),
            "output should contain instantiateAt"
        );
        assert!(
            output.contains("def instantiate"),
            "output should contain instantiate"
        );
    }

    // ── Trust chain ─────────────────────────────────────────────────────

    #[test]
    fn test_trust_chain_initial_unverified() {
        let verifier = TrustChainVerifier::new();
        let report = verifier.verify_trust_chain();
        assert_eq!(report.status, TrustChainStatus::Unverified);
        assert!(report.lean4_proved_theorems.is_empty());
        assert!(report.self_verified_theorems.is_empty());
    }

    #[test]
    fn test_trust_chain_partial_with_some_proofs() {
        let mut verifier = TrustChainVerifier::new();
        verifier.add_lean4_proof("type_preservation");
        let report = verifier.verify_trust_chain();
        assert_eq!(report.status, TrustChainStatus::Partial);
        assert_eq!(report.lean4_proved_theorems.len(), 1);
    }

    #[test]
    fn test_trust_chain_complete_with_all_proofs() {
        let mut verifier = TrustChainVerifier::new();
        verifier.add_lean4_proof("type_preservation");
        verifier.add_lean4_proof("progress");
        verifier.add_lean4_proof("confluence");
        verifier.add_self_verification("model_fidelity");
        verifier.add_self_verification("cross_validation");
        let report = verifier.verify_trust_chain();
        assert_eq!(report.status, TrustChainStatus::Complete);
    }

    #[test]
    fn test_trust_level_ordering() {
        assert!(BootstrapTrustLevel::Unverified < BootstrapTrustLevel::Lean4Proved);
        assert!(BootstrapTrustLevel::Lean4Proved < BootstrapTrustLevel::SelfVerified);
        assert!(BootstrapTrustLevel::SelfVerified < BootstrapTrustLevel::FullyVerified);
    }
}
