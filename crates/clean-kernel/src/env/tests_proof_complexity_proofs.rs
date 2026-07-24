// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for proof complexity kernel proofs (PC01-PC04).
//!
//! Verifies that all inductive types and theorem declarations are registered
//! and type-check through the kernel type checker.
//!
//! Part of #3365: Phase 4 kernel proofs.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::ExprKind;
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_proof_complexity_proofs()
        .expect("init_proof_complexity_proofs");
    env
}

#[test]
fn test_resolv_step_registered() {
    let env = make_env();
    for name in [
        "ProofComplexitySAT.ResolvStep",
        "ProofComplexitySAT.ResolvStep.input",
        "ProofComplexitySAT.ResolvStep.resolve",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

#[test]
fn test_resolv_sound_registered() {
    let env = make_env();
    for name in [
        "ProofComplexitySAT.ResolvSound",
        "ProofComplexitySAT.ResolvSound.input",
        "ProofComplexitySAT.ResolvSound.resolve",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

#[test]
fn test_resolv_complete_registered() {
    let env = make_env();
    for name in [
        "ProofComplexitySAT.ResolvComplete",
        "ProofComplexitySAT.ResolvComplete.base_empty",
        "ProofComplexitySAT.ResolvComplete.elim_var",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

#[test]
fn test_cp_step_registered() {
    let env = make_env();
    for name in [
        "ProofComplexitySAT.CPStep",
        "ProofComplexitySAT.CPStep.input",
        "ProofComplexitySAT.CPStep.addition",
        "ProofComplexitySAT.CPStep.scalar_mul",
        "ProofComplexitySAT.CPStep.division",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

#[test]
fn test_cp_sound_registered() {
    let env = make_env();
    for name in [
        "ProofComplexitySAT.CPSound",
        "ProofComplexitySAT.CPSound.input",
        "ProofComplexitySAT.CPSound.addition",
        "ProofComplexitySAT.CPSound.scalar_mul",
        "ProofComplexitySAT.CPSound.division",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

#[test]
fn test_cp_sim_resolv_registered() {
    let env = make_env();
    for name in [
        "ProofComplexitySAT.CPSimResolvStep",
        "ProofComplexitySAT.CPSimResolvStep.encode_clause",
        "ProofComplexitySAT.CPSimResolvStep.sim_resolve",
        "ProofComplexitySAT.CPSimResolvSound",
        "ProofComplexitySAT.CPSimResolvSound.encode_clause",
        "ProofComplexitySAT.CPSimResolvSound.sim_resolve",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

#[test]
fn test_pc01_theorem_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "ProofComplexitySAT.pc01_resolution_soundness"
        ))
        .is_some());
}

#[test]
fn test_pc02_axiom_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "ProofComplexitySAT.pc02_resolution_completeness"
        ))
        .is_some());
}

#[test]
fn test_pc03_axiom_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("ProofComplexitySAT.pc03_cp_soundness"))
        .is_some());
}

#[test]
fn test_pc04_axiom_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "ProofComplexitySAT.pc04_cp_subsumes_resolution"
        ))
        .is_some());
}

#[test]
fn test_pc01_is_theorem_not_axiom() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string(
            "ProofComplexitySAT.pc01_resolution_soundness",
        ))
        .expect("pc01 should exist");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "PC01 should be a Theorem, not an Axiom"
    );
}

// ====================================================================
// PC02-PC04: honest admitted AXIOMS (NOT Theorem-wrapping-Axiom masquerades)
//
// PC02/PC03/PC04 are genuine metatheorems (Davis-Putnam resolution
// completeness; cutting-planes arithmetic soundness; CP pivot/ceiling
// simulation of resolution) that are not yet structurally provable in-kernel.
// They are registered as HONEST `Declaration::Axiom`s carrying their UNWRAPPED
// propositions — NOT as `Declaration::Theorem`s whose value is `Nonempty.intro`
// over a hidden underlying axiom (the masquerade CLAUDE.md forbids). These
// guards assert the honest-axiom shape: kind == Axiom, no `Nonempty` wrapper in
// the type, and the previously-hidden `_axiom`-suffixed twin is gone (the
// canonical name now IS the axiom).
// ====================================================================

#[test]
fn test_pc02_is_axiom_not_theorem() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string(
            "ProofComplexitySAT.pc02_resolution_completeness",
        ))
        .expect("pc02 should exist");
    assert_eq!(
        info.kind,
        ConstantKind::Axiom,
        "PC02 must be an honest Axiom, not a Theorem-wrapping-Axiom masquerade"
    );
    assert!(
        info.value.is_none(),
        "PC02 axiom must carry no proof value (an admitted axiom has none)"
    );
}

#[test]
fn test_pc03_is_axiom_not_theorem() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("ProofComplexitySAT.pc03_cp_soundness"))
        .expect("pc03 should exist");
    assert_eq!(
        info.kind,
        ConstantKind::Axiom,
        "PC03 must be an honest Axiom, not a Theorem-wrapping-Axiom masquerade"
    );
    assert!(
        info.value.is_none(),
        "PC03 axiom must carry no proof value (an admitted axiom has none)"
    );
}

#[test]
fn test_pc04_is_axiom_not_theorem() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string(
            "ProofComplexitySAT.pc04_cp_subsumes_resolution",
        ))
        .expect("pc04 should exist");
    assert_eq!(
        info.kind,
        ConstantKind::Axiom,
        "PC04 must be an honest Axiom, not a Theorem-wrapping-Axiom masquerade"
    );
    assert!(
        info.value.is_none(),
        "PC04 axiom must carry no proof value (an admitted axiom has none)"
    );
}

/// The old `_axiom`-suffixed twins that the `Nonempty`-wrapping theorems leaned
/// on must be GONE: the canonical PC02/PC03/PC04 names ARE the honest axioms now,
/// so there is no separate underlying axiom for a wrapper theorem to consume.
#[test]
fn test_pc02_pc04_axiom_twins_removed() {
    let env = make_env();
    for n in [
        "ProofComplexitySAT.pc02_resolution_completeness_axiom",
        "ProofComplexitySAT.pc03_cp_soundness_axiom",
        "ProofComplexitySAT.pc04_cp_subsumes_resolution_axiom",
    ] {
        assert!(
            env.get_const(&Name::from_string(n)).is_none(),
            "{n} must be gone — the canonical name is the honest axiom, not a wrapper's hidden twin"
        );
    }
}

/// PC02/PC03/PC04 types must be the UNWRAPPED propositions — the codomain head
/// must be the domain predicate (`ResolvComplete` / `CPSound` / `CPSimResolvSound`),
/// NEVER a `Nonempty` wrapper. Guards against re-introducing the masquerade.
#[test]
fn test_pc02_pc04_types_are_unwrapped() {
    let env = make_env();
    for (name, expected_head) in [
        (
            "ProofComplexitySAT.pc02_resolution_completeness",
            "ProofComplexitySAT.ResolvComplete",
        ),
        (
            "ProofComplexitySAT.pc03_cp_soundness",
            "ProofComplexitySAT.CPSound",
        ),
        (
            "ProofComplexitySAT.pc04_cp_subsumes_resolution",
            "ProofComplexitySAT.CPSimResolvSound",
        ),
    ] {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist"));
        // Walk under the Pi binders to the codomain head.
        let mut body = &info.type_;
        while let ExprKind::Pi(_, _, b) = body.kind() {
            body = b;
        }
        let head = body.get_app_fn();
        match head.kind() {
            ExprKind::Const(head_name, _) => {
                assert_eq!(
                    head_name,
                    &Name::from_string(expected_head),
                    "{name} codomain head must be {expected_head}, not a Nonempty wrapper"
                );
                assert_ne!(
                    head_name,
                    &Name::from_string("Nonempty"),
                    "{name} must NOT be Nonempty-wrapped"
                );
            }
            other => panic!("expected Const head for {name}, got {other:?}"),
        }
    }
}

#[test]
fn test_pc01_type_checks() {
    let env = make_env();
    let expr = crate::expr::Expr::const_(
        Name::from_string("ProofComplexitySAT.pc01_resolution_soundness"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&expr).expect("PC01 should type-check");
    // forall (nc : Nat) (step : ResolvStep nc), ResolvSound nc step
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_pc02_type_checks() {
    let env = make_env();
    let expr = crate::expr::Expr::const_(
        Name::from_string("ProofComplexitySAT.pc02_resolution_completeness"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&expr).expect("PC02 should type-check");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_pc03_type_checks() {
    let env = make_env();
    let expr = crate::expr::Expr::const_(
        Name::from_string("ProofComplexitySAT.pc03_cp_soundness"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&expr).expect("PC03 should type-check");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_pc04_type_checks() {
    let env = make_env();
    let expr = crate::expr::Expr::const_(
        Name::from_string("ProofComplexitySAT.pc04_cp_subsumes_resolution"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&expr).expect("PC04 should type-check");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_proof_complexity_proofs().expect("first init");
    env.init_proof_complexity_proofs().expect("second init");
}

#[test]
fn test_cutting_planes_dependency() {
    // init_proof_complexity_proofs should also initialize cutting planes defs
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("ProofTheory.LinearInequality"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("ProofTheory.CuttingPlanesProof"))
        .is_some());
}

#[test]
fn test_resolv_step_type_checks() {
    let env = make_env();
    let expr =
        crate::expr::Expr::const_(Name::from_string("ProofComplexitySAT.ResolvStep"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&expr).expect("ResolvStep should type-check");
    // ResolvStep : Nat -> Type
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_cp_step_type_checks() {
    let env = make_env();
    let expr = crate::expr::Expr::const_(Name::from_string("ProofComplexitySAT.CPStep"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&expr).expect("CPStep should type-check");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

// ====================================================================
// PC01: genuine structural-recursion proof (no axiom, no masquerade)
// ====================================================================

/// `ResolvStep` must now be a REAL inductive: the kernel must have generated
/// its recursor `ProofComplexitySAT.ResolvStep.rec`. Without this, the PC01
/// proof term (structural recursion via the recursor) could not exist.
#[test]
fn test_resolv_step_recursor_generated() {
    let env = make_env();
    assert!(
        env.get_recursor(&Name::from_string("ProofComplexitySAT.ResolvStep.rec"))
            .is_some(),
        "ResolvStep must be a real inductive with a generated recursor"
    );
    // The constructors must be registered as genuine constructors, not opaque axioms.
    for ctor in [
        "ProofComplexitySAT.ResolvStep.input",
        "ProofComplexitySAT.ResolvStep.resolve",
    ] {
        assert!(
            env.get_constructor(&Name::from_string(ctor)).is_some(),
            "{ctor} must be a genuine constructor"
        );
    }
}

/// The PC01 *axiom* that the old `Theorem`-wrapping-`Axiom` masquerade leaned on
/// must NOT exist any more. PC01 is now a real proof, so there is no axiom to wrap.
#[test]
fn test_pc01_axiom_removed() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string(
            "ProofComplexitySAT.pc01_resolution_soundness_axiom"
        ))
        .is_none(),
        "the PC01 soundness axiom must be gone — the theorem must stand on its own proof term"
    );
}

/// PC01's stated type is the FULL soundness proposition
/// `forall (nc : Nat) (step : ResolvStep nc), ResolvSound nc step` — NOT a
/// `Nonempty`-wrapped restatement.
#[test]
fn test_pc01_type_is_unwrapped_soundness() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string(
            "ProofComplexitySAT.pc01_resolution_soundness",
        ))
        .expect("pc01 should exist");
    // forall (nc : Nat) (step : ResolvStep nc), ResolvSound nc step
    // The codomain head is ResolvSound (NOT Nonempty).
    let mut body = &info.type_;
    while let ExprKind::Pi(_, _, b) = body.kind() {
        body = b;
    }
    let head = body.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => assert_eq!(
            name,
            &Name::from_string("ProofComplexitySAT.ResolvSound"),
            "PC01 codomain head must be ResolvSound, not a Nonempty wrapper"
        ),
        other => panic!("expected Const head, got {other:?}"),
    }
}

/// The structural shape of the PC01 proof VALUE: two lambdas (`nc`, `step`) whose
/// body is an application headed by `ResolvStep.rec`. This proves the term
/// genuinely eliminates the `ResolvStep` inductive and is NOT an `Eq.refl`,
/// a `Nonempty.intro`, or an identity-on-hypothesis passthrough.
#[test]
fn test_pc01_value_is_recursor_elimination() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string(
            "ProofComplexitySAT.pc01_resolution_soundness",
        ))
        .expect("pc01 should exist");
    let value = info.value.as_ref().expect("PC01 must carry a proof value");

    // Strip the two outer lambdas (nc, step).
    let ExprKind::Lam(_, _, body1) = value.kind() else {
        panic!("PC01 value must start with a lambda (over nc)");
    };
    let ExprKind::Lam(_, _, body2) = body1.kind() else {
        panic!("PC01 value must have a second lambda (over step)");
    };

    // The lambda body must be an application whose head is ResolvStep.rec.
    let head = body2.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => assert_eq!(
            name,
            &Name::from_string("ProofComplexitySAT.ResolvStep.rec"),
            "PC01 proof body must be a ResolvStep.rec elimination"
        ),
        other => panic!("expected ResolvStep.rec head, got {other:?}"),
    }

    // Guard against masquerades: the proof must NOT reference the (now-deleted)
    // PC01 axiom, must NOT be an Eq.refl, and must NOT lean on Nonempty.intro.
    let consts = value.collect_constants();
    assert!(
        !consts.contains(&Name::from_string(
            "ProofComplexitySAT.pc01_resolution_soundness_axiom"
        )),
        "PC01 proof must not reference the soundness axiom (no circularity / no wrap)"
    );
    assert!(
        consts
            .iter()
            .all(|n| n != &Name::from_string("Eq.refl") && n != &Name::from_string("rfl")),
        "PC01 proof must not be a vacuous Eq.refl"
    );
    assert!(
        !consts.contains(&Name::from_string("Nonempty.intro")),
        "PC01 proof must produce ResolvSound directly, not a Nonempty witness"
    );
    // It MUST genuinely use the inductive's recursor and both sound constructors.
    assert!(consts.contains(&Name::from_string("ProofComplexitySAT.ResolvStep.rec")));
    assert!(consts.contains(&Name::from_string("ProofComplexitySAT.ResolvSound.input")));
    assert!(consts.contains(&Name::from_string("ProofComplexitySAT.ResolvSound.resolve")));
}

/// End-to-end kernel re-check: PC01's value type-checks against its declared
/// type. (`add_decl` already enforces this at registration; this is an explicit,
/// independent re-check that the proof term inhabits the soundness proposition.)
#[test]
fn test_pc01_value_checks_against_type() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string(
            "ProofComplexitySAT.pc01_resolution_soundness",
        ))
        .expect("pc01 should exist");
    let value = info.value.as_ref().expect("PC01 must carry a proof value");
    let tc = TypeChecker::with_mode(&env, env.mode());
    tc.check_type(value, &info.type_)
        .expect("PC01 proof term must check against the soundness proposition");
}
