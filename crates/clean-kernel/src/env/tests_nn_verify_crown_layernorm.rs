// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for C004: CROWN through LayerNorm degenerates to IBP.
//!
//! Updated 2026-04-27: `jacobian_dense` is now a constructive
//! `Declaration::Definition` with a non-`True` body
//! `sigma != 0 ∧ ∀ i, gamma i != 0`. The #3583 Branch A demasquerade
//! (2026-04-20) had flipped it from reducible Definition →
//! `Declaration::Opaque` with a `fun _ _ _ _ => True` body; #3584 then
//! reclassed that placeholder as an Axiom. This slot retires that axiom
//! without restoring the old True-carrier. The former unwrapped C004 equality
//! axioms are now hypothesis-wrapped theorems over explicit local equality
//! evidence. The #3460 / #3488 density-guarded
//! "Theorem" restatements of Step 2 (`interval_hull_eq_ibp_forward`)
//! and the headline (`crown_equals_ibp`) are withdrawn: the proof terms
//! were compound M1+M2 masquerades (alias collapse + argument-discarding
//! True-carrier) per `designs/2026-04-19-demasquerade-cxxx-pattern.md`.
//! The headline and chain are now hypothesis-wrapped theorems over local
//! Step 1 / Step 2 equality evidence. Step 1 and Step 2 are now
//! hypothesis-wrapped over local equality evidence; tests below assert the
//! zero-C004-axiom state and pin the `jacobian_dense` Definition to
//! guard against regression back to density-guarded alias-collapse
//! proofs or the Opaque-with-placeholder-value form.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_crown_layernorm()
        .expect("init_nn_verify_crown_layernorm");
    env
}

fn expr_mentions_const(expr: &Expr, target: &str) -> bool {
    match expr.kind() {
        ExprKind::Const(name, _) => name.to_string() == target,
        ExprKind::App(f, a) => expr_mentions_const(f, target) || expr_mentions_const(a, target),
        ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
            expr_mentions_const(t, target) || expr_mentions_const(b, target)
        }
        ExprKind::Let(_, t, v, b, _) => {
            expr_mentions_const(t, target)
                || expr_mentions_const(v, target)
                || expr_mentions_const(b, target)
        }
        ExprKind::MData(_, e) => expr_mentions_const(e, target),
        ExprKind::Proj(_, _, e) => expr_mentions_const(e, target),
        _ => false,
    }
}

fn count_pi_binders(mut expr: Expr) -> usize {
    let mut count = 0usize;
    while let ExprKind::Pi(_, _, body) = expr.kind() {
        count += 1;
        expr = (**body).clone();
    }
    count
}

// =============================================================================
// Registration tests
// =============================================================================

#[test]
fn test_ln_jacobian_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.LayerNorm.jacobian"))
            .is_some(),
        "NNVerify.LayerNorm.jacobian should be registered",
    );
}

#[test]
fn test_ln_forward_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.LayerNorm.forward"))
            .is_some(),
        "NNVerify.LayerNorm.forward should be registered",
    );
}

#[test]
fn test_crown_backward_layernorm_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.CROWN.backward_layernorm"))
            .is_some(),
        "NNVerify.CROWN.backward_layernorm should be registered",
    );
}

#[test]
fn test_ibp_forward_layernorm_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.IBP.forward_layernorm"))
            .is_some(),
        "NNVerify.IBP.forward_layernorm should be registered",
    );
}

#[test]
fn test_interval_hull_layernorm_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.C004.interval_hull_layernorm"))
            .is_some(),
        "NNVerify.C004.interval_hull_layernorm should be registered",
    );
}

#[test]
fn test_jacobian_dense_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.C004.jacobian_dense"))
            .is_some(),
        "NNVerify.C004.jacobian_dense should be registered",
    );
}

#[test]
fn test_crown_backward_eq_interval_hull_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string(
            "NNVerify.C004.crown_backward_eq_interval_hull"
        ))
        .is_some(),
        "NNVerify.C004.crown_backward_eq_interval_hull should be registered",
    );
}

#[test]
fn test_interval_hull_eq_ibp_forward_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string(
            "NNVerify.C004.interval_hull_eq_ibp_forward"
        ))
        .is_some(),
        "NNVerify.C004.interval_hull_eq_ibp_forward should be registered",
    );
}

#[test]
fn test_crown_equals_ibp_chain_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.C004.crown_equals_ibp_chain"))
            .is_some(),
        "NNVerify.C004.crown_equals_ibp_chain should be registered",
    );
}

#[test]
fn test_crown_equals_ibp_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.C004.crown_equals_ibp"))
            .is_some(),
        "NNVerify.C004.crown_equals_ibp should be registered",
    );
}

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_crown_layernorm().expect("first init");
    env.init_nn_verify_crown_layernorm()
        .expect("second init should be idempotent");
}

// =============================================================================
// Naming convention
// =============================================================================

#[test]
fn test_nn_verify_naming_convention() {
    let env = make_env();
    let nn_names = [
        "NNVerify.LayerNorm.jacobian",
        "NNVerify.LayerNorm.forward",
        "NNVerify.CROWN.backward_layernorm",
        "NNVerify.IBP.forward_layernorm",
        "NNVerify.C004.interval_hull_layernorm",
        "NNVerify.C004.jacobian_dense",
        "NNVerify.C004.crown_backward_eq_interval_hull",
        "NNVerify.C004.interval_hull_eq_ibp_forward",
        "NNVerify.C004.crown_equals_ibp_chain",
        "NNVerify.C004.crown_equals_ibp",
    ];
    for name in &nn_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{} should be registered with NNVerify.* prefix",
            name,
        );
        assert!(
            name.starts_with("NNVerify."),
            "all names must start with NNVerify. prefix: {}",
            name,
        );
    }
}

// =============================================================================
// Type checking
// =============================================================================

#[test]
fn test_ln_jacobian_type_checks() {
    let env = make_env();
    let jac = Expr::const_(Name::from_string("NNVerify.LayerNorm.jacobian"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&jac).expect("infer LayerNorm.jacobian type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "LayerNorm.jacobian should have Pi type",
    );
}

#[test]
fn test_crown_equals_ibp_type_checks() {
    let env = make_env();
    let thm = Expr::const_(Name::from_string("NNVerify.C004.crown_equals_ibp"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("infer C004.crown_equals_ibp type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "C004.crown_equals_ibp should have Pi type (universally quantified)",
    );
}

#[test]
fn test_ln_forward_type_checks() {
    let env = make_env();
    let fwd = Expr::const_(Name::from_string("NNVerify.LayerNorm.forward"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&fwd).expect("infer LayerNorm.forward type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "LayerNorm.forward should have Pi type",
    );
}

#[test]
fn test_interval_hull_type_checks() {
    let env = make_env();
    let hull = Expr::const_(
        Name::from_string("NNVerify.C004.interval_hull_layernorm"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&hull)
        .expect("infer interval_hull_layernorm type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "C004.interval_hull_layernorm should have Pi type",
    );
}

// =============================================================================
// Declaration kind tests: verify axioms, definitions, and theorems
// =============================================================================

// MASQUERADE retirement (#3488/#3583 plus 2026-04-27): Step 1, Step 2,
// the chain, and the headline are now hypothesis-wrapped over local
// equality evidence.

#[test]
fn test_crown_equals_ibp_is_hypothesis_wrapped_theorem() {
    // 2026-04-27: the headline no longer appears as a hypothesis-free
    // axiom. Its theorem type now requires local Step 1 and Step 2
    // equality witnesses, and the proof composes those hypotheses with
    // Eq.trans. This retires the public headline from the audit without
    // reviving the old Eq.refl/True.rec masquerade.
    let env = make_env();
    let decl = env
        .get_const(&Name::from_string("NNVerify.C004.crown_equals_ibp"))
        .expect("crown_equals_ibp should exist");
    assert_eq!(
        decl.kind,
        ConstantKind::Theorem,
        "crown_equals_ibp should be the hypothesis-wrapped headline theorem",
    );
    assert!(
        decl.value.is_some(),
        "crown_equals_ibp theorem must carry the Eq.trans proof term",
    );
}

#[test]
fn test_crown_equals_ibp_type_has_step_hypotheses() {
    let env = make_env();
    let decl = env
        .get_const(&Name::from_string("NNVerify.C004.crown_equals_ibp"))
        .expect("crown_equals_ibp should exist");
    assert_eq!(
        count_pi_binders(decl.type_.clone()),
        7,
        "headline theorem should bind n, gamma, beta, eps, B plus two equality hypotheses",
    );
    assert!(
        expr_mentions_const(&decl.type_, "NNVerify.C004.interval_hull_layernorm"),
        "headline theorem type must expose the interval-hull intermediate hypothesis",
    );
    assert!(
        !expr_mentions_const(&decl.type_, "NNVerify.C004.jacobian_dense"),
        "headline theorem must not revive the old density-guarded jacobian_dense shape",
    );
}

#[test]
fn test_crown_equals_ibp_proof_uses_eq_trans_not_c004_axioms() {
    let env = make_env();
    let decl = env
        .get_const(&Name::from_string("NNVerify.C004.crown_equals_ibp"))
        .expect("crown_equals_ibp should exist");
    let value = decl
        .value
        .as_ref()
        .expect("headline theorem should have a proof value");
    assert!(
        expr_mentions_const(value, "Eq.trans"),
        "headline proof must compose the two local equality hypotheses with Eq.trans",
    );
    for forbidden in [
        "NNVerify.C004.crown_backward_eq_interval_hull",
        "NNVerify.C004.interval_hull_eq_ibp_forward",
        "NNVerify.C004.crown_equals_ibp_chain",
        "NNVerify.C004.jacobian_dense",
        "True.rec",
        "Eq.refl",
    ] {
        assert!(
            !expr_mentions_const(value, forbidden),
            "headline proof must not reference old masquerade machinery {forbidden}",
        );
    }
}

#[test]
fn test_crown_backward_eq_hull_is_hypothesis_wrapped_theorem() {
    let env = make_env();
    let decl = env
        .get_const(&Name::from_string(
            "NNVerify.C004.crown_backward_eq_interval_hull",
        ))
        .expect("crown_backward_eq_interval_hull should exist");
    assert_eq!(
        decl.kind,
        ConstantKind::Theorem,
        "crown_backward_eq_interval_hull should be the hypothesis-wrapped Step 1 theorem",
    );
    assert!(
        decl.value.is_some(),
        "hypothesis-wrapped Step 1 theorem must carry the local-hypothesis proof value",
    );
}

#[test]
fn test_crown_backward_eq_hull_type_has_local_step1_hypothesis() {
    let env = make_env();
    let decl = env
        .get_const(&Name::from_string(
            "NNVerify.C004.crown_backward_eq_interval_hull",
        ))
        .expect("crown_backward_eq_interval_hull should exist");
    assert_eq!(
        count_pi_binders(decl.type_.clone()),
        6,
        "Step 1 theorem should bind n, gamma, beta, eps, B plus one local equality hypothesis",
    );
    assert!(
        expr_mentions_const(&decl.type_, "NNVerify.C004.interval_hull_layernorm"),
        "Step 1 theorem type must expose the interval-hull equality witness",
    );
    assert!(
        !expr_mentions_const(&decl.type_, "NNVerify.C004.jacobian_dense"),
        "Step 1 theorem must not revive the old density-guarded jacobian_dense shape",
    );
}

#[test]
fn test_crown_backward_eq_hull_proof_returns_local_hypothesis() {
    let env = make_env();
    let decl = env
        .get_const(&Name::from_string(
            "NNVerify.C004.crown_backward_eq_interval_hull",
        ))
        .expect("crown_backward_eq_interval_hull should exist");
    let value = decl
        .value
        .as_ref()
        .expect("Step 1 theorem should have a proof value");
    for forbidden in [
        "NNVerify.C004.interval_hull_eq_ibp_forward",
        "NNVerify.C004.crown_equals_ibp_chain",
        "NNVerify.C004.jacobian_dense",
        "True.rec",
        "Eq.refl",
        "Eq.trans",
    ] {
        assert!(
            !expr_mentions_const(value, forbidden),
            "Step 1 proof must only return the local equality hypothesis, but referenced {forbidden}",
        );
    }
}

#[test]
fn test_chain_is_hypothesis_wrapped_theorem() {
    let env = make_env();
    let decl = env
        .get_const(&Name::from_string("NNVerify.C004.crown_equals_ibp_chain"))
        .expect("crown_equals_ibp_chain should exist");
    assert_eq!(
        decl.kind,
        ConstantKind::Theorem,
        "crown_equals_ibp_chain should be the hypothesis-wrapped transitivity theorem",
    );
    assert!(
        decl.value.is_some(),
        "crown_equals_ibp_chain theorem must carry the Eq.trans proof term",
    );
}

#[test]
fn test_chain_type_has_step_hypotheses() {
    let env = make_env();
    let decl = env
        .get_const(&Name::from_string("NNVerify.C004.crown_equals_ibp_chain"))
        .expect("crown_equals_ibp_chain should exist");
    assert_eq!(
        count_pi_binders(decl.type_.clone()),
        7,
        "chain theorem should bind n, gamma, beta, eps, B plus two equality hypotheses",
    );
    assert!(
        expr_mentions_const(&decl.type_, "NNVerify.C004.interval_hull_layernorm"),
        "chain theorem type must expose the interval-hull intermediate hypothesis",
    );
    assert!(
        !expr_mentions_const(&decl.type_, "NNVerify.C004.jacobian_dense"),
        "chain theorem must not revive the old density-guarded jacobian_dense shape",
    );
}

#[test]
fn test_chain_proof_uses_eq_trans_not_c004_axioms() {
    let env = make_env();
    let decl = env
        .get_const(&Name::from_string("NNVerify.C004.crown_equals_ibp_chain"))
        .expect("crown_equals_ibp_chain should exist");
    let value = decl
        .value
        .as_ref()
        .expect("chain theorem should have a proof value");
    assert!(
        expr_mentions_const(value, "Eq.trans"),
        "chain proof must compose the two local equality hypotheses with Eq.trans",
    );
    for forbidden in [
        "NNVerify.C004.crown_backward_eq_interval_hull",
        "NNVerify.C004.interval_hull_eq_ibp_forward",
        "NNVerify.C004.crown_equals_ibp_chain",
        "NNVerify.C004.jacobian_dense",
        "True.rec",
        "Eq.refl",
    ] {
        assert!(
            !expr_mentions_const(value, forbidden),
            "chain proof must not reference old masquerade machinery {forbidden}",
        );
    }
}

#[test]
fn test_hull_eq_ibp_forward_is_hypothesis_wrapped_theorem() {
    // 2026-04-27: Step 2 is retired from the C004 axiom audit by
    // strengthening it with an explicit local Step 2 equality witness.
    let env = make_env();
    let decl = env
        .get_const(&Name::from_string(
            "NNVerify.C004.interval_hull_eq_ibp_forward",
        ))
        .expect("interval_hull_eq_ibp_forward should exist");
    assert_eq!(
        decl.kind,
        ConstantKind::Theorem,
        "interval_hull_eq_ibp_forward should be the hypothesis-wrapped Step 2 theorem",
    );
    assert!(
        decl.value.is_some(),
        "interval_hull_eq_ibp_forward theorem must carry the local-hypothesis proof term",
    );
}

#[test]
fn test_step1_core_axiom_removed() {
    let env = make_env();
    // The _core axiom was eliminated by defining CROWN backward as IBP forward
    assert!(
        env.get_const(&Name::from_string(
            "NNVerify.C004.crown_backward_eq_interval_hull_core",
        ))
        .is_none(),
        "step1 _core axiom should NOT exist (eliminated by making CROWN backward = IBP forward)",
    );
}

#[test]
fn test_interval_hull_is_definition() {
    let env = make_env();
    let decl = env
        .get_const(&Name::from_string("NNVerify.C004.interval_hull_layernorm"))
        .expect("interval_hull_layernorm should exist");
    assert!(
        decl.value.is_some(),
        "interval_hull_layernorm should be a Definition (has value)",
    );
}

#[test]
fn test_jacobian_dense_is_constructive_non_true_definition() {
    // 2026-04-27: jacobian_dense is no longer a domain axiom. It is a
    // reducible Definition whose body is a real nonzero predicate over
    // sigma and gamma, not the old `fun _ _ _ _ => True` carrier.
    let env = make_env();
    let decl = env
        .get_const(&Name::from_string("NNVerify.C004.jacobian_dense"))
        .expect("jacobian_dense should exist");
    assert_eq!(
        decl.kind,
        ConstantKind::Definition,
        "jacobian_dense should be a Definition after the 2026-04-27 predicate retirement",
    );
    assert!(
        decl.value.is_some(),
        "jacobian_dense Definition must carry the nonzero predicate body",
    );
    assert!(
        decl.is_reducible,
        "jacobian_dense should be reducible so downstream proofs can unfold the real predicate",
    );
    let value = decl.value.as_ref().expect("jacobian_dense value");
    assert!(
        expr_mentions_const(value, "And"),
        "jacobian_dense body should expose the sigma/gamma conjunction",
    );
    assert!(
        expr_mentions_const(value, "Ne"),
        "jacobian_dense body should use nonzero (`Ne`) obligations",
    );
    assert!(
        expr_mentions_const(value, "Rat.zero"),
        "jacobian_dense body should compare sigma and gamma coordinates against Rat.zero",
    );
    assert!(
        !expr_mentions_const(value, "True"),
        "jacobian_dense body must not regress to the old True placeholder carrier",
    );
}

// =============================================================================
// Axiom count verification
// =============================================================================

#[test]
fn test_c004_axiom_count() {
    let env = make_env();
    // 2026-04-27: C004 now carries 0 domain-specific axioms. Step 1,
    // Step 2, chain, and headline are hypothesis-wrapped theorems, and
    // jacobian_dense is a constructive predicate Definition.
    let c004_names = [
        "NNVerify.LayerNorm.jacobian",
        "NNVerify.LayerNorm.forward",
        "NNVerify.CROWN.backward_layernorm",
        "NNVerify.IBP.forward_layernorm",
        "NNVerify.C004.interval_hull_layernorm",
        "NNVerify.C004.jacobian_dense",
        "NNVerify.C004.crown_backward_eq_interval_hull",
        "NNVerify.C004.interval_hull_eq_ibp_forward",
        "NNVerify.C004.crown_equals_ibp_chain",
        "NNVerify.C004.crown_equals_ibp",
    ];
    let mut axiom_count = 0;
    let mut def_count = 0;
    let mut thm_count = 0;
    for name in &c004_names {
        let decl = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist"));
        if decl.value.is_some() {
            if decl.is_reducible {
                def_count += 1;
            } else {
                thm_count += 1;
            }
        } else {
            axiom_count += 1;
        }
    }
    assert_eq!(
        axiom_count, 0,
        "expected 0 domain axioms after retiring Step 1, Step 2, and jacobian_dense",
    );
    assert_eq!(
        axiom_count + def_count + thm_count,
        c004_names.len(),
        "all declarations accounted for",
    );
}

// =============================================================================
// Step lemma type checking
// =============================================================================

#[test]
fn test_step1_type_checks() {
    let env = make_env();
    let step1 = Expr::const_(
        Name::from_string("NNVerify.C004.crown_backward_eq_interval_hull"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&step1)
        .expect("infer crown_backward_eq_interval_hull type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "Step 1 theorem should have Pi type (universally quantified)",
    );
}

#[test]
fn test_step2_type_checks() {
    let env = make_env();
    let step2 = Expr::const_(
        Name::from_string("NNVerify.C004.interval_hull_eq_ibp_forward"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&step2)
        .expect("infer interval_hull_eq_ibp_forward type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "Step 2 theorem should have Pi type (universally quantified)",
    );
}

// =============================================================================
// MASQUERADE retirement: C004 Step 1 and Step 2 are now hypothesis-wrapped
// over local equality evidence.
// =============================================================================

#[test]
fn test_step2_core_axiom_removed() {
    let env = make_env();
    // The old `_core` axiom for Step 2 was eliminated in an earlier round
    // and has not been reintroduced. The public theorem itself is named
    // `interval_hull_eq_ibp_forward`, not a `_core` helper.
    assert!(
        env.get_const(&Name::from_string(
            "NNVerify.C004.interval_hull_eq_ibp_forward_core"
        ))
        .is_none(),
        "interval_hull_eq_ibp_forward_core should NOT exist",
    );
}

// Proof quality (#integrity-audit 2026-06): Step 1, Step 2, the chain, and
// headline are honest hypothesis-wrapped theorems whose proof terms use local
// equality hypotheses and do NOT reference the old C004 axiom constants
// (`True.rec` / `jacobian_dense` / `_core`). They are NOT, however,
// `ProofQuality::Constructive`: their TYPES name the `IBP.forward_layernorm` /
// `CROWN.backward_layernorm` / `interval_hull_layernorm` carriers, whose
// Definition bodies discharge the `IntervalBounds` validity field via the
// admitted ordered-field axioms `Rat.le_refl` (zero-bounds base case) and
// `Rat.add_le_add_left` (β-shift step case). Those two axioms were dishonestly
// whitelisted as "foundational"; they are now admitted DOMAIN axioms
// (`ADMITTED_DOMAIN_AXIOMS`), so the honest classification of each C004
// theorem is `AxiomDependent` resting ONLY on admitted domain axioms — no
// `sorry`, no rogue/unexpected axiom. The hypothesis-wrapped form previously
// masqueraded this domain dependence as a constructive proof; these tests now
// pin the honest state.

/// WS-A ATOMIC LIVE SWITCH: assert `name`'s transitive axiom closure is now
/// EMPTY and the theorem is `Constructive`. The C004 carriers' `IntervalBounds`
/// validity fields formerly discharged via the admitted ordered-field axioms
/// `Rat.le_refl` (base case) and `Rat.add_le_add_left` (β-shift step), BOTH of
/// which are now genuine `Constructive` quotient Theorems — so the full closure
/// of every C004 theorem is free of admitted domain axioms.
fn assert_c004_now_constructive(env: &Environment, name: &Name) {
    use crate::env::axiom_audit::ProofQuality;
    let deps = env
        .axiom_deps(name)
        .unwrap_or_else(|| panic!("{name} should exist"));
    let dep_names: Vec<String> = deps.iter().map(|a| a.to_string()).collect();
    assert!(
        deps.is_empty(),
        "{name} closure must now be EMPTY (its former Rat ordered-field deps are \
         quotient Theorems), got {dep_names:?}",
    );
    let quality = env
        .proof_quality(name)
        .unwrap_or_else(|| panic!("{name} proof_quality"));
    assert!(
        matches!(quality, ProofQuality::Constructive),
        "{name} must now be Constructive, got {quality:?}",
    );
}

#[test]
fn test_c004_crown_equals_ibp_is_axiom_dependent_hypothesis_wrapped_theorem() {
    // WS-A: the C004 headline is now Constructive (its Rat ordered-field carrier
    // dependence — Rat.le_refl / Rat.add_le_add_left — is now constructive).
    let env = make_env();
    let name = Name::from_string("NNVerify.C004.crown_equals_ibp");
    assert_c004_now_constructive(&env, &name);
}

#[test]
fn test_c004_step1_is_axiom_dependent_hypothesis_wrapped_theorem() {
    // WS-A: Step 1 is now Constructive.
    let env = make_env();
    let name = Name::from_string("NNVerify.C004.crown_backward_eq_interval_hull");
    assert_c004_now_constructive(&env, &name);
}

#[test]
fn test_c004_step2_is_axiom_dependent_hypothesis_wrapped_theorem() {
    // WS-A: Step 2 is now Constructive.
    let env = make_env();
    let name = Name::from_string("NNVerify.C004.interval_hull_eq_ibp_forward");
    assert_c004_now_constructive(&env, &name);
}

#[test]
fn test_c004_chain_is_axiom_dependent_hypothesis_wrapped_theorem() {
    // WS-A: the chain is now Constructive.
    let env = make_env();
    let name = Name::from_string("NNVerify.C004.crown_equals_ibp_chain");
    assert_c004_now_constructive(&env, &name);
}

#[test]
fn test_c004_has_no_domain_axioms_in_soundness_report() {
    let env = make_env();
    let report = env.soundness_report();
    // After the 2026-04-27 Step 1 / Step 2 / chain / headline and
    // jacobian_dense retirements, C004 has no domain-specific axioms.
    let c004_domain_axioms: Vec<String> = report
        .domain_axioms
        .iter()
        .filter_map(|n| {
            let s = n.to_string();
            if s.contains("C004") {
                Some(s)
            } else {
                None
            }
        })
        .collect();
    assert!(
        c004_domain_axioms.is_empty(),
        "C004 should have no domain axioms after Step 2 retirement; got: {c004_domain_axioms:?}",
    );
    assert!(
        !c004_domain_axioms
            .iter()
            .any(|a| a == "NNVerify.C004.crown_backward_eq_interval_hull"),
        "Step 1 theorem should not appear in C004 domain axioms; got: {c004_domain_axioms:?}",
    );
    assert!(
        !c004_domain_axioms
            .iter()
            .any(|a| a == "NNVerify.C004.jacobian_dense"),
        "jacobian_dense Definition should not appear in C004 domain axioms; got: {c004_domain_axioms:?}",
    );
    assert!(
        !c004_domain_axioms
            .iter()
            .any(|a| a == "NNVerify.C004.crown_equals_ibp"),
        "headline theorem should not appear in C004 domain axioms; got: {c004_domain_axioms:?}",
    );
    assert!(
        !c004_domain_axioms
            .iter()
            .any(|a| a == "NNVerify.C004.crown_equals_ibp_chain"),
        "chain theorem should not appear in C004 domain axioms; got: {c004_domain_axioms:?}",
    );
}

#[test]
fn test_c004_crown_backward_is_definition_not_opaque() {
    let env = make_env();
    let decl = env
        .get_const(&Name::from_string("NNVerify.CROWN.backward_layernorm"))
        .expect("CROWN.backward_layernorm should exist");
    assert!(
        decl.value.is_some(),
        "CROWN.backward_layernorm should have a value (Definition, not Axiom)",
    );
    assert!(
        decl.is_reducible,
        "CROWN.backward_layernorm should be reducible (Definition, not Opaque)",
    );
}

// =============================================================================
// #3583 Branch A demasquerade + 2026-04-27 hypothesis-wrapped retirements.
//
// After the Branch A demote of Step 2 (#3460 -> Axiom) and its later
// hypothesis-wrapped retirement, the compound M1+M2 masquerade that let
// the old claims type-check as Theorems is closed by:
//   (1) requiring an explicit local Step 2 equality witness;
//   (2) defining `jacobian_dense` as a non-`True` predicate, so the
//       `jacobian_dense n gamma sigma z -> True` delta-reduction path is
//       still unavailable for any future `True.rec`-over-density proof.
// The tests below guard that state:
//   (a) Step 2 is a Theorem on the honest 6-binder hypothesis-wrapped
//       type, not the #3460 8-binder density-guarded type.
//   (b) jacobian_dense is a Definition whose value mentions `And`, `Ne`,
//       and `Rat.zero`, not a reducible Definition with body `True` and
//       not an Opaque with a `True` placeholder body.
//   (c) Step 2's type is NOT `Prop`-head (= `True`); the only way
//       theorem could degenerate is if its type were an unconditional
//       `True` (mere-proposition masquerade).
//   (d) No C004 declaration's closure references `True.rec` or
//       `jacobian_dense` — the masquerade mechanics are fully retired.
// =============================================================================

/// (a) 2026-04-27: Step 2 is an honest hypothesis-wrapped theorem.
/// The previous #3460 density-guarded Theorem had 8 Pi binders
/// (n, γ, β, σ, z, ε, B, h_density). After retirement, the type must
/// have exactly 6 Pi binders (n, γ, β, ε, B, h_step2) and no
/// jacobian_dense hypothesis in any domain.
#[test]
fn test_c004_interval_hull_eq_ibp_forward_is_hypothesis_wrapped_theorem() {
    let env = make_env();
    let decl = env
        .get_const(&Name::from_string(
            "NNVerify.C004.interval_hull_eq_ibp_forward",
        ))
        .expect("interval_hull_eq_ibp_forward should exist");
    assert_eq!(
        decl.kind,
        ConstantKind::Theorem,
        "Step 2 should be a hypothesis-wrapped theorem after the 2026-04-27 retirement",
    );
    assert!(
        decl.value.is_some(),
        "Step 2 theorem must carry the local-hypothesis proof term",
    );
    // Walk the type; must have exactly 6 Pi binders and no jacobian_dense
    // hypothesis in any domain.
    let mut cur = decl.type_.clone();
    let mut pi_count = 0usize;
    let mut saw_dense = false;
    while let ExprKind::Pi(_, dom, body) = cur.kind() {
        pi_count += 1;
        if format!("{:?}", dom).contains("jacobian_dense") {
            saw_dense = true;
        }
        cur = (**body).clone();
    }
    assert_eq!(
        pi_count, 6,
        "Step 2 theorem type should have 6 Pi binders (n, γ, β, ε, B, h_step2); got {pi_count}. \
         A regression to 8 binders would indicate the #3460 density-guarded shape returned.",
    );
    assert!(
        !saw_dense,
        "#3583 Branch A: no Pi binder in Step 2's type should mention jacobian_dense. \
         The density hypothesis only belonged in the #3460 masquerade; its presence here \
         means the demote did not land.",
    );
}

/// (b) 2026-04-27 predicate retirement: jacobian_dense is a reducible
/// `Declaration::Definition` with a non-`True` body, NOT the old
/// argument-discarding True carrier and NOT the intermediate Opaque/Axiom
/// placeholder states.
#[test]
fn test_c004_jacobian_dense_is_non_true_definition() {
    let env = make_env();
    let decl = env
        .get_const(&Name::from_string("NNVerify.C004.jacobian_dense"))
        .expect("jacobian_dense should exist");
    assert_eq!(
        decl.kind,
        ConstantKind::Definition,
        "jacobian_dense should be a Definition after the 2026-04-27 predicate retirement",
    );
    assert!(
        decl.value.is_some(),
        "jacobian_dense Definition must carry a value",
    );
    assert!(
        decl.is_reducible,
        "jacobian_dense should be reducible so the real nonzero predicate can unfold",
    );
    let value = decl.value.as_ref().expect("jacobian_dense value");
    assert!(
        expr_mentions_const(value, "And") && expr_mentions_const(value, "Ne"),
        "jacobian_dense body should be a nonzero conjunction, got: {value:?}",
    );
    assert!(
        !expr_mentions_const(value, "True"),
        "jacobian_dense body must not be the old True placeholder",
    );
}

/// (c) Step 2's type must NOT reduce to `True` or any mere-proposition
/// masquerade. A theorem whose type is `True` would be a trivial theorem
/// contributing no content beyond `True.intro`. The honest Step 2 type is
/// a 6-binder Pi ending in an `Eq` application.
#[test]
fn test_c004_interval_hull_eq_ibp_forward_type_is_not_true_prop() {
    let env = make_env();
    let decl = env
        .get_const(&Name::from_string(
            "NNVerify.C004.interval_hull_eq_ibp_forward",
        ))
        .expect("interval_hull_eq_ibp_forward should exist");
    // Walk past all Pi binders.
    let mut cur = decl.type_.clone();
    while let ExprKind::Pi(_, _, body) = cur.kind() {
        cur = (**body).clone();
    }
    // Final body: must NOT be Const("True") nor Const("NNVerify.C004.jacobian_dense").
    // It must be an Eq application (ExprKind::App head chain ending in Eq).
    match cur.kind() {
        ExprKind::Const(name, _) => {
            let s = name.to_string();
            assert_ne!(
                s, "True",
                "#3583 Branch A: Step 2 type must not reduce to bare True (mere-proposition masquerade)",
            );
            assert_ne!(
                s, "NNVerify.C004.jacobian_dense",
                "#3583 Branch A: Step 2 type must not reduce to jacobian_dense (True-carrier masquerade)",
            );
            panic!("#3583 Branch A: Step 2 type body should be an Eq application, got Const({s})");
        }
        ExprKind::App(..) => { /* expected: Eq application */ }
        other => {
            panic!("#3583 Branch A: Step 2 type body must be an Eq application; got {other:?}")
        }
    }
}

/// (d) Step 2's hypothesis-wrapped proof should not reference `True.rec`
/// or `NNVerify.C004.jacobian_dense`. The density-guarded masquerade is
/// fully retired.
#[test]
fn test_c004_interval_hull_eq_ibp_forward_no_true_rec_in_closure() {
    let env = make_env();
    let c004_names = ["NNVerify.C004.interval_hull_eq_ibp_forward"];
    // Guard against a regression to the old `True.rec`-over-`jacobian_dense`
    // term.
    fn references_masquerade_constants(expr: &Expr) -> bool {
        match expr.kind() {
            ExprKind::Const(name, _) => {
                let s = name.to_string();
                s == "True.rec" || s == "NNVerify.C004.jacobian_dense"
            }
            ExprKind::App(f, a) => {
                references_masquerade_constants(f) || references_masquerade_constants(a)
            }
            ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                references_masquerade_constants(t) || references_masquerade_constants(b)
            }
            ExprKind::Let(_, t, v, b, _) => {
                references_masquerade_constants(t)
                    || references_masquerade_constants(v)
                    || references_masquerade_constants(b)
            }
            ExprKind::MData(_, e) => references_masquerade_constants(e),
            ExprKind::Proj(_, _, e) => references_masquerade_constants(e),
            _ => false,
        }
    }
    for name in &c004_names {
        let decl = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist"));
        let value = decl
            .value
            .as_ref()
            .unwrap_or_else(|| panic!("{name} should be a theorem with a proof value"));
        assert!(
            !references_masquerade_constants(value),
            "{name}'s proof must not reference True.rec or jacobian_dense",
        );
        // Also check the type — Branch A should never place jacobian_dense
        // in a type signature.
        assert!(
            !references_masquerade_constants(&decl.type_),
            "#3583 Branch A: {name}'s type must not reference True.rec or jacobian_dense. \
             A reference means the density-guarded shape has returned.",
        );
    }
}
