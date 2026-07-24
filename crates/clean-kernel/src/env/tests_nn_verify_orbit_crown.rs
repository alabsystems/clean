// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Orbit-CROWN symmetry quotienting theorems (C030).

use crate::env::{ConstantKind, Environment};
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_orbit_crown()
        .expect("init_nn_verify_orbit_crown");
    env
}

#[test]
fn test_symmetry_group_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.OrbitCROWN.SymmetryGroup"))
            .is_some(),
        "NNVerify.OrbitCROWN.SymmetryGroup should be registered",
    );
}

#[test]
fn test_group_action_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.OrbitCROWN.GroupAction"))
            .is_some(),
        "NNVerify.OrbitCROWN.GroupAction should be registered",
    );
}

#[test]
fn test_equivariant_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.OrbitCROWN.Equivariant"))
            .is_some(),
        "NNVerify.OrbitCROWN.Equivariant should be registered",
    );
}

#[test]
fn test_quotient_space_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.OrbitCROWN.QuotientSpace"))
            .is_some(),
        "NNVerify.OrbitCROWN.QuotientSpace should be registered",
    );
}

#[test]
fn test_orbit_bound_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.OrbitCROWN.OrbitBound"))
            .is_some(),
        "NNVerify.OrbitCROWN.OrbitBound should be registered",
    );
}

#[test]
fn test_group_order_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.OrbitCROWN.GroupOrder"))
            .is_some(),
        "NNVerify.OrbitCROWN.GroupOrder should be registered",
    );
}

#[test]
fn test_quotient_project_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.OrbitCROWN.quotient_project"))
            .is_some(),
        "NNVerify.OrbitCROWN.quotient_project should be registered",
    );
}

#[test]
fn test_crown_on_quotient_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.OrbitCROWN.crown_on_quotient"))
            .is_some(),
        "NNVerify.OrbitCROWN.crown_on_quotient should be registered",
    );
}

#[test]
fn test_crown_on_full_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.OrbitCROWN.crown_on_full"))
            .is_some(),
        "NNVerify.OrbitCROWN.crown_on_full should be registered",
    );
}

#[test]
fn test_c030a_equivariant_factors_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string(
            "NNVerify.OrbitCROWN.C030a_equivariant_factors"
        ))
        .is_some(),
        "C030a: NNVerify.OrbitCROWN.C030a_equivariant_factors should be registered",
    );
}

#[test]
fn test_c030b_quotient_crown_sound_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string(
            "NNVerify.OrbitCROWN.C030b_quotient_crown_sound"
        ))
        .is_some(),
        "C030b: NNVerify.OrbitCROWN.C030b_quotient_crown_sound should be registered",
    );
}

#[test]
fn test_c030c_verification_speedup_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string(
            "NNVerify.OrbitCROWN.C030c_verification_speedup"
        ))
        .is_some(),
        "C030c: NNVerify.OrbitCROWN.C030c_verification_speedup should be registered",
    );
}

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_orbit_crown().expect("first init");
    env.init_nn_verify_orbit_crown()
        .expect("second init should be idempotent");
}

#[test]
fn test_naming_convention() {
    let env = make_env();
    let names = [
        "NNVerify.OrbitCROWN.SymmetryGroup",
        "NNVerify.OrbitCROWN.GroupAction",
        "NNVerify.OrbitCROWN.Equivariant",
        "NNVerify.OrbitCROWN.QuotientSpace",
        "NNVerify.OrbitCROWN.OrbitBound",
        "NNVerify.OrbitCROWN.GroupOrder",
        "NNVerify.OrbitCROWN.quotient_project",
        "NNVerify.OrbitCROWN.crown_on_quotient",
        "NNVerify.OrbitCROWN.crown_on_full",
        "NNVerify.OrbitCROWN.C030a_equivariant_factors",
        "NNVerify.OrbitCROWN.C030b_quotient_crown_sound",
        "NNVerify.OrbitCROWN.C030c_verification_speedup",
    ];
    for name in &names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{} should be registered",
            name,
        );
        assert!(
            name.starts_with("NNVerify."),
            "all names must start with NNVerify. prefix: {}",
            name,
        );
    }
}

#[test]
fn test_symmetry_group_type_checks() {
    let env = make_env();
    let sg = Expr::const_(
        Name::from_string("NNVerify.OrbitCROWN.SymmetryGroup"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&sg).expect("infer SymmetryGroup type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "SymmetryGroup should have Pi type (Nat -> Type)",
    );
}

#[test]
fn test_equivariant_type_checks() {
    let env = make_env();
    let eq = Expr::const_(Name::from_string("NNVerify.OrbitCROWN.Equivariant"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&eq).expect("infer Equivariant type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "Equivariant should have Pi type (universally quantified)",
    );
}

#[test]
fn test_c030a_type_checks() {
    let env = make_env();
    let thm = Expr::const_(
        Name::from_string("NNVerify.OrbitCROWN.C030a_equivariant_factors"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("infer C030a_equivariant_factors type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "C030a should have Pi type (universally quantified)",
    );
}

#[test]
fn test_c030b_type_checks() {
    let env = make_env();
    let thm = Expr::const_(
        Name::from_string("NNVerify.OrbitCROWN.C030b_quotient_crown_sound"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("infer C030b_quotient_crown_sound type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "C030b should have Pi type (universally quantified)",
    );
}

#[test]
fn test_c030c_type_checks() {
    let env = make_env();
    let thm = Expr::const_(
        Name::from_string("NNVerify.OrbitCROWN.C030c_verification_speedup"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("infer C030c_verification_speedup type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "C030c should have Pi type (universally quantified)",
    );
}

#[test]
fn test_c030a_is_opaque_not_axiom() {
    let env = make_env();
    let name = Name::from_string("NNVerify.OrbitCROWN.C030a_equivariant_factors");
    let info = env.get_const(&name).expect("C030a should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Opaque,
        "C030a should be Opaque (not Axiom) after sorry-based inhabitation",
    );
}

#[test]
fn test_c030b_is_opaque_not_axiom() {
    let env = make_env();
    let name = Name::from_string("NNVerify.OrbitCROWN.C030b_quotient_crown_sound");
    let info = env.get_const(&name).expect("C030b should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Opaque,
        "C030b should be Opaque (not Axiom) after sorry-based inhabitation",
    );
}

#[test]
fn test_c030c_verification_speedup_is_hypothesis_wrapped_theorem() {
    // 2026-04-27: C030c retires the remaining C030 domain axiom by
    // strengthening the type with an explicit local orbit-bound hypothesis
    // and returning that hypothesis. The old Nat.le_refl-over-OrbitBound
    // proof is not restored.
    let env = make_env();
    let name = Name::from_string("NNVerify.OrbitCROWN.C030c_verification_speedup");
    let info = env.get_const(&name).expect("C030c should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "C030c should be a hypothesis-wrapped Theorem after axiom retirement. \
         Got {:?}",
        info.kind,
    );
    assert!(
        info.value.is_some(),
        "C030c hypothesis-wrapped Theorem should carry a proof value",
    );
}

#[test]
fn test_c030c_axiom_backing_opaque_removed_by_3589() {
    // #3589 Branch A: the backing `C030c_verification_speedup_axiom`
    // Opaque (introduced in #3468 alongside the headline Theorem) is
    // removed because no downstream production code referenced it and
    // it duplicated the demoted proof value.
    let env = make_env();
    let name = Name::from_string("NNVerify.OrbitCROWN.C030c_verification_speedup_axiom");
    assert!(
        env.get_const(&name).is_none(),
        "C030c_verification_speedup_axiom should NOT be registered after #3589 removal",
    );
}

#[test]
fn test_c030_has_no_domain_axioms_after_c030c_hypothesis_wrapping() {
    // The remaining C030 domain axiom was retired by exposing the missing
    // orbit-bound proof as a local hypothesis of C030c.
    let env = make_env();
    let report = env.soundness_report();
    let c030_axioms: Vec<String> = report
        .domain_axioms
        .iter()
        .filter(|n| n.to_string().starts_with("NNVerify.OrbitCROWN."))
        .map(|n| n.to_string())
        .collect();
    assert_eq!(
        c030_axioms,
        Vec::<String>::new(),
        "C030 should have no domain axioms after C030c hypothesis wrapping",
    );
}

#[test]
fn test_c030_verify_conjecture_hypothesis_wrapped_after_c030c_hypothesis_wrapping() {
    // #3700 INTEGRITY FIX: retiring the C030c domain axiom by exposing it as a
    // local hypothesis makes the C030 headline theorem a `fun … h => h`
    // projection (empty axiom closure, proves only `H -> H`). The honest gamma-
    // crown verdict is therefore HYPOTHESIS-WRAPPED, NOT constructive — the
    // previous "constructive" assertion was the overstatement #3700 corrects.
    use crate::env::gamma_crown_verify::verify_conjecture;
    let result = verify_conjecture("C030");
    assert!(result.init_ok, "C030 init should succeed");
    assert!(result.tc_verified, "C030 should be type-checked");
    assert!(
        !result.constructive,
        "C030 headline theorem is an H->H projection, not a genuine proof",
    );
    assert_eq!(result.proof_mechanism, "hypothesis_wrapped");
    assert_eq!(result.status, "VERIFIED_HYPOTHESIS_WRAPPED");
    assert_eq!(
        result.domain_axioms, 0,
        "C030 should have no C030-prefix (namespace) domain axioms",
    );
}

// =============================================================================
// C030c hypothesis-wrapped proof (no sorry_inhabit_pi)
// =============================================================================

/// Walk through nested `ExprKind::Lam` binders, returning the body under
/// the innermost lambda plus the binder count.
fn strip_lam_spine(e: &Expr) -> (&Expr, usize) {
    let mut cursor = e;
    let mut binder_count = 0usize;
    while let ExprKind::Lam(_, _, body) = cursor.kind() {
        binder_count += 1;
        cursor = body;
    }
    (cursor, binder_count)
}

fn count_pi_binders(e: &Expr) -> usize {
    let mut cursor = e;
    let mut binder_count = 0usize;
    while let ExprKind::Pi(_, _, body) = cursor.kind() {
        binder_count += 1;
        cursor = body;
    }
    binder_count
}

/// Guard test for the 2026-04-27 C030c retirement: the theorem is explicitly
/// hypothesis-wrapped as `forall d_in G, H -> H`.
#[test]
fn test_c030c_verification_speedup_hypothesis_wrapped_type_checks() {
    let env = make_env();

    let info = env
        .get_const(&Name::from_string(
            "NNVerify.OrbitCROWN.C030c_verification_speedup",
        ))
        .expect("C030c should be registered");

    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "C030c should be a hypothesis-wrapped Theorem, got {:?}",
        info.kind,
    );
    assert!(
        info.value.is_some(),
        "C030c theorem must carry the local-hypothesis proof value",
    );
    assert_eq!(
        count_pi_binders(&info.type_),
        3,
        "C030c type should bind d_in, G, and the local orbit-bound hypothesis",
    );

    let axm = Expr::const_(
        Name::from_string("NNVerify.OrbitCROWN.C030c_verification_speedup"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&axm)
        .expect("C030c theorem reference should infer a type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "C030c theorem type should be Pi, got {:?}",
        ty.kind(),
    );
}

#[test]
fn test_c030c_verification_speedup_proof_returns_local_hypothesis() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string(
            "NNVerify.OrbitCROWN.C030c_verification_speedup",
        ))
        .expect("C030c should be registered");
    let value = info
        .value
        .as_ref()
        .expect("hypothesis-wrapped theorem should carry a proof value");
    let (body, binder_count) = strip_lam_spine(value);
    assert_eq!(
        binder_count, 3,
        "C030c proof should bind d_in, G, and the local hypothesis",
    );
    assert!(
        matches!(body.kind(), ExprKind::BVar(_)),
        "C030c proof should return the innermost local hypothesis, got {body:?}",
    );
}

/// Verifies the C030 `sorry_inhabit_pi` site count.
///
/// - Before #3468: 3 sites (C030a, C030b, C030c).
/// - After #3468: 2 sites (C030c promoted to constructive Theorem).
/// - After #3589 Branch A: 2 sites (C030a, C030b). C030c became an Axiom
///   with no value, so it could not be sorry-inhabited.
/// - After 2026-04-27: still 2 sites. C030c is now a hypothesis-wrapped
///   Theorem whose proof returns a local hypothesis.
///
/// The test walks each remaining conjecture Opaque's value. A sorry-
/// inhabited value has the shape `fun .. .. => <synthetic sorry>` — a
/// nested lambda whose innermost body is the canonical synthetic sorry term.
#[test]
fn test_c030_sorry_inhabit_pi_site_count_after_c030c_hypothesis_wrapping() {
    let env = make_env();

    fn innermost_body_is_synthetic_sorry(env_value: &Expr) -> bool {
        let mut cursor = env_value;
        while let ExprKind::Lam(_, _, body) = cursor.kind() {
            cursor = body;
        }
        cursor.is_synthetic_sorry()
    }

    // C030c: hypothesis-wrapped theorem with a real local-hypothesis proof,
    // not sorry-inhabited. The backing `_axiom` Opaque remains removed.
    let c030c_info = env
        .get_const(&Name::from_string(
            "NNVerify.OrbitCROWN.C030c_verification_speedup",
        ))
        .expect("C030c should be registered");
    assert!(
        c030c_info.value.is_some(),
        "C030c should carry the local-hypothesis proof value",
    );
    assert!(
        env.get_const(&Name::from_string(
            "NNVerify.OrbitCROWN.C030c_verification_speedup_axiom",
        ))
        .is_none(),
        "Backing _axiom Opaque should be removed by #3589",
    );

    // C030a and C030b: STILL sorry-inhabited (not remediated).
    let c030a_value = env
        .get_const(&Name::from_string(
            "NNVerify.OrbitCROWN.C030a_equivariant_factors",
        ))
        .and_then(|ci| ci.value.clone())
        .expect("C030a should have a value");
    assert!(
        innermost_body_is_synthetic_sorry(&c030a_value),
        "C030a_equivariant_factors should still be sorry-inhabited",
    );

    let c030b_value = env
        .get_const(&Name::from_string(
            "NNVerify.OrbitCROWN.C030b_quotient_crown_sound",
        ))
        .and_then(|ci| ci.value.clone())
        .expect("C030b should have a value");
    assert!(
        innermost_body_is_synthetic_sorry(&c030b_value),
        "C030b_quotient_crown_sound should still be sorry-inhabited",
    );
}

/// Guard test for #3589 Branch A: `OrbitBound` is `Opaque` and NOT
/// reducible, closing the δ-reduction loophole that permitted the
/// `Nat.le_refl` masquerade proof of C030c.
///
/// The body `fun d_in _ => d_in` is preserved — the semantic claim is
/// unchanged — but the kernel no longer δ-unfolds through it, so the
/// prior Theorem proof (`fun d_in g => Nat.le_refl d_in`) no longer
/// type-checks. See #3589 and
/// `reports/audit/2026-04-20-r8-wave6-masquerade-sweep.md`.
///
/// History:
/// - #3468: body `fun _ _ => Nat.zero`, reducible Definition (vacuous).
/// - #3550: body `fun d_in _ => d_in`, reducible Definition (substantive
///   body, but masquerade persisted via δ-reduction).
/// - #3589 (this change): Opaque, body unchanged. Masquerade closed.
#[test]
fn test_orbit_bound_is_opaque_not_reducible_definition() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.OrbitCROWN.OrbitBound"))
        .expect("OrbitBound should be registered");

    // (1) Kind is Opaque (not Definition) after #3589.
    assert_eq!(
        info.kind,
        ConstantKind::Opaque,
        "OrbitBound should be Opaque (not Definition) after #3589 demasquerade. \
         Got {:?}",
        info.kind,
    );

    // (2) Not reducible — kernel must not δ-unfold through it.
    assert!(
        !info.is_reducible,
        "OrbitBound must NOT be reducible after #3589 — that was the \
         δ-reduction loophole enabling the C030c Nat.le_refl masquerade",
    );

    // (3) Body preserved: `fun d_in g => d_in` (2-binder lambda, innermost
    // body is a BVar pointing at the outer `d_in` binder). The semantic
    // claim is unchanged; only the reducibility was demoted.
    let value = info
        .value
        .as_ref()
        .expect("OrbitBound Opaque should carry a value");
    let (body, binder_count) = strip_lam_spine(value);
    assert_eq!(
        binder_count, 2,
        "OrbitBound body should be a 2-binder lambda, got {binder_count}",
    );
    match body.kind() {
        ExprKind::BVar(_) => { /* expected: bound variable referring to d_in */ }
        ExprKind::Const(name, _) => {
            assert_ne!(
                name.to_string(),
                "Nat.zero",
                "OrbitBound innermost body must NOT be Nat.zero — that was the vacuous #3468 carrier"
            );
            panic!("OrbitBound innermost body should be a BVar (bound d_in), got Const({name})");
        }
        other => panic!("OrbitBound innermost body should be a BVar (bound d_in), got {other:?}"),
    }
}

// =============================================================================
// #3564: C030d sharp orbit-stabilizer bound (honest Opaque, sorry-inhabited)
// =============================================================================

/// Checks whether an expression's innermost body is the synthetic sorry
/// trust marker — the canonical shape produced by `sorry_inhabit_pi`.
fn innermost_body_is_synthetic_sorry(value: &Expr) -> bool {
    let (body, _) = strip_lam_spine(value);
    body.is_synthetic_sorry()
}

/// Guard test for #3564: verifies
/// `NNVerify.OrbitCROWN.C030d_orbit_stabilizer_sharp` is kernel-registered
/// as the honest sharp-bound claim.
///
/// Keys pinned:
/// 1. Declaration kind is `Opaque` (not `Axiom`, not `Theorem`).
///    - Axiom would increase C030's domain-axiom count from 0 — ratchet violation.
///    - Theorem would masquerade the unproved claim — #3468 regression risk.
///    - Opaque is the correct honest carrier per the C030a / C030b pattern.
/// 2. Type is a Pi (universally quantified over `d_in` and `G`).
/// 3. Value is sorry-inhabited (matches `sorry_inhabit_pi` shape).
/// 4. Type contains `Nat.mul`, `NNVerify.OrbitCROWN.OrbitBound`, AND
///    `NNVerify.OrbitCROWN.GroupOrder` as subterms — this is the
///    multiplicative sharp bound `|Orbit| * |G| <= d_in`, NOT a
///    degenerate loose bound.
#[test]
fn test_c030d_sharp_bound_registered_as_honest_opaque() {
    let env = make_env();
    let name = Name::from_string("NNVerify.OrbitCROWN.C030d_orbit_stabilizer_sharp");
    let info = env
        .get_const(&name)
        .expect("C030d_orbit_stabilizer_sharp should be registered after #3564");

    // (1) Opaque kind.
    assert_eq!(
        info.kind,
        ConstantKind::Opaque,
        "C030d should be Opaque (honest sorry-inhabited claim), got {:?}. \
         Axiom would break the 0-domain-axiom ratchet; \
         Theorem would masquerade an unproved claim.",
        info.kind,
    );

    // (2) Type is Pi.
    assert!(
        matches!(info.type_.kind(), ExprKind::Pi(..)),
        "C030d type should be Pi (forall d_in G, ...), got {:?}",
        info.type_.kind(),
    );

    // (3) Sorry-inhabited value.
    let value = info
        .value
        .as_ref()
        .expect("C030d Opaque should carry a value");
    assert!(
        innermost_body_is_synthetic_sorry(value),
        "C030d value should be sorry_inhabit_pi shape; got {value:?}",
    );

    // (4) Type references Nat.mul, OrbitBound, and GroupOrder — pinning
    //     the multiplicative sharp form `|Orbit| * |G| <= d_in`.
    //
    //     Walk the type expression and collect every `Const` name. The
    //     required set must all appear, distinguishing this statement
    //     from the C030c loose bound (no `Nat.mul`, no `GroupOrder`).
    fn collect_const_names(e: &Expr, out: &mut std::collections::HashSet<String>) {
        match e.kind() {
            ExprKind::Const(name, _) => {
                out.insert(name.to_string());
            }
            ExprKind::App(f, a) => {
                collect_const_names(f, out);
                collect_const_names(a, out);
            }
            ExprKind::Pi(_, dom, body) | ExprKind::Lam(_, dom, body) => {
                collect_const_names(dom, out);
                collect_const_names(body, out);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                collect_const_names(ty, out);
                collect_const_names(val, out);
                collect_const_names(body, out);
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => {
                collect_const_names(inner, out);
            }
            _ => {}
        }
    }
    let mut names: std::collections::HashSet<String> = std::collections::HashSet::new();
    collect_const_names(&info.type_, &mut names);
    assert!(
        names.contains("Nat.mul"),
        "C030d type should reference Nat.mul (sharp multiplicative form). \
         Consts found: {names:?}"
    );
    assert!(
        names.contains("NNVerify.OrbitCROWN.OrbitBound"),
        "C030d type should reference OrbitBound. Consts found: {names:?}"
    );
    assert!(
        names.contains("NNVerify.OrbitCROWN.GroupOrder"),
        "C030d type should reference GroupOrder (sharp form carries |G|). \
         Consts found: {names:?}"
    );
}

/// Verifies the C030d Opaque type-checks through the full kernel
/// `add_decl` pipeline (via `init_nn_verify_orbit_crown` on a fresh
/// Environment) AND that its type infers to a Sort.
#[test]
fn test_c030d_kernel_validates_via_add_decl() {
    let env = make_env();
    let thm = Expr::const_(
        Name::from_string("NNVerify.OrbitCROWN.C030d_orbit_stabilizer_sharp"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("C030d should infer a type via kernel type-checking");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "C030d inferred type should be Pi, got {:?}",
        ty.kind(),
    );
}

/// Verifies C030c and C030d coexist with their current shapes:
/// - C030c: hypothesis-wrapped `Declaration::Theorem`.
/// - C030d: `Declaration::Opaque` (sorry-inhabited sharp-bound claim from #3564).
#[test]
fn test_c030c_hypothesis_wrapped_theorem_and_c030d_opaque_coexist() {
    let env = make_env();
    let c030c = env
        .get_const(&Name::from_string(
            "NNVerify.OrbitCROWN.C030c_verification_speedup",
        ))
        .expect("C030c should still be registered");
    assert_eq!(
        c030c.kind,
        ConstantKind::Theorem,
        "C030c should be a hypothesis-wrapped Theorem. Got {:?}",
        c030c.kind,
    );
    assert!(
        c030c.value.is_some(),
        "C030c hypothesis-wrapped Theorem must carry a proof value",
    );
    // C030d is a distinct, sharp-bound Opaque (unchanged by #3589).
    let c030d = env
        .get_const(&Name::from_string(
            "NNVerify.OrbitCROWN.C030d_orbit_stabilizer_sharp",
        ))
        .expect("C030d should be registered after #3564");
    assert_eq!(
        c030d.kind,
        ConstantKind::Opaque,
        "C030d should be Opaque (honest sharp-bound claim), got {:?}",
        c030d.kind,
    );
    assert!(
        c030d.value.is_some(),
        "C030d Opaque should carry a (sorry-inhabited) value",
    );
}

/// Verifies that adding C030d does NOT introduce a C030 domain axiom. C030c
/// is now hypothesis-wrapped, so the C030 namespace has no domain axioms.
#[test]
fn test_c030d_does_not_add_domain_axioms() {
    let env = make_env();
    let report = env.soundness_report();
    let c030_axioms: Vec<String> = report
        .domain_axioms
        .iter()
        .filter(|n| n.to_string().starts_with("NNVerify.OrbitCROWN."))
        .map(|n| n.to_string())
        .collect();
    assert_eq!(
        c030_axioms,
        Vec::<String>::new(),
        "C030 should have no domain axioms after C030c hypothesis wrapping. \
         C030d must remain Opaque + sorry — never an Axiom.",
    );
}
