// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for C007: Streaming verification certificates for Branch-and-Bound.
//!
//! Verifies that the three novel kernel theorems C007a (compositionality),
//! C007b (incremental cost bound), and C007c (restrict soundness) are
//! correctly registered, type-check through the kernel TypeChecker, and
//! have the expected Declaration kinds.
//!
//! Post-#3568 / 2026-04-27 state:
//! - `cert_sound` is `Declaration::Opaque` (reverted from the #3461
//!   reducible Definition that enabled the `True.intro` masquerade).
//! - `merge_sound_helper` is a hypothesis-wrapped `Declaration::Theorem`.
//! - `restrict_refines_helper` and `incremental_cost_helper` remain
//!   `Declaration::Opaque` with `sorry_inhabit_pi` bodies (#3381),
//!   pending their own remediation slices.
//!
//! Part of #3312, #3150, #3568.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_streaming_certs()
        .expect("init_nn_verify_streaming_certs should succeed");
    env
}

fn assert_registered(env: &Environment, name: &str) {
    assert!(
        env.get_const(&Name::from_string(name)).is_some(),
        "{name} should be registered"
    );
}

fn assert_type_checks_as_pi(env: &Environment, name: &str) {
    let e = Expr::const_(Name::from_string(name), vec![]);
    let tc = TypeChecker::with_mode(env, env.mode());
    let ty = tc
        .infer_type(&e)
        .unwrap_or_else(|err| panic!("{name} should type-check, got: {err:?}"));
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "{name} type should be Pi, got {:?}",
        ty.kind()
    );
}

// ---------------------------------------------------------------
// Registration tests
// ---------------------------------------------------------------

#[test]
fn test_c007a_merge_compositionality_registered() {
    assert_registered(&make_env(), "NNVerify.C007.merge_compositionality");
}

#[test]
fn test_c007b_incremental_cost_bound_registered() {
    assert_registered(&make_env(), "NNVerify.C007.incremental_cost_bound");
}

#[test]
fn test_c007c_restrict_sound_registered() {
    assert_registered(&make_env(), "NNVerify.C007.restrict_sound");
}

#[test]
fn test_bab_cert_type_registered() {
    assert_registered(&make_env(), "NNVerify.C007.BaBCert");
}

#[test]
fn test_cert_sound_registered() {
    assert_registered(&make_env(), "NNVerify.C007.cert_sound");
}

#[test]
fn test_merge_cert_registered() {
    assert_registered(&make_env(), "NNVerify.C007.merge_cert");
}

#[test]
fn test_restrict_cert_registered() {
    assert_registered(&make_env(), "NNVerify.C007.restrict_cert");
}

#[test]
fn test_cert_cost_registered() {
    assert_registered(&make_env(), "NNVerify.C007.cert_cost");
}

#[test]
fn test_delta_cost_registered() {
    assert_registered(&make_env(), "NNVerify.C007.delta_cost");
}

#[test]
fn test_disjoint_cover_registered() {
    assert_registered(&make_env(), "NNVerify.C007.disjoint_cover");
}

// ---------------------------------------------------------------
// Helper axiom registration tests
// ---------------------------------------------------------------

#[test]
fn test_merge_sound_helper_registered() {
    assert_registered(&make_env(), "NNVerify.C007.merge_sound_helper");
}

#[test]
fn test_restrict_refines_helper_registered() {
    assert_registered(&make_env(), "NNVerify.C007.restrict_refines_helper");
}

#[test]
fn test_incremental_cost_helper_registered() {
    assert_registered(&make_env(), "NNVerify.C007.incremental_cost_helper");
}

// ---------------------------------------------------------------
// Type checking tests
// ---------------------------------------------------------------

#[test]
fn test_c007a_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.C007.merge_compositionality");
}

#[test]
fn test_c007b_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.C007.incremental_cost_bound");
}

#[test]
fn test_c007c_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.C007.restrict_sound");
}

#[test]
fn test_cert_sound_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.C007.cert_sound");
}

#[test]
fn test_merge_cert_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.C007.merge_cert");
}

#[test]
fn test_restrict_cert_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.C007.restrict_cert");
}

#[test]
fn test_cert_cost_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.C007.cert_cost");
}

#[test]
fn test_delta_cost_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.C007.delta_cost");
}

#[test]
fn test_disjoint_cover_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.C007.disjoint_cover");
}

#[test]
fn test_bab_cert_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("NNVerify.C007.BaBCert"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&e)
        .unwrap_or_else(|err| panic!("BaBCert should type-check, got: {err:?}"));
    // BaBCert : Nat -> Type, so its type is Pi
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "BaBCert type should be Pi (Nat -> Type), got {:?}",
        ty.kind()
    );
}

// ---------------------------------------------------------------
// Declaration kind tests — C007a/b/c are Theorems, helpers split by status
// ---------------------------------------------------------------

#[test]
fn test_c007a_is_theorem() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.C007.merge_compositionality"))
        .expect("C007a should exist");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "C007a should be Theorem (machine-checked proof), got {:?}",
        info.kind
    );
}

#[test]
fn test_c007b_is_theorem() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.C007.incremental_cost_bound"))
        .expect("C007b should exist");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "C007b should be Theorem (machine-checked proof), got {:?}",
        info.kind
    );
}

#[test]
fn test_c007c_is_theorem() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.C007.restrict_sound"))
        .expect("C007c should exist");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "C007c should be Theorem (machine-checked proof), got {:?}",
        info.kind
    );
}

#[test]
fn test_helpers_kind_split_after_3568() {
    // Post-#3568 / 2026-04-27:
    // - merge_sound_helper: hypothesis-wrapped Declaration::Theorem.
    // - restrict_refines_helper / incremental_cost_helper: still
    //   Declaration::Opaque with sorry_inhabit_pi bodies (pending
    //   their own remediation slices).
    let env = make_env();

    let merge_info = env
        .get_const(&Name::from_string("NNVerify.C007.merge_sound_helper"))
        .expect("merge_sound_helper should be registered");
    assert_eq!(
        merge_info.kind,
        ConstantKind::Theorem,
        "merge_sound_helper must be a hypothesis-wrapped theorem after the \
         2026-04-27 retirement. Got: {:?}",
        merge_info.kind,
    );
    assert!(
        merge_info.value.is_some(),
        "merge_sound_helper theorem must carry the local-hypothesis proof",
    );

    let opaque_names = [
        "NNVerify.C007.restrict_refines_helper",
        "NNVerify.C007.incremental_cost_helper",
    ];
    for name in &opaque_names {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist"));
        assert_eq!(
            info.kind,
            ConstantKind::Opaque,
            "{name} should still be Opaque (sorry-inhabited, #3381), got {:?}",
            info.kind
        );
    }
}

#[test]
fn test_c007_axiom_inventory_after_3568() {
    // Post-2026-04-27 C007 carries no domain axioms. If this test ever flips,
    // either a new demotion landed or a previously-proved theorem regressed.
    let env = make_env();
    let c007_names = [
        "NNVerify.C007.merge_compositionality",
        "NNVerify.C007.incremental_cost_bound",
        "NNVerify.C007.restrict_sound",
        "NNVerify.C007.merge_sound_helper",
        "NNVerify.C007.restrict_refines_helper",
        "NNVerify.C007.incremental_cost_helper",
        "NNVerify.C007.BaBCert",
        "NNVerify.C007.cert_sound",
        "NNVerify.C007.merge_cert",
        "NNVerify.C007.restrict_cert",
        "NNVerify.C007.cert_cost",
        "NNVerify.C007.delta_cost",
        "NNVerify.C007.disjoint_cover",
    ];
    for name in &c007_names {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist"));
        assert!(
            !matches!(info.kind, ConstantKind::Axiom),
            "{name}: C007 should have no remaining Axioms; got kind={:?}",
            info.kind,
        );
    }
}

#[test]
fn test_foundation_types_are_opaque() {
    // Post-#3568: `cert_sound` is Opaque again (reverted from reducible
    // Definition — see `test_c007_cert_sound_is_opaque_not_reducible_definition`).
    // All other foundation primitives are Opaque as before.
    let env = make_env();
    let opaque_names = [
        "NNVerify.C007.BaBCert",
        "NNVerify.C007.cert_sound",
        "NNVerify.C007.merge_cert",
        "NNVerify.C007.restrict_cert",
        "NNVerify.C007.cert_cost",
        "NNVerify.C007.delta_cost",
        "NNVerify.C007.disjoint_cover",
    ];
    for name in &opaque_names {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist"));
        assert_eq!(
            info.kind,
            ConstantKind::Opaque,
            "{name} should be Opaque (upgraded from Axiom), got {:?}",
            info.kind
        );
    }
}

// ---------------------------------------------------------------
// Dependency tests — base infrastructure is present
// ---------------------------------------------------------------

#[test]
fn test_base_ibp_deps_present() {
    let env = make_env();
    // NNVerify types from init_nn_verify_types
    assert_registered(&env, "NNVerify.NNVec");
    assert_registered(&env, "NNVerify.IntervalBounds");
    assert_registered(&env, "NNVerify.IntervalBounds.contains");
    assert_registered(&env, "NNVerify.IntervalBounds.subset");
}

// ---------------------------------------------------------------
// Naming convention test
// ---------------------------------------------------------------

#[test]
fn test_naming_convention() {
    let env = make_env();
    let names = [
        "NNVerify.C007.merge_compositionality",
        "NNVerify.C007.incremental_cost_bound",
        "NNVerify.C007.restrict_sound",
        "NNVerify.C007.BaBCert",
        "NNVerify.C007.cert_sound",
        "NNVerify.C007.merge_cert",
        "NNVerify.C007.restrict_cert",
        "NNVerify.C007.cert_cost",
        "NNVerify.C007.delta_cost",
        "NNVerify.C007.disjoint_cover",
        "NNVerify.C007.merge_sound_helper",
        "NNVerify.C007.restrict_refines_helper",
        "NNVerify.C007.incremental_cost_helper",
    ];
    for name in &names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
        assert!(
            name.starts_with("NNVerify.C007."),
            "{name} must use NNVerify.C007. prefix"
        );
    }
}

// ---------------------------------------------------------------
// Idempotency test
// ---------------------------------------------------------------

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_streaming_certs().expect("first init");
    env.init_nn_verify_streaming_certs()
        .expect("second init (idempotent)");
}

// ---------------------------------------------------------------
// #3568 MASQUERADE-demotion behavioural tests
// ---------------------------------------------------------------
//
// These tests replace the #3461-era constructive-proof guards after
// the Branch A demasquerade of `merge_sound_helper`. See
// `designs/2026-04-19-demasquerade-cxxx-pattern.md` (Rules M1+M4) and
// the rustdoc on `register_c007_merge_sound_helper`.

/// True iff the innermost body (after stripping lambdas) is the canonical
/// synthetic sorry term. Still used by the remaining sorry-inhabited helpers
/// (restrict / incremental cost).
fn innermost_body_is_synthetic_sorry(env_value: &Expr) -> bool {
    let mut cursor = env_value;
    while let ExprKind::Lam(_, _, body) = cursor.kind() {
        cursor = body;
    }
    cursor.is_synthetic_sorry()
}

/// #3568: `cert_sound` must be `Declaration::Opaque` (NOT a reducible
/// Definition). The reducible-Definition promotion from #3461 was a
/// MASQUERADE Rule M1 enabler — it let `cert_sound d B c` delta-reduce
/// to `True`, admitting `True.intro` as a vacuous proof. Opaque values
/// are not unfolded by `def_eq`, closing that reduction path.
#[test]
fn test_c007_cert_sound_is_opaque_not_reducible_definition() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.C007.cert_sound"))
        .expect("cert_sound should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Opaque,
        "cert_sound must be Opaque after the #3568 MASQUERADE demotion \
         (reverted from the #3461 reducible Definition that enabled \
         `True.intro` as a vacuous merge_sound_helper proof). See \
         designs/2026-04-19-demasquerade-cxxx-pattern.md (Rule M1). \
         Got: {:?}",
        info.kind
    );
    // Opaque declarations carry `is_reducible = false` by construction
    // in our kernel, but pin it defensively in case the representation
    // ever diverges.
    assert!(
        !info.is_reducible,
        "cert_sound must NOT be reducible — a reducible carrier re-opens \
         the delta-reduction path exploited by the #3461 masquerade (#3568)"
    );
}

/// 2026-04-27: `merge_sound_helper` is a hypothesis-wrapped theorem. The
/// missing merge-soundness obligation is explicit as a local hypothesis, not
/// hidden behind a global axiom or the old `cert_sound = True` carrier.
#[test]
fn test_c007_merge_sound_helper_is_hypothesis_wrapped_theorem() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.C007.merge_sound_helper"))
        .expect("merge_sound_helper should be registered");

    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "merge_sound_helper must be the 2026-04-27 hypothesis-wrapped theorem. \
         Got: {:?}",
        info.kind
    );
    assert!(
        info.value.is_some(),
        "merge_sound_helper theorem must carry a local-hypothesis proof value"
    );
}

/// The hypothesis-wrapped `merge_sound_helper` must still type-check
/// via `env.get_const` / `TypeChecker::infer_type` on a `Const` reference,
/// and its stored type is still the C007a Pi shape with one extra local
/// conclusion hypothesis.
#[test]
fn test_c007_merge_sound_helper_type_still_type_checks() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.C007.merge_sound_helper"))
        .expect("merge_sound_helper should be registered");

    // Type is a Pi (9-argument product per build_c007a_type).
    assert!(
        matches!(info.type_.kind(), ExprKind::Pi(..)),
        "merge_sound_helper type should be Pi, got {:?}",
        info.type_.kind()
    );

    // The axiom reference itself type-checks at the const site.
    let const_ref = Expr::const_(
        Name::from_string("NNVerify.C007.merge_sound_helper"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let inferred = tc
        .infer_type(&const_ref)
        .expect("Const(merge_sound_helper) should type-check under TypeChecker");
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "merge_sound_helper Const-ref inferred type must be def_eq to \
         declared theorem type"
    );
}

/// Pins the sorry_inhabit_pi site count transition for C007. Now that
/// `merge_sound_helper` is a hypothesis-wrapped theorem, only
/// `restrict_refines_helper` and
/// `incremental_cost_helper` remain sorry-headed pending their own
/// remediation slices.
///
/// Before #3461: all 3 helpers were sorry-headed Opaques.
/// After  #3461: merge_sound_helper was True.intro-headed (MASQUERADE);
///               the other 2 were sorry-headed.
/// After  #3568: merge_sound_helper was an Axiom; the other 2 stayed sorry.
/// After  2026-04-27: merge_sound_helper is hypothesis-wrapped.
#[test]
fn test_c007_sorry_inhabit_pi_site_count_after_3568() {
    let env = make_env();

    // merge_sound_helper: local-hypothesis theorem, no sorry body.
    let merge_info = env
        .get_const(&Name::from_string("NNVerify.C007.merge_sound_helper"))
        .expect("merge_sound_helper registered");
    assert!(
        merge_info.value.is_some(),
        "merge_sound_helper must be a theorem after the 2026-04-27 retirement"
    );
    let merge_value = merge_info.value.as_ref().expect("theorem value");
    let merge_dbg = format!("{:?}", merge_value);
    for forbidden in ["True.intro", "sorry", "sorryAx"] {
        assert!(
            !merge_dbg.contains(forbidden),
            "merge_sound_helper proof must not mention {forbidden}; got {merge_dbg}",
        );
    }
    assert!(
        !innermost_body_is_synthetic_sorry(merge_value),
        "merge_sound_helper proof must not be sorry-inhabited"
    );

    // restrict_refines_helper: still sorry-headed Opaque.
    let restrict_value = env
        .get_const(&Name::from_string("NNVerify.C007.restrict_refines_helper"))
        .expect("restrict_refines_helper registered")
        .value
        .clone()
        .expect("Opaque value stored");
    assert!(
        innermost_body_is_synthetic_sorry(&restrict_value),
        "restrict_refines_helper should still be sorry-inhabited \
         (pending its own remediation slice)"
    );

    // incremental_cost_helper: still sorry-headed Opaque.
    let cost_value = env
        .get_const(&Name::from_string("NNVerify.C007.incremental_cost_helper"))
        .expect("incremental_cost_helper registered")
        .value
        .clone()
        .expect("Opaque value stored");
    assert!(
        innermost_body_is_synthetic_sorry(&cost_value),
        "incremental_cost_helper should still be sorry-inhabited \
         (pending its own remediation slice)"
    );
}

/// The retired `merge_sound_helper` transitive axiom closure must be empty:
/// no self axiom, no sorry, and no `True.intro` carrier path.
#[test]
fn test_c007_merge_sound_helper_has_no_sorry_in_axiom_closure() {
    let env = make_env();
    let deps = env
        .axiom_deps(&Name::from_string("NNVerify.C007.merge_sound_helper"))
        .expect("merge_sound_helper should be registered");
    assert!(
        deps.is_empty(),
        "merge_sound_helper should have no transitive axiom deps after the \
         2026-04-27 retirement; got {deps:?}",
    );
}
