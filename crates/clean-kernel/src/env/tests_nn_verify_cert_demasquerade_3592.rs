// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Guard tests for the #3592 Branch A demasquerade of
//! `NNVerify.cert_composition_trust` (T72) and its twin
//! `NNVerify.cert_list_composition_trust` (T72b).
//!
//! Per `designs/2026-04-19-demasquerade-cxxx-pattern.md` Rules M1
//! (alias-collapse via reducible Definition chain), M2 (identity
//! carrier), and M4 (`Eq.refl` root), and
//! `reports/audit/2026-04-20-r10-wave8-masquerade-sweep.md` Finding 1,
//! the prior `Declaration::Theorem` T72 proofs closed via `Eq.refl` over
//! a three-link reducible Definition alias chain:
//!
//! | Declaration | Prior kind | Body |
//! |-------------|------------|------|
//! | `NNVerify.BlockCert` | reducible Definition | `Nat` |
//! | `NNVerify.BlockCert.axiomProfile` | reducible Definition | `fun cert => cert` (identity) |
//! | `NNVerify.composePair` | reducible Definition | `fun c1 c2 => Nat.lor c1 c2` |
//!
//! Under δ-reduction, both sides of
//! `axiomProfile (composePair c1 c2) = Nat.lor (axiomProfile c1) (axiomProfile c2)`
//! collapsed to `Nat.lor c1 c2`, so `Eq.refl` type-checked. Identical
//! shape for T72b (list-level): both sides reduced to `listComposeTrust cs`.
//!
//! Branch A remediation (this file's guards):
//! 1. `cert_composition_trust` is now `Declaration::Axiom` on the
//!    original Pi type (no stored proof term).
//! 2. `cert_list_composition_trust` is also `Declaration::Axiom` — it
//!    shares the same masquerade pattern and its `Eq.refl` proof can
//!    no longer type-check once `axiomProfile` is Opaque.
//! 3. `NNVerify.BlockCert.axiomProfile` is flipped from reducible
//!    `Declaration::Definition` to `Declaration::Opaque` (same body).
//! 4. `NNVerify.composePair` is flipped from reducible
//!    `Declaration::Definition` to `Declaration::Opaque` (same body).
//! 5. `NNVerify.BlockCert` intentionally remains a reducible
//!    `Declaration::Definition` — demoting the `Nat` alias itself would
//!    break `axiomProfile`'s own body type-check (the identity lambda
//!    returns a `BlockCert`-typed local where `Nat` is expected, relying
//!    on δ-unfolding of `BlockCert = Nat`).
//! 6. The demoted Axioms' Pi types still type-check via the kernel
//!    TypeChecker to confirm the demotion did not regress declaration
//!    well-formedness.
//!
//! Mirrors the sibling demasquerade guard files for #3586
//! (`tests_nn_verify_zonotope_compress_c001_demasquerade_3586`), #3589
//! (C030c), etc.
//!
//! Part of #3592.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_cert_proofs()
        .expect("init_nn_verify_cert_proofs should succeed");
    env
}

// ---------------------------------------------------------------
// Guard 1: cert_composition_trust (T72) is an honest Axiom
// ---------------------------------------------------------------

#[test]
fn test_t72_cert_composition_trust_is_axiom_honest_demotion() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.cert_composition_trust"))
        .expect("cert_composition_trust should be registered");

    assert_eq!(
        info.kind,
        ConstantKind::Axiom,
        "#3592 Branch A demasquerade: cert_composition_trust MUST be \
         Declaration::Axiom (demoted from Theorem with masquerade proof \
         Eq.refl over reducible axiomProfile/composePair alias chain); \
         got {:?}",
        info.kind
    );
}

/// Structural guard: the Axiom carries no proof term. A regression that
/// smuggled a value in via `add_decl_structural` or a builder would
/// re-open the masquerade path.
#[test]
fn test_t72_cert_composition_trust_has_no_proof_value() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.cert_composition_trust"))
        .expect("cert_composition_trust should be registered");
    assert!(
        info.value.is_none(),
        "#3592: Axiom must carry no proof value (Declaration::Axiom has \
         no .value field); got value={:?}",
        info.value
    );
}

// ---------------------------------------------------------------
// Guard 2: cert_list_composition_trust (T72b) is an honest Axiom
// ---------------------------------------------------------------

#[test]
fn test_t72b_cert_list_composition_trust_is_axiom_honest_demotion() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.cert_list_composition_trust"))
        .expect("cert_list_composition_trust should be registered");

    assert_eq!(
        info.kind,
        ConstantKind::Axiom,
        "#3592 Branch A demasquerade (twin): cert_list_composition_trust \
         MUST be Declaration::Axiom (demoted from Theorem with masquerade \
         proof `fun cs => Eq.refl (listComposeTrust cs)`); got {:?}",
        info.kind
    );
}

#[test]
fn test_t72b_cert_list_composition_trust_has_no_proof_value() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.cert_list_composition_trust"))
        .expect("cert_list_composition_trust should be registered");
    assert!(
        info.value.is_none(),
        "#3592: twin Axiom must carry no proof value; got value={:?}",
        info.value
    );
}

// ---------------------------------------------------------------
// Guard 3: axiomProfile is Opaque (not a reducible Definition)
// ---------------------------------------------------------------

#[test]
fn test_axiom_profile_is_opaque_not_reducible_definition() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.BlockCert.axiomProfile"))
        .expect("axiomProfile should be registered");

    assert_eq!(
        info.kind,
        ConstantKind::Opaque,
        "#3592 Branch A demasquerade: axiomProfile MUST be \
         Declaration::Opaque (demoted from reducible Definition to block \
         δ-unfolding of `axiomProfile c -> c`, closing the T72 masquerade \
         path); got {:?}",
        info.kind
    );
}

/// Structural guard: axiomProfile retains its identity body (Opaque has a
/// value; we keep the identity lambda) AND is non-reducible. A reducible
/// Definition with the same body would re-open the δ-reduction that
/// enabled the original Eq.refl masquerade.
#[test]
fn test_axiom_profile_is_opaque_non_reducible_with_value() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.BlockCert.axiomProfile"))
        .expect("axiomProfile should be registered");
    assert!(
        info.value.is_some(),
        "#3592: axiomProfile should carry its Opaque value (identity \
         lambda body unchanged); got value=None"
    );
    assert!(
        !info.is_reducible,
        "#3592: axiomProfile must be non-reducible (Opaque). A reducible \
         Definition with identity body would re-open the δ-reduction \
         path that enabled the T72 masquerade."
    );
}

// ---------------------------------------------------------------
// Guard 4: composePair is Opaque (not a reducible Definition)
// ---------------------------------------------------------------

#[test]
fn test_compose_pair_is_opaque_not_reducible_definition() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.composePair"))
        .expect("composePair should be registered");

    assert_eq!(
        info.kind,
        ConstantKind::Opaque,
        "#3592 Branch A demasquerade: composePair MUST be \
         Declaration::Opaque (demoted from reducible Definition to \
         close the last δ-path in the T72 alias chain); got {:?}",
        info.kind
    );
}

#[test]
fn test_compose_pair_is_opaque_non_reducible_with_value() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.composePair"))
        .expect("composePair should be registered");
    assert!(
        info.value.is_some(),
        "#3592: composePair should carry its Opaque value (Nat.lor body \
         unchanged); got value=None"
    );
    assert!(
        !info.is_reducible,
        "#3592: composePair must be non-reducible (Opaque)."
    );
}

// ---------------------------------------------------------------
// Guard 5: BlockCert intentionally stays reducible
// ---------------------------------------------------------------
//
// Per R10 Finding 1 and the design doc, demoting BlockCert itself would
// break axiomProfile's body type-check. We only demote the M1/M2 carriers
// (axiomProfile, composePair) that directly closed the masquerade path.

#[test]
fn test_block_cert_stays_reducible_definition() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.BlockCert"))
        .expect("BlockCert should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Definition,
        "#3592: BlockCert intentionally stays Definition — demoting to \
         Opaque would break axiomProfile body type-check (identity lambda \
         returning BlockCert-typed local where Nat is expected). Got {:?}",
        info.kind
    );
    assert!(
        info.is_reducible,
        "#3592: BlockCert must stay reducible so its `= Nat` alias \
         δ-unfolds for downstream definitions."
    );
}

// ---------------------------------------------------------------
// Guard 6: demoted Axiom types still type-check as Pi
// ---------------------------------------------------------------

#[test]
fn test_t72_cert_composition_trust_type_still_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("NNVerify.cert_composition_trust"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).unwrap_or_else(|err| {
        panic!(
            "#3592: cert_composition_trust (Axiom) type should still \
             type-check, got: {err:?}"
        )
    });
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "#3592: cert_composition_trust type should remain Pi (same shape \
         as before demotion), got {:?}",
        ty.kind()
    );
}

#[test]
fn test_t72b_cert_list_composition_trust_type_still_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.cert_list_composition_trust"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).unwrap_or_else(|err| {
        panic!(
            "#3592: cert_list_composition_trust (Axiom) type should still \
             type-check, got: {err:?}"
        )
    });
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "#3592: cert_list_composition_trust type should remain Pi, \
         got {:?}",
        ty.kind()
    );
}
