// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Guard tests for the `Rat.abs` carrier — Branch B remediation (TCB-shrink
//! Tier 1), which SUPERSEDES the #3565 Branch A opacity workaround.
//!
//! # History and why the invariant flipped
//!
//! - #3545 promoted four `Rat.abs_*` to Theorems with `Eq.refl` / `Rat.le_refl`
//!   bodies that type-checked only because `Rat.abs` was a reducible
//!   `Declaration::Definition` with the IDENTITY body `fun a : Rat => a`
//!   (#3435). Under δ-reduction LHS/RHS collapsed to the same term — classic
//!   M1 masquerade (zero mathematical content beyond the alias).
//! - #3565 Branch A patched the *symptom*: it demoted the four theorems back to
//!   axioms and co-demoted `Rat.abs` to `Declaration::Opaque` so its identity
//!   body would no longer δ-reduce. But the carrier was STILL the identity, so
//!   the axioms stayed false-in-model (`Rat.abs_nonneg : 0 ≤ |a|` ≡ `0 ≤ a`),
//!   merely hidden behind opacity.
//! - TCB-shrink Tier 1 Branch B fixes the *cause*: `Rat.abs` is now the
//!   FAITHFUL reducible Definition `Rat.abs a := Rat.max a (Rat.neg a)`. The M1
//!   masquerade is closed STRUCTURALLY by the body itself — `Rat.abs a`
//!   δ-reduces to `max a (-a)`, which is NOT def-eq to `a` (nor to `-a`)
//!   in general — so an `Eq.refl`-based "proof" of `Rat.abs a = a` no longer
//!   type-checks. Opacity is no longer needed and would in fact block the
//!   genuine constructive proofs that now characterize `Rat.abs`.
//!
//! These tests pin the Branch B invariant: the carrier is a reducible
//! Definition AND the masquerade path is closed by the non-trivial body.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_rat_abs().expect("init_rat_abs should succeed");
    env
}

// ---------------------------------------------------------------
// Guard 1: Rat.abs is a FAITHFUL reducible Definition (Branch B)
// ---------------------------------------------------------------

/// `Rat.abs` MUST be a reducible `Declaration::Definition` carrying a body —
/// the faithful `Rat.max a (Rat.neg a)`. The old Branch A `Opaque` identity
/// carrier was a workaround; Branch B replaces it with the real definition.
#[test]
fn test_rat_abs_carrier_is_faithful_reducible_definition() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("Rat.abs"))
        .expect("Rat.abs should be registered");

    assert_eq!(
        info.kind,
        ConstantKind::Definition,
        "TCB-shrink Tier 1 Branch B: Rat.abs MUST be a reducible \
         Declaration::Definition (= Rat.max a (Rat.neg a)); got {:?}",
        info.kind
    );
    assert!(
        info.value.is_some(),
        "Rat.abs must carry the faithful max/neg body"
    );
    assert!(
        info.is_reducible,
        "Rat.abs must be reducible so its lemmas can be proved by unfolding to \
         Rat.max a (Rat.neg a)"
    );
}

// ---------------------------------------------------------------
// Guard 2: Rat.abs type still type-checks as Pi (Rat → Rat)
// ---------------------------------------------------------------

#[test]
fn test_rat_abs_carrier_type_still_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("Rat.abs"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&e)
        .unwrap_or_else(|err| panic!("Rat.abs type should type-check, got: {err:?}"));
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "Rat.abs type should be Pi (Rat → Rat), got {:?}",
        ty.kind()
    );
}

// ---------------------------------------------------------------
// Guard 3: the M1 masquerade is closed by the FAITHFUL body
// ---------------------------------------------------------------

/// The crux of the Branch B soundness argument: with the faithful carrier
/// `Rat.abs a = Rat.max a (Rat.neg a)`, the bogus equality `Rat.abs a = a`
/// is NOT provable by `@Eq.refl Rat a` — the kernel correctly REJECTS it,
/// because `Rat.abs a` does not reduce to `a`. (Under the old identity carrier
/// this `Eq.refl` would have type-checked: the masquerade.)
///
/// We check the masquerade is blocked by type-checking the would-be proof term
/// against the bogus type and asserting it FAILS.
#[test]
fn test_rat_abs_eq_self_refl_masquerade_is_rejected() {
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());

    let rat = Expr::const_(Name::from_string("Rat"), vec![]);
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(rat.clone());

    // Bogus claim: ∀ a, Rat.abs a = a.
    let eq_c = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let abs_a = Expr::app(
        Expr::const_(Name::from_string("Rat.abs"), vec![]),
        a.clone(),
    );
    let bogus_concl = Expr::apps(eq_c, [rat.clone(), abs_a, a.clone()]);
    let bogus_ty = b.mk_pi(
        a_id,
        crate::expr::BinderInfo::Default,
        rat.clone(),
        bogus_concl,
    );
    let bogus_ty = b.finish(bogus_ty);

    // Would-be masquerade proof: fun a => @Eq.refl Rat a.
    let mut bp = EnvDeclBuilder::new();
    let (a2_id, a2) = bp.fresh_local(rat.clone());
    let refl = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [rat.clone(), a2.clone()],
    );
    let bogus_proof = bp.mk_lam(a2_id, crate::expr::BinderInfo::Default, rat.clone(), refl);
    let bogus_proof = bp.finish(bogus_proof);

    let result = tc.check_type(&bogus_proof, &bogus_ty);
    assert!(
        result.is_err(),
        "MASQUERADE REGRESSION: `fun a => Eq.refl a` type-checked against \
         `∀ a, Rat.abs a = a`. With the faithful carrier `Rat.abs a = \
         Rat.max a (Rat.neg a)` this MUST fail — if it succeeds the carrier has \
         regressed to an identity (or otherwise trivial) body and the abs \
         lemmas are masquerading again."
    );
}
