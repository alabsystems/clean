// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A pattern variable bound to a constructor field whose type is a parameter
//! applied to earlier fields — `h₂` in `fun ⟨h₁, h₂⟩ => …` over `∃ h, p h`,
//! whose `Exists.intro` field is `(fun h => p h) h₁` once the predicate is in —
//! reads the head-beta-reduced `p h₁`, as Lean's `introN` gives it. Measured
//! 2026-09-11 (`Prop.exists_iff`, `Prop.forall_iff` in
//! `Mathlib/Logic/Basic.lean`): `simpa only [H] using h₂` could not rewrite
//! `h₁` to `True` under the un-reduced redex. The end-to-end shape is pinned
//! in `tests_simp_prop_hyp`; here the two sites are checked directly.

use clean_kernel::Environment;

#[test]
fn test_intro_head_beta_reduces_the_binder_type() {
    use crate::tactic::{intro, ProofState};
    use clean_kernel::{BinderInfo, Expr, Name};
    let env = Environment::with_prelude();
    let true_ = Expr::const_(Name::from_string("True"), vec![]);
    // `∀ (h : (fun x : Prop => x) True), True`
    let redex = Expr::app(
        Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0)),
        true_.clone(),
    );
    let goal = Expr::pi(BinderInfo::Default, redex, true_.clone());
    let mut state = ProofState::new(env, goal);
    intro(&mut state, &clean_parser::SurfaceName::generated_path("h")).expect("intro on a Pi goal");
    let h = state
        .current_goal()
        .expect("a goal remains")
        .local_ctx
        .iter()
        .find(|d| d.name == clean_parser::SurfaceName::generated_path("h"))
        .expect("the introduced local")
        .clone();
    assert_eq!(h.ty, true_, "the introduced type must be head-beta-reduced");
}

#[test]
fn test_constructor_field_types_are_head_beta_reduced() {
    use crate::infer::ElabCtx;
    use clean_kernel::{BinderInfo, Expr, Level, Name};
    let env = Environment::with_prelude();
    let ctx = ElabCtx::new(&env);
    // `Exists (fun h : Prop => True)` — its `intro` fields are `(w : Prop)` and
    // `(h : (fun h => True) w)`, the second a redex once the predicate is in.
    let pred = Expr::lam(
        BinderInfo::Default,
        Expr::prop(),
        Expr::const_(Name::from_string("True"), vec![]),
    );
    let scrutinee = Expr::app(
        Expr::app(
            Expr::const_(
                Name::from_string("Exists"),
                vec![Level::succ(Level::zero())],
            ),
            Expr::prop(),
        ),
        pred,
    );
    let tys = ctx
        .compute_ctor_field_types(&Name::from_string("Exists.intro"), &scrutinee)
        .expect("Exists.intro field types");
    assert_eq!(tys.len(), 2);
    assert_eq!(
        tys[1],
        Expr::const_(Name::from_string("True"), vec![]),
        "the predicate field must be head-beta-reduced, got {}",
        tys[1]
    );
}
