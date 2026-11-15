// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A pending elaborator type must cross the tactic bridge with one identity.
//! The enclosing application can determine that type after its `by` argument
//! finishes. Capturing the root before translating its enclosing locals used
//! the old meta IDs in the immutable scope and the new IDs in the visible goal.

use super::*;
use crate::tactic::TacticError;

fn run_with_pending_local(source: &str, false_goal: bool) -> Result<Expr, ElabError> {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let pending_type = ctx.fresh_meta(Expr::type_());
    ctx.push_local(SurfaceName::generated_path("pending"), pending_type.clone());
    let boolean = Expr::const_(Name::from_string("Bool"), vec![]);
    let flag = ctx.push_local(SurfaceName::generated_path("flag"), boolean.clone());
    let target = if false_goal {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [
                boolean.clone(),
                Expr::const_(Name::from_string("Bool.true"), vec![]),
                Expr::const_(Name::from_string("Bool.false"), vec![]),
            ],
        )
    } else {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                    boolean,
                ),
                Expr::fvar(flag),
            ),
            Expr::fvar(flag),
        )
    };
    ctx.current_expected_type = Some(target.clone());
    let term =
        clean_parser::parse_expr_with_tactics(source, &ctx.tactic_registry.tactic_patterns())
            .expect("tactic source parses");
    let proof = ctx.elaborate(&term)?;
    assert_eq!(
        ctx.metas.instantiate(&pending_type),
        pending_type,
        "the irrelevant pending type must not be solved to close the goal"
    );
    let proof_ty = ctx.infer_type_full(&proof)?;
    assert!(ctx.is_def_eq(&proof_ty, &target));
    Ok(proof)
}

#[test]
fn pending_local_type_survives_cases_bridge() {
    let _proof = run_with_pending_local("by cases flag <;> rfl", false)
        .expect("cases must preserve the remapped local type in its root scope");
}

#[test]
fn pending_local_type_survives_rfl_bridge() {
    let _proof = run_with_pending_local("by rfl", false)
        .expect("a direct close must preserve the remapped local type too");
}

#[test]
fn pending_local_type_does_not_prove_false() {
    let error = run_with_pending_local("by cases flag <;> rfl", true)
        .expect_err("translating a pending local must not equate true and false");
    let rendered = format!("{error:?}");
    assert!(
        matches!(
            error.innermost(),
            ElabError::TacticFailed(TacticError::TypeMismatch { .. })
        ) && rendered.contains("Bool.true")
            && rendered.contains("Bool.false"),
        "the invalid claim must fail on its distinct Boolean constructors: {rendered}"
    );
}

fn local_let_pending_value(source: &str) -> (Result<Expr, ElabError>, Expr) {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    // The pending value is created before h: assigning it a term that captures
    // h must still be refused by the existing immutable meta scope guard.
    let pending_value = ctx.fresh_meta(nat.clone());
    let h = ctx.fresh_fvar();
    ctx.push_local_let_with_fvar(
        SurfaceName::generated_path("h"),
        h,
        nat.clone(),
        pending_value.clone(),
    );
    ctx.current_expected_type = Some(nat.clone());
    let surface =
        clean_parser::parse_expr_with_tactics(source, &ctx.tactic_registry.tactic_patterns())
            .expect("actual tactic source parses");
    let result = ctx.elaborate(&surface);
    if let Ok(proof) = &result {
        let ty = ctx.infer_type_full(proof).expect("full proof type");
        assert!(ctx.is_def_eq(&ty, &nat));
    }
    (result, ctx.metas.instantiate(&pending_value))
}

#[test]
fn pending_local_let_value_crosses_nested_tactic_bridge() {
    let (proof, value) = local_let_pending_value("by\n  have hk : h = 7 := by rfl\n  exact h");
    let _proof = proof.expect("the genuine let value must be adopted and its solution returned");
    assert_eq!(value, Expr::nat_lit(7));
}

#[test]
fn pending_local_let_value_cannot_satisfy_contradictory_equations() {
    let (proof, _) = local_let_pending_value(
        "by\n  have hk : h = 7 := by rfl\n  have hj : h = 8 := by rfl\n  exact h",
    );
    let error = proof.expect_err("adopting a let value cannot equate 7 and 8");
    let rendered = format!("{error:?}");
    assert!(
        matches!(
            error.innermost(),
            ElabError::TacticFailed(TacticError::TypeMismatch { .. })
        ) && rendered.contains('7')
            && rendered.contains('8'),
        "the refusal must reach the distinct literals after the first equation: {rendered}",
    );
}

fn auxiliary_value_visibility(
    source: &str,
    visible_good: bool,
    pending_value: bool,
) -> (Result<Expr, ElabError>, Option<Expr>, Expr) {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let truth = Expr::const_(Name::from_string("True"), vec![]);
    let good =
        visible_good.then(|| ctx.push_local(SurfaceName::generated_path("good"), nat.clone()));
    let value = if pending_value {
        ctx.fresh_meta(truth.clone())
    } else {
        Expr::const_(Name::from_string("True.intro"), vec![])
    };
    let helper = ctx.push_local(SurfaceName::generated_path("helper"), nat.clone());
    ctx.aux_decl_locals.insert(helper);
    let p = ctx.fresh_fvar();
    ctx.push_local_let_with_fvar(SurfaceName::generated_path("p"), p, truth, value);
    let before = ctx.locals.to_vec();
    let values = ctx.locals.let_values().clone();
    ctx.current_expected_type = Some(nat.clone());
    let term =
        clean_parser::parse_expr_with_tactics(source, &ctx.tactic_registry.tactic_patterns())
            .expect("actual tactic source parses");
    let result = ctx.elaborate(&term);
    assert_eq!(ctx.locals.to_vec(), before);
    assert_eq!(ctx.locals.let_values(), &values);
    assert!(ctx.aux_decl_locals.contains(&helper));
    if let Ok(proof) = &result {
        let ty = ctx
            .infer_type_full(proof)
            .expect("full scoped proof inference");
        assert!(ctx.is_def_eq(&ty, &nat));
    }
    (result, good.map(Expr::fvar), Expr::fvar(helper))
}

#[test]
fn have_opacity_aux_value_meta_not_an_assumption() {
    let (result, _, _) = auxiliary_value_visibility("by assumption", false, true);
    let error = result.expect_err("an auxiliary declaration is not an assumption");
    assert!(matches!(
        error.innermost(),
        ElabError::TacticFailed(TacticError::NoMatchingHypothesis { tactic, goal })
            if tactic == "assumption" && goal.as_deref().is_some_and(|g| g.contains("Nat"))
    ));
}

#[test]
fn have_opacity_aux_value_meta_selects_visible_good() {
    let (result, good, _) = auxiliary_value_visibility("by assumption", true, true);
    assert_eq!(
        result.expect("the visible local remains available"),
        good.expect("visible good was requested")
    );
}

#[test]
fn have_opacity_aux_value_meta_explicit_name() {
    let (result, _, helper) = auxiliary_value_visibility("by exact helper", false, true);
    assert_eq!(
        result.expect("the explicit helper remains in elaborator scope"),
        helper
    );
}

#[test]
fn have_opacity_aux_ground_value_control() {
    let (result, _, _) = auxiliary_value_visibility("by assumption", false, false);
    let error = result.expect_err("the original non-reroot path hides auxiliaries");
    assert!(matches!(
        error.innermost(),
        ElabError::TacticFailed(TacticError::NoMatchingHypothesis { tactic, goal })
            if tactic == "assumption" && goal.as_deref().is_some_and(|g| g.contains("Nat"))
    ));
}

#[test]
fn have_opacity_reduction_contexts_retain_raw_proofs() {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let n = ctx.push_local(SurfaceName::generated_path("n"), nat.clone());
    let h = ctx.fresh_fvar();
    let raw = Expr::mdata(
        vec![(
            Name::from_string("_clean_have"),
            clean_kernel::MDataValue::Bool(true),
        )],
        Expr::fvar(n),
    );
    ctx.push_local_let_with_fvar(
        SurfaceName::generated_path("h"),
        h,
        nat.clone(),
        raw.clone(),
    );
    let l = ctx.fresh_fvar();
    ctx.push_local_let_with_fvar(SurfaceName::generated_path("l"), l, nat, Expr::fvar(n));
    assert_eq!(ctx.locals.let_value(h), Some(&raw));
    let full = ctx.build_local_ctx();
    assert!(full.get(h).expect("opaque local").value.is_none());
    assert_eq!(full.get(l).expect("true let").value, Some(Expr::fvar(n)));
    let h_expr = Expr::fvar(h);
    let demand = ctx.demand_local_ctx(&[&h_expr]);
    assert!(demand.get(h).expect("demand opaque local").value.is_none());
    assert!(
        demand.get(n).is_none(),
        "a hidden proof is not a reduction dependency"
    );
    let l_expr = Expr::fvar(l);
    let demand = ctx.demand_local_ctx(&[&l_expr]);
    assert_eq!(
        demand.get(l).expect("demand true let").value,
        Some(Expr::fvar(n))
    );
    assert!(
        demand.get(n).is_some(),
        "a genuine let retains its reduction dependency"
    );
    for info in [
        BinderInfo::Default,
        BinderInfo::Implicit,
        BinderInfo::StrictImplicit,
        BinderInfo::InstImplicit,
    ] {
        for mult in [
            clean_kernel::Multiplicity::Zero,
            clean_kernel::Multiplicity::One,
            clean_kernel::Multiplicity::Many,
        ] {
            let data = BinderData::new(info, mult);
            ctx.locals.set_binder_info(h, data);
            let full = ctx.build_local_ctx();
            let demand = ctx.demand_local_ctx(&[&h_expr]);
            for local in [
                full.get(h).expect("full local"),
                demand.get(h).expect("demand local"),
            ] {
                assert_eq!(local.bi, data);
                assert!(
                    local.value.is_none(),
                    "binder metadata must not expose the proof"
                );
            }
            assert_eq!(ctx.locals.binder_info(h), data);
        }
    }
    assert_eq!(
        ctx.locals.let_value(h),
        Some(&raw),
        "views never erase canonical proof data"
    );
}
