// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! RM1 gates at the unit level. The join point's metavariable gate once
//! asked the kernel's `has_expr_mvar_quick` flag, which never sees an
//! elaborator metavariable (a tagged `FVar`), so it declined nothing; these
//! drive it with a metavariable directly, beside a ground control.
//! `tests/rm1_elab_fixes_e2e.rs` covers the gates from source. A `where`
//! helper's hints are keyed by span as well as name, which only a nested
//! same-named helper could tell apart from source.

use super::*;
use crate::infer::elab_match::{take_join_outcomes, JoinOutcome};
use clean_parser::{SurfaceBinder, SurfaceBinderInfo, SurfaceMatchArm};

/// `match x with | true => 1 | _ => if b then 2 else 3`'s arms.
fn catch_all_arms() -> Vec<SurfaceMatchArm> {
    match parse_expr("match x with\n  | true => 1\n  | _ => if b then 2 else 3").expect("parses") {
        SurfaceExpr::Match(_, _, _, arms) => arms,
        other => panic!("expected a match, got {other:?}"),
    }
}

/// Lower the catch-all match over `x : Bool` against the expected type
/// `expected` builds, returning whether it lowered and the outcomes.
fn lower_against(expected: impl FnOnce(&mut ElabCtx<'_>) -> Expr) -> (bool, Vec<JoinOutcome>) {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let x = ctx.push_local(SurfaceName::generated_path("x"), bool_ty.clone());
    ctx.push_local(SurfaceName::generated_path("b"), bool_ty.clone());
    let ty = expected(&mut ctx);
    ctx.current_expected_type = Some(ty);
    let _ = take_join_outcomes();
    let lowered = ctx
        .try_lower_match_with_join_point(&Expr::fvar(x), &bool_ty, None, false, &catch_all_arms())
        .expect("a declined join is not an error");
    (lowered.is_some(), take_join_outcomes())
}

#[test]
fn join_point_applies_against_a_ground_expected_type() {
    let (lowered, outcomes) = lower_against(|_| Expr::const_(Name::from_string("Nat"), vec![]));
    assert!(
        lowered,
        "control: a ground expected type lowers: {outcomes:?}"
    );
    assert_eq!(outcomes.last(), Some(&JoinOutcome::Applied));
}

#[test]
fn join_point_declines_an_expected_type_with_a_metavariable() {
    let (lowered, outcomes) =
        lower_against(|ctx| Expr::fvar(MetaState::to_fvar(ctx.metas.fresh(Expr::type_()))));
    assert!(!lowered, "an open expected type is declined: {outcomes:?}");
    assert_eq!(outcomes, vec![JoinOutcome::ExpectedTypeOpen]);
}

/// A `where` helper's hints reach the `let rec` binder the desugarer builds
/// for that helper (same span and name), and no other binder of the name.
#[test]
fn where_hints_are_keyed_by_span_and_name() {
    let decls = clean_parser::parse_file(
        "def countUp (limit : Nat) : Nat :=\n  go 0\nwhere\n  go (i : Nat) : Nat :=\n    \
         if i < limit then go (i + 1) else i\n  termination_by limit - i",
    )
    .expect("parses");
    let [SurfaceDecl::Def { where_decls, .. }] = decls.as_slice() else {
        panic!("expected one def, got {decls:?}");
    };
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    ctx.register_where_termination(where_decls);
    let helper = &where_decls[0];
    let binder = |span| SurfaceBinder {
        span,
        name: helper.name.clone(),
        ty: None,
        default: None,
        info: SurfaceBinderInfo::Explicit,
    };
    let hinted = ctx.where_termination_for(&binder(helper.span));
    assert!(
        hinted
            .termination_by
            .as_ref()
            .and_then(|tb| tb.well_founded_measure())
            .is_some(),
        "the helper's own binder gets its measure"
    );
    let elsewhere = clean_parser::Span::new(helper.span.end + 10, helper.span.end + 12);
    let other = ctx.where_termination_for(&binder(elsewhere));
    assert!(
        other.termination_by.is_none() && other.decreasing_by.is_none(),
        "a same-named binder elsewhere gets nothing"
    );
}
