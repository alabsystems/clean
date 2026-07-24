// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for recursor universe parameter supply during match elaboration (#422).
//!
//! Verifies that `eliminator_levels` correctly uses the RecursorVal's level_params
//! to determine whether to include a motive universe level, handling both
//! universe-polymorphic and Prop-only inductives correctly.

use super::*;
use clean_kernel::env::{ConstantInfo, Declaration, TrustedEnvExt};
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};

/// Build an environment with a universe-polymorphic `MyOpt` inductive:
///   `inductive MyOpt (α : Type u) : Type u | none | some : α → MyOpt α`
///
/// This has `level_params = [u]`, so the recursor should have
/// `level_params = [u_motive, u]` (motive + inductive param).
fn poly_opt_env() -> Environment {
    let mut env = Environment::with_prelude();

    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());
    let type_u = Expr::sort(Level::succ(u_level.clone()));

    // MyOpt : Type u → Type u
    let myopt_name = Name::from_string("MyOpt");
    let myopt_type = Expr::pi(BinderInfo::Default, type_u.clone(), type_u.clone());

    // MyOpt.none : {α : Type u} → MyOpt α
    let none_type = Expr::pi(
        BinderInfo::Implicit,
        type_u.clone(),
        Expr::app(
            Expr::const_(myopt_name.clone(), vec![u_level.clone()]),
            Expr::bvar(0),
        ),
    );

    // MyOpt.some : {α : Type u} → α → MyOpt α
    let some_type = Expr::pi(
        BinderInfo::Implicit,
        type_u,
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0), // α
            Expr::app(
                Expr::const_(myopt_name.clone(), vec![u_level.clone()]),
                Expr::bvar(1), // α (shifted)
            ),
        ),
    );

    let decl = InductiveDecl {
        level_params: vec![u],
        num_params: 1,
        types: vec![InductiveType {
            name: myopt_name.clone(),
            type_: myopt_type,
            constructors: vec![
                Constructor {
                    name: Name::from_string("MyOpt.none"),
                    type_: none_type,
                },
                Constructor {
                    name: Name::from_string("MyOpt.some"),
                    type_: some_type,
                },
            ],
        }],
    };

    env.add_inductive(decl)
        .expect("MyOpt inductive should register");
    env
}

/// Test that match on a universe-polymorphic inductive correctly supplies
/// both the motive universe and the inductive's universe parameter.
#[test]
fn test_match_poly_inductive_supplies_all_universe_levels() {
    use clean_parser::{Span, SurfaceMatchArm, SurfacePattern};

    let env = poly_opt_env();

    // Verify the recursor was created and has the right level_params structure.
    let rec_val = env.get_recursor(&Name::from_string("MyOpt.casesOn"));
    assert!(rec_val.is_some(), "MyOpt.casesOn should be registered");
    let rec_val = rec_val.unwrap();
    // Should have motive_univ + u = 2 level params
    assert_eq!(
        rec_val.level_params.len(),
        2,
        "MyOpt.casesOn should have 2 level params (motive + u), got {:?}",
        rec_val.level_params
    );

    // Create: axiom x : MyOpt Nat
    let myopt_nat = Expr::app(
        Expr::const_(
            Name::from_string("MyOpt"),
            vec![Level::succ(Level::zero())], // u = 1 for Nat
        ),
        Expr::const_(Name::from_string("Nat"), vec![]),
    );

    let mut ctx = ElabCtx::new(&env);
    // Push x : MyOpt Nat
    let _x_fvar = ctx.push_local("x".to_string(), myopt_nat);

    // match x with | MyOpt.none => 0 | MyOpt.some n => n
    let match_expr = SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(SurfaceExpr::Ident(Span::dummy(), "x".to_string())),
        vec![
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Ctor("MyOpt.none".to_string(), vec![]),
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)),
            },
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Ctor(
                    "MyOpt.some".to_string(),
                    vec![SurfacePattern::Var("n".to_string())],
                ),
                body: SurfaceExpr::Ident(Span::dummy(), "n".to_string()),
            },
        ],
    );

    let result = ctx.elaborate(&match_expr);
    assert!(
        result.is_ok(),
        "match on universe-polymorphic MyOpt Nat should elaborate, got {result:?}"
    );

    // Verify the elaborated result contains the eliminator with correct level count.
    let expr = result.unwrap();
    fn find_elim_levels(e: &Expr) -> Option<Vec<Level>> {
        match e.kind() {
            ExprKind::Const(name, levels) if name.to_string().contains("casesOn") => {
                Some(levels.to_vec())
            }
            ExprKind::App(f, _) => find_elim_levels(f),
            _ => None,
        }
    }
    if let Some(levels) = find_elim_levels(&expr) {
        assert_eq!(
            levels.len(),
            2,
            "MyOpt.casesOn should be applied with 2 universe levels, got {levels:?}"
        );
    }
}

/// Test that match on Nat (a monomorphic Type inductive) still works correctly.
/// Nat has level_params = [], so Nat.casesOn has level_params = [motive_univ].
#[test]
fn test_match_nat_caseson_has_motive_universe() {
    let env = Environment::with_prelude();

    // Verify Nat.casesOn has exactly 1 level param (motive only).
    let rec_val = env.get_recursor(&Name::from_string("Nat.casesOn"));
    assert!(rec_val.is_some(), "Nat.casesOn should exist");
    let rec_val = rec_val.unwrap();
    assert_eq!(
        rec_val.level_params.len(),
        1,
        "Nat.casesOn should have 1 level param (motive only), got {:?}",
        rec_val.level_params
    );
}

/// Test that match on Bool (also a monomorphic inductive) elaborates correctly.
#[test]
fn test_match_bool_caseson_levels() {
    use clean_parser::{Span, SurfaceMatchArm, SurfacePattern};

    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("b"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Bool"), vec![]),
    })
    .unwrap();

    let mut ctx = ElabCtx::new(&env);

    // match b with | Bool.true => 1 | Bool.false => 0
    let match_expr = SurfaceExpr::Match(
        Span::dummy(),
        None,
        Box::new(SurfaceExpr::Ident(Span::dummy(), "b".to_string())),
        vec![
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Ctor("Bool.true".to_string(), vec![]),
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(1)),
            },
            SurfaceMatchArm {
                span: Span::dummy(),
                pattern: SurfacePattern::Ctor("Bool.false".to_string(), vec![]),
                body: SurfaceExpr::Lit(Span::dummy(), SurfaceLit::Nat(0)),
            },
        ],
    );

    let result = ctx.elaborate(&match_expr);
    assert!(
        result.is_ok(),
        "match on Bool with correct universe levels should elaborate, got {result:?}"
    );
}

/// Test that the eliminator_levels function correctly handles the recursor
/// lookup path vs the fallback path.
///
/// When the recursor IS registered, it uses the RecursorVal's level_params
/// to determine the universe structure. When NOT registered, it falls back
/// to the old heuristic.
#[test]
fn test_eliminator_levels_uses_recursor_val() {
    let env = poly_opt_env();

    // The MyOpt.rec recursor should also exist and have level_params.
    let rec_val = env.get_recursor(&Name::from_string("MyOpt.rec"));
    assert!(rec_val.is_some(), "MyOpt.rec should be registered");
    let rec_val = rec_val.unwrap();
    // rec should also have 2 level params (motive + u)
    assert_eq!(
        rec_val.level_params.len(),
        2,
        "MyOpt.rec should have 2 level params (motive + u), got {:?}",
        rec_val.level_params
    );
}

#[test]
fn metadata_fail_closed_recursor_constant_disagreement_is_atomic() {
    let mut env = poly_opt_env();
    let cases_name = Name::from_string("MyOpt.casesOn");
    let mut malformed = env
        .get_recursor(&cases_name)
        .cloned()
        .expect("MyOpt.casesOn recursor metadata");
    malformed
        .level_params
        .push(Name::from_string("fabricated_recursor_level"));
    // Trusted import registration replaces the registry packet but preserves
    // the already-present constant, creating the exact authority disagreement
    // that elaboration must reject.
    env.register_recursor(malformed);

    let mut ctx = ElabCtx::new(&env);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let myopt_nat = Expr::app(
        Expr::const_(Name::from_string("MyOpt"), vec![Level::succ(Level::zero())]),
        nat.clone(),
    );
    let sentinel = ctx.push_local("sentinel".to_string(), nat.clone());
    let locals_before = ctx.locals.clone();
    let universes_before = ctx.universe_params.clone();
    let pending_before = ctx.pending_level_assigns.borrow().clone();
    let meta_depth_before = ctx.metas.scope_depth();
    let meta_trail_before = ctx.metas.undo_trail_len_for_tests();

    let result = ctx.eliminator_levels(&cases_name, &myopt_nat, &nat);
    assert!(
        matches!(&result, Err(ElabError::InternalInvariant(message)) if message.contains("constant/recursor") && message.contains("disagree")),
        "recursor/constant disagreement must fail before guessing levels, got {result:?}"
    );
    assert_eq!(ctx.locals, locals_before);
    assert_eq!(ctx.universe_params, universes_before);
    assert_eq!(*ctx.pending_level_assigns.borrow(), pending_before);
    assert_eq!(ctx.metas.scope_depth(), meta_depth_before);
    assert_eq!(ctx.metas.undo_trail_len_for_tests(), meta_trail_before);
    assert_eq!(
        ctx.elaborate(&SurfaceExpr::Ident(
            clean_parser::Span::dummy(),
            "sentinel".to_string(),
        ))
        .expect("same context remains usable"),
        Expr::fvar(sentinel)
    );
}

#[test]
fn metadata_fail_closed_scrutinee_level_arity_mints_no_state() {
    let env = poly_opt_env();
    let mut ctx = ElabCtx::new(&env);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let malformed = Expr::app(
        Expr::const_(Name::from_string("MyOpt"), vec![]),
        nat.clone(),
    );
    let universes_before = ctx.universe_params.clone();
    let pending_before = ctx.pending_level_assigns.borrow().clone();
    let meta_depth_before = ctx.metas.scope_depth();
    let meta_trail_before = ctx.metas.undo_trail_len_for_tests();

    let result = ctx.eliminator_levels(&Name::from_string("MyOpt.casesOn"), &malformed, &nat);
    assert!(
        matches!(&result, Err(ElabError::InternalInvariant(message)) if message.contains("supplies 0 universe levels") && message.contains("requires 1")),
        "scrutinee level arity corruption must fail before motive-level inference, got {result:?}"
    );
    assert!(ctx.locals.is_empty());
    assert_eq!(ctx.universe_params, universes_before);
    assert_eq!(*ctx.pending_level_assigns.borrow(), pending_before);
    assert_eq!(ctx.metas.scope_depth(), meta_depth_before);
    assert_eq!(ctx.metas.undo_trail_len_for_tests(), meta_trail_before);
}

#[test]
fn metadata_fail_closed_partial_parameter_spine_is_rejected() {
    let env = poly_opt_env();
    let ctx = ElabCtx::new(&env);
    let partial = Expr::const_(Name::from_string("MyOpt"), vec![Level::succ(Level::zero())]);
    let result = ctx.apply_eliminator_params_count(
        Expr::const_(Name::from_string("MyOpt.casesOn"), vec![]),
        &partial,
        1,
    );
    assert!(
        matches!(&result, Err(ElabError::InternalInvariant(message)) if message.contains("supplies 0 type arguments") && message.contains("requires 1")),
        "mandatory eliminator construction must reject a partial inductive spine, got {result:?}"
    );
    assert!(ctx.locals.is_empty());
    assert_eq!(ctx.metas.scope_depth(), 0);
    assert_eq!(ctx.metas.undo_trail_len_for_tests(), 0);
}

#[test]
fn metadata_fail_closed_wrong_recursor_rhs_reaches_match_boundary() {
    let mut env = poly_opt_env();
    let cases_name = Name::from_string("MyOpt.casesOn");
    let mut malformed = env
        .get_recursor(&cases_name)
        .cloned()
        .expect("MyOpt.casesOn metadata");
    assert_eq!(malformed.rules.len(), 2);
    malformed.rules[1].rhs = malformed.rules[0].rhs.clone();
    env.register_recursor(malformed);

    let ctx = ElabCtx::new(&env);
    let error = match ctx.match_eliminator_metadata("MyOpt", &cases_name, true) {
        Ok(_) => panic!("wrong recursor RHS unexpectedly authenticated"),
        Err(error) => error,
    };
    assert!(
        matches!(&error, ElabError::InternalInvariant(message)
            if message.contains("failed authentication")
                && message.contains("violates subject reduction")),
        "a well-formed but wrong iota RHS must be rejected before match lowering, got {error:?}"
    );
}

#[test]
fn metadata_fail_closed_member_recursor_is_bound_to_requested_family() {
    let mut env = poly_opt_env();
    let rec_name = Name::from_string("MyOpt.rec");
    let mut misplaced = env
        .get_recursor(&rec_name)
        .cloned()
        .expect("MyOpt.rec metadata");
    // The packet remains internally valid for the MyOpt major premise and all
    // of its genuine constructor rules. Only its family identity is poisoned;
    // packet-local authentication alone must not let it contribute minors to
    // the member-derived `MyOpt.rec` slot.
    misplaced.inductive_name = Name::from_string("Bool");
    env.register_recursor(misplaced);

    let cases_name = Name::from_string("MyOpt.casesOn");
    let error = match ElabCtx::new(&env).match_eliminator_metadata("MyOpt", &cases_name, true) {
        Ok(_) => panic!("misidentified family recursor unexpectedly authenticated"),
        Err(error) => error,
    };
    assert!(
        matches!(&error, ElabError::InternalInvariant(message)
            if message.contains("MyOpt.rec")
                && message.contains("identifies `Bool` instead of member `MyOpt`")),
        "a genuine-yet-unrelated recursor packet must not supply another family's minors, got {error:?}"
    );
}

#[test]
fn metadata_fail_closed_overapplied_scrutinee_spine_is_rejected() {
    let env = poly_opt_env();
    let ctx = ElabCtx::new(&env);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let myopt_nat = Expr::app(
        Expr::const_(Name::from_string("MyOpt"), vec![Level::zero()]),
        nat.clone(),
    );
    let overapplied = Expr::app(myopt_nat, nat);
    let result = ctx.compute_ctor_field_types(&Name::from_string("MyOpt.some"), &overapplied);
    assert!(
        matches!(&result, Err(ElabError::InternalInvariant(message))
            if message.contains("supplies 2 type arguments") && message.contains("requires 1")),
        "constructor-field recovery must reject an overapplied inductive spine, got {result:?}"
    );
}

#[test]
fn metadata_fail_closed_overapplied_constructor_return_spine_is_rejected() {
    let mut env = poly_opt_env();
    let some_name = Name::from_string("MyOpt.some");
    let mut malformed = env
        .get_constructor(&some_name)
        .cloned()
        .expect("MyOpt.some metadata");
    let u = Name::from_string("u");
    let type_u = Expr::sort(Level::succ(Level::param(u.clone())));
    let malformed_return = Expr::apps(
        Expr::const_(Name::from_string("MyOpt"), vec![Level::param(u.clone())]),
        vec![
            Expr::bvar(1),
            Expr::const_(Name::from_string("Nat"), vec![]),
        ],
    );
    let malformed_type = Expr::pi(
        BinderInfo::Implicit,
        type_u,
        Expr::pi(BinderInfo::Default, Expr::bvar(0), malformed_return),
    );
    malformed.type_ = malformed_type.clone();

    assert!(env.forget_decl(&some_name));
    env.extend_constants_unchecked(std::iter::once(ConstantInfo::new(
        some_name.clone(),
        vec![u],
        malformed_type,
        None,
        false,
    )));
    env.register_constructor(malformed);

    let ctx = ElabCtx::new(&env);
    let scrutinee = Expr::app(
        Expr::const_(Name::from_string("MyOpt"), vec![Level::zero()]),
        Expr::const_(Name::from_string("Nat"), vec![]),
    );
    let result = ctx.compute_ctor_field_types(&some_name, &scrutinee);
    assert!(
        matches!(&result, Err(ElabError::InternalInvariant(message))
            if message.contains("return spine supplies 2 arguments") && message.contains("expected 1")),
        "a constructor whose constant and side table agree on an overapplied return must still be rejected, got {result:?}"
    );
}

#[test]
fn default_selection_authenticates_later_constructors_before_returning() {
    let mut env = Environment::with_prelude();
    let succ_name = Name::from_string("Nat.succ");
    let mut malformed = env
        .get_constructor(&succ_name)
        .cloned()
        .expect("Nat.succ metadata");
    // Nat.zero is the first, valid nullary constructor. A premature return
    // would therefore hide this false field count on Nat.succ.
    malformed.num_fields = 0;
    env.register_constructor(malformed);

    let ctx = ElabCtx::new(&env);
    let result = ctx.try_default_value_of_type(&Expr::const_(Name::from_string("Nat"), vec![]));
    assert!(
        matches!(&result, Err(ElabError::InternalInvariant(message))
            if message.contains("Nat.succ") && message.contains("does not return inductive")),
        "default discovery must authenticate constructors after the first nullary candidate, got {result:?}"
    );
}

fn import_shaped_bool_env(corrupt_cases_body: bool) -> Environment {
    let donor = Environment::with_prelude();
    let bool_name = Name::from_string("Bool");
    let cases_name = Name::from_string("Bool.casesOn");
    let mut env = Environment::new();
    let bool_info = donor
        .get_inductive(&bool_name)
        .cloned()
        .expect("donor Bool metadata");
    env.register_inductive(bool_info.clone());
    for ctor_name in &bool_info.constructor_names {
        env.register_constructor(
            donor
                .get_constructor(ctor_name)
                .cloned()
                .unwrap_or_else(|| panic!("donor constructor `{ctor_name}`")),
        );
    }
    env.register_recursor(
        donor
            .get_recursor(&Name::from_string("Bool.rec"))
            .cloned()
            .expect("donor Bool.rec metadata"),
    );

    let mut cases = donor
        .get_const(&cases_name)
        .cloned()
        .expect("donor Bool.casesOn definition");
    assert!(cases.value.is_some());
    if corrupt_cases_body {
        let bad_name = Name::from_string("BadBoolCases");
        env.add_decl(Declaration::Axiom {
            name: bad_name.clone(),
            level_params: cases.level_params.clone(),
            type_: cases.type_.clone(),
        })
        .expect("same-typed bad cases axiom should register");
        let levels: Vec<Level> = cases
            .level_params
            .iter()
            .cloned()
            .map(Level::param)
            .collect();
        cases.value = Some(Expr::const_(bad_name, levels));
    }
    env.extend_constants_unchecked(std::iter::once(cases));
    assert!(env.get_recursor(&cases_name).is_none());
    env
}

#[test]
fn imported_cases_on_requires_the_canonical_checked_wrapper() {
    let cases_name = Name::from_string("Bool.casesOn");

    let canonical = import_shaped_bool_env(false);
    ElabCtx::new(&canonical)
        .match_eliminator_metadata("Bool", &cases_name, true)
        .expect("the canonical imported Bool.casesOn wrapper must authenticate");

    let corrupt = import_shaped_bool_env(true);
    let error = match ElabCtx::new(&corrupt).match_eliminator_metadata("Bool", &cases_name, true) {
        Ok(_) => panic!("same-typed noncanonical casesOn unexpectedly authenticated"),
        Err(error) => error,
    };
    assert!(
        matches!(&error, ElabError::InternalInvariant(message)
            if message.contains("imported cases eliminator")
                && message.contains("not definitionally equal")),
        "a same-typed imported casesOn body must not substitute for the canonical recursor wrapper, got {error:?}"
    );
}
