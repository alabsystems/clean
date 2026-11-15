// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Failed term-let body cleanup, independently of term-let opacity.
//!
//! These use the actual elaboration entry points, not a surrounding rollback
//! transaction. Scope content must be restored; cumulative work counters,
//! generation tokens and fresh identifiers deliberately remain monotone.

use super::{ElabCtx, RecursiveDefContext};
use crate::ElabError;
use clean_kernel::{BinderInfo, Environment, Expr, ExprKind, FVarId, Level, Name, TypeChecker};
use clean_parser::{parse_expr, SurfaceName};
use std::collections::{HashMap, HashSet};

#[derive(Debug, PartialEq, Eq)]
struct ScopeContent {
    locals: Vec<(SurfaceName, FVarId, Expr)>,
    local_let_values: HashMap<FVarId, Expr>,
    local_instances: Vec<(FVarId, Expr)>,
    local_name_aliases: Vec<(SurfaceName, FVarId)>,
    auxiliary_locals: HashSet<FVarId>,
    recursive_context: String,
    helper_uses: String,
    expected_type: Option<Expr>,
}

fn scope_content(ctx: &ElabCtx<'_>) -> ScopeContent {
    ScopeContent {
        locals: ctx.locals.clone(),
        local_let_values: ctx.locals.let_values().clone(),
        local_instances: ctx.local_instances.clone(),
        local_name_aliases: ctx.local_name_aliases.clone(),
        auxiliary_locals: ctx.aux_decl_locals.clone(),
        recursive_context: format!("{:?}", ctx.recursive_def_ctx),
        helper_uses: format!("{:?}", ctx.let_rec_lift),
        expected_type: ctx.current_expected_type.clone(),
    }
}

fn nat() -> Expr {
    Expr::const_str("Nat")
}

/// Real pre-existing opaque and let locals, an instance and auxiliary-use
/// bookkeeping must survive the cleanup of a different failed binder.
fn seeded_ctx(env: &Environment) -> ElabCtx<'_> {
    let mut ctx = ElabCtx::new(env);
    let held = ctx.push_local(SurfaceName::generated_path("held"), nat());
    let held_let = ctx.fresh_fvar();
    ctx.push_local_let_with_fvar(
        SurfaceName::generated_path("held_let"),
        held_let,
        nat(),
        Expr::nat_lit(23),
    );
    ctx.local_name_aliases
        .push((SurfaceName::generated_path("held_alias"), held));
    ctx.aux_decl_locals.insert(held_let);
    ctx.push_let_rec_use(
        held_let,
        &Name::from_string("held_auxiliary"),
        &nat(),
        &Expr::nat_lit(23),
    );
    let inhabited = Expr::app(
        Expr::const_(Name::from_string("Inhabited"), vec![Level::zero()]),
        nat(),
    );
    let instance = ctx.push_local(
        SurfaceName::generated_path("held_instance"),
        inhabited.clone(),
    );
    ctx.push_local_instance(instance, inhabited);
    ctx.recursive_def_ctx = Some(RecursiveDefContext {
        func_name: SurfaceName::generated_path("held_recursive"),
        decreasing_arg_pos: 0,
        decreasing_arg_name: SurfaceName::generated_path("held"),
        inductive_type_name: Some(Name::from_string("Nat")),
        ih_fvar: Some(held),
        ih_type: Some(nat()),
        ih_map: HashMap::from([(held_let, held)]),
        sibling_names: Vec::new(),
        sibling_types: Vec::new(),
        parameters: Vec::new(),
        generalized_params: Vec::new(),
        index_params: Vec::new(),
        wf_measure: None,
        outer_locals_floor: None,
    });
    ctx
}

fn assert_later_expression_works(ctx: &mut ElabCtx<'_>, before: &ScopeContent) {
    let held = ctx
        .elaborate(&parse_expr("held").unwrap())
        .expect("original local remains usable after failure");
    assert_eq!(held, Expr::fvar(before.locals[0].1));
    let later = ctx
        .elaborate(&parse_expr("let later : Nat := 11; later").unwrap())
        .expect("same elaborator supports a new valid term let");
    assert!(matches!(later.kind(), ExprKind::Let(..)));
    assert!(!later.has_fvar_quick());
    assert!(!later.has_loose_bvar(0));
    let mut checker = TypeChecker::new(ctx.env);
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker.check_type(&later, &nat()).unwrap();
    assert!(!checker.heartbeat_spent());
    assert_eq!(scope_content(ctx), *before);
}

fn assert_unknown(error: ElabError, expected_name: &str) {
    let actual_name = match error {
        ElabError::UnknownIdent(name)
        | ElabError::UnknownIdentDeferred { name, .. }
        | ElabError::UnknownIdentWithSuggestions { name, .. } => name,
        other => panic!("actual failed body, not parser/resource failure: {other:?}"),
    };
    assert_eq!(actual_name, expected_name, "failure occurs inside the body");
}

#[test]
fn failed_inferred_term_let_body_restores_original_scope() {
    let env = Environment::with_prelude();
    let mut ctx = seeded_ctx(&env);
    let before = scope_content(&ctx);
    let fresh_before = ctx.next_fvar;
    let error = ctx
        .elaborate(&parse_expr("let leaked := 7; missing_term_let_body").unwrap())
        .unwrap_err();
    assert_unknown(error, "missing_term_let_body");
    assert_eq!(scope_content(&ctx), before);
    assert!(ctx
        .lookup_local(&SurfaceName::generated_path("leaked"))
        .is_none());
    assert!(ctx.next_fvar > fresh_before, "fresh IDs are not rewound");
    assert_later_expression_works(&mut ctx, &before);
}

#[test]
fn failed_term_have_restores_raw_values_and_opacity_with_capture_off_and_on() {
    for capture_enabled in [false, true] {
        let env = Environment::with_prelude();
        let mut ctx = seeded_ctx(&env);
        let retained = ctx.fresh_fvar();
        let marked = crate::tactic::have_value(Expr::nat_lit(23));
        ctx.push_local_let_with_fvar(
            SurfaceName::generated_path("retained_have"),
            retained,
            nat(),
            marked.clone(),
        );
        let capture = crate::term_info::TermInfoCapture::default();
        if capture_enabled {
            ctx.set_term_info_capture(Some(capture.clone()));
        }
        let before = scope_content(&ctx);
        for source in [
            "have leaked : Nat := 7; missing_term_have_body",
            "have leaked : Nat := 7; let nested : Nat := leaked; missing_term_have_body",
        ] {
            let generation = ctx.locals.generation();
            let cached = ctx.shared_local_ctx();
            assert!(cached
                .get(retained)
                .expect("retained have local")
                .value
                .is_none());
            assert_eq!(ctx.locals.let_value(retained), Some(&marked));
            let error = ctx
                .elaborate(&parse_expr(source).expect("actual term-have source parses"))
                .expect_err("the failed body must cause scope restoration");
            assert_unknown(error, "missing_term_have_body");
            assert_eq!(scope_content(&ctx), before);
            assert_ne!(ctx.locals.generation(), generation);
            assert_eq!(ctx.locals.let_value(retained), Some(&marked));
            assert!(ctx.locals.reduction_value(retained).is_none());
            let restored = ctx.shared_local_ctx();
            assert!(!std::sync::Arc::ptr_eq(&cached, &restored));
            assert!(restored
                .get(retained)
                .expect("restored have local")
                .value
                .is_none());
            for leaked in ["leaked", "nested"] {
                assert!(ctx
                    .lookup_local(&SurfaceName::generated_path(leaked))
                    .is_none());
            }
        }
        assert_later_expression_works(&mut ctx, &before);
        ctx.finish_term_info();
        if capture_enabled {
            assert!(
                !capture
                    .take()
                    .expect("enabled term capture finishes")
                    .is_empty(),
                "the capture-on case must observe actual later successful elaboration"
            );
        }
    }
}

#[test]
fn failed_expected_term_let_body_restores_original_scope_and_expected_type() {
    let env = Environment::with_prelude();
    let mut ctx = seeded_ctx(&env);
    ctx.current_expected_type = Some(Expr::const_str("Bool"));
    let before = scope_content(&ctx);
    let error = ctx
        .elaborate_with_expected_type(
            &parse_expr("let leaked : Nat := 7; missing_checked_let_body").unwrap(),
            Some(nat()),
        )
        .unwrap_err();
    assert_unknown(error, "missing_checked_let_body");
    assert_eq!(scope_content(&ctx), before);
    // Reset only the caller's prior expected-type request for this separate
    // valid inference query; the failed checked call already restored it.
    ctx.current_expected_type = None;
    let before = scope_content(&ctx);
    assert_later_expression_works(&mut ctx, &before);
}

#[test]
fn nested_failed_term_let_bodies_pop_every_binder() {
    let env = Environment::with_prelude();
    let mut ctx = seeded_ctx(&env);
    let before = scope_content(&ctx);
    let fresh_before = ctx.next_fvar;
    let error = ctx
        .elaborate(
            &parse_expr("let outer : Nat := 7; let inner : Nat := outer; missing_nested_let_body")
                .unwrap(),
        )
        .unwrap_err();
    assert_unknown(error, "missing_nested_let_body");
    assert_eq!(scope_content(&ctx), before);
    for name in ["outer", "inner"] {
        assert!(ctx
            .lookup_local(&SurfaceName::generated_path(name))
            .is_none());
    }
    assert!(ctx.next_fvar >= fresh_before + 2);
    assert_later_expression_works(&mut ctx, &before);
}

#[test]
fn failed_class_typed_term_let_preserves_preexisting_local_instances() {
    let env = Environment::with_prelude();
    let mut ctx = seeded_ctx(&env);
    // Exercise the real class-typed term-let push/pop branch, not merely an
    // ordinary Nat binder in a context that happens to contain an instance.
    ctx.instances_mut()
        .register_class(Name::from_string("Inhabited"), 1, Vec::new());
    let class_ty = Expr::app(
        Expr::const_(Name::from_string("Inhabited"), vec![Level::zero()]),
        nat(),
    );
    assert!(ctx.binder_is_local_instance(BinderInfo::Default, &class_ty));
    let before = scope_content(&ctx);
    let error = ctx
        .elaborate(
            &parse_expr(
                "let local_instance : Inhabited Nat := @Inhabited.mk Nat 0; missing_instance_let_body",
            )
            .unwrap(),
        )
        .unwrap_err();
    assert_unknown(error, "missing_instance_let_body");
    assert_eq!(scope_content(&ctx), before);
    assert_eq!(ctx.local_instances.len(), 1);
    assert_later_expression_works(&mut ctx, &before);
}

#[test]
fn failed_nonrecursive_let_rec_body_drops_only_its_auxiliary_local() {
    let env = Environment::with_prelude();
    let mut ctx = seeded_ctx(&env);
    let before = scope_content(&ctx);
    let error = ctx
        .elaborate(&parse_expr("let rec helper : Nat := 9; missing_auxiliary_let_body").unwrap())
        .unwrap_err();
    assert_unknown(error, "missing_auxiliary_let_body");
    assert_eq!(scope_content(&ctx), before);
    assert!(ctx
        .lookup_local(&SurfaceName::generated_path("helper"))
        .is_none());
    assert_eq!(ctx.aux_decl_locals.len(), 1);
    assert_later_expression_works(&mut ctx, &before);
}

#[test]
fn successful_ordinary_and_dependent_term_lets_stay_closed_and_kernel_checked() {
    let env = Environment::with_prelude();
    let mut ctx = seeded_ctx(&env);
    let before = scope_content(&ctx);
    let equality = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat(), Expr::nat_lit(7), Expr::nat_lit(7)],
    );
    for (source, expected) in [
        ("let x : Nat := 7; x", nat()),
        ("let x : Nat := 7; let y : Nat := x; y", nat()),
        (
            "let x : Nat := 7; let h : @Eq Nat x x := @Eq.refl Nat x; h",
            equality,
        ),
    ] {
        let expr = ctx
            .elaborate(&parse_expr(source).unwrap())
            .expect("successful ordinary/dependent term let");
        let ExprKind::Let(name, ty, value, _, nondependent) = expr.kind() else {
            panic!("source let must retain the canonical Let node: {expr:?}");
        };
        assert_eq!(name, &Name::from_string("x"));
        assert_eq!(ty.as_ref(), &nat());
        assert!(!nondependent);
        assert!(!expr.has_fvar_quick(), "no escaped locals: {source}");
        assert!(!expr.has_loose_bvar(0), "closed binders: {source}");
        let mut checker = TypeChecker::new(&env);
        checker.set_allow_unsafe(false);
        checker.set_allow_partial(false);
        assert!(checker.is_def_eq(value, &Expr::nat_lit(7)));
        checker.check_type(&expr, &expected).unwrap();
        assert!(!checker.heartbeat_spent());
        // Certification audits propositions, not a bare computational Nat
        // judgment. Audit the independently typed reflexive equality while
        // retaining the complete value and its declaration closure.
        let sort = checker.infer_type(&expected).unwrap();
        let ExprKind::Sort(level) = sort.kind() else {
            panic!("the independently checked result type must inhabit a sort");
        };
        let goal = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![level.clone()]),
            [expected.clone(), expr.clone(), expr.clone()],
        );
        let proof = Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![level.clone()]),
            [expected.clone(), expr.clone()],
        );
        checker
            .check_type(&goal, &Expr::sort(Level::zero()))
            .unwrap();
        checker.check_type(&proof, &goal).unwrap();
        assert!(env.audit_certification(&goal, &proof).is_certified());
        assert!(!checker.heartbeat_spent());
        assert!(!clean_kernel::tc::declaration_budget_exhausted());
        assert_eq!(scope_content(&ctx), before);
    }
}
