// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The access-law producer exposed this general conversion shape: a harmless
//! projection in one argument must not force evaluation of a shared symbolic
//! guard. These use checked local definitions, without a dependency on EvalIR.

use super::*;
use crate::elaborate_decl_and_register;
use clean_kernel::expr::BinderInfo;
use clean_parser::parse_decl;
use std::time::Instant;

fn register(env: &mut Environment, source_input: &str) {
    let source = source_input;
    // These are conversion fixtures, not native programs: Bool/custom recursors
    // require noncomputable declarations in Lean's source compiler.
    let source = source
        .strip_prefix("def ")
        .map(|rest| format!("noncomputable def {rest}"));
    let source = source.as_deref().unwrap_or(source_input);
    let declaration = parse_decl(source).expect("valid regression declaration");
    elaborate_decl_and_register(env, &declaration)
        .unwrap_or_else(|error| panic!("{source}\n{error}"));
}

fn guard_environment() -> Environment {
    let mut env = Environment::with_prelude();
    // These fixtures exercise checked kernel conversion. Generic Bool/custom
    // recursors have no Lean code generator implementation, so keep the actual
    // noncomputable source form rather than claiming native compilation.
    for source in [
        "inductive CongruenceLayout : Type where | mk (align : Nat) : CongruenceLayout",
        "def congruence_align (layout : CongruenceLayout) : Nat := @CongruenceLayout.rec (fun (_ : CongruenceLayout) => Nat) (fun (align : Nat) => align) layout",
        "def congruence_iszero (n : Nat) : Bool := @Nat.rec (fun (_ : Nat) => Bool) Bool.true (fun (_ : Nat) (_ : Bool) => Bool.false) n",
        "def congruence_pos (n : Nat) : Bool := @Nat.rec (fun (_ : Nat) => Bool) Bool.false (fun (_ : Nat) (_ : Bool) => Bool.true) n",
        "def congruence_eqb (a b : Nat) : Bool := @Bool.rec (fun (_ : Bool) => Bool) Bool.false (congruence_iszero (Nat.sub b a)) (congruence_iszero (Nat.sub a b))",
        "def congruence_ltb (a b : Nat) : Bool := congruence_pos (Nat.sub b a)",
        "def congruence_leb (a b : Nat) : Bool := Bool.or (congruence_ltb a b) (congruence_eqb a b)",
        "def congruence_effective_align (requested natural : Nat) : Nat := @Bool.rec (fun (_ : Bool) => Nat) requested natural (congruence_eqb requested 0)",
        "def congruence_pow2_go (fuel n : Nat) : Bool := @Nat.rec (fun (_ : Nat) => Nat -> Bool) (fun (_ : Nat) => Bool.false) (fun (_ : Nat) (ih : Nat -> Bool) => fun (x : Nat) => @Bool.rec (fun (_ : Bool) => Bool) (Bool.and (congruence_pos x) (Bool.and (congruence_eqb (Nat.mod x 2) 0) (ih (Nat.div x 2)))) Bool.true (congruence_eqb x 1)) fuel n",
        "def congruence_alignment (fuel a limit : Nat) : Bool := Bool.and (congruence_ltb a limit) (congruence_pow2_go fuel a)",
        // The actual byte accessibility predicate contains this symbolic-minus-
        // limit shape inside its range comparison, beside the alignment check.
        "noncomputable def congruence_access_guard (fuel base align limit : Nat) : Bool := Bool.and (congruence_pos base) (Bool.and (congruence_leb (Nat.add base 8) limit) (Bool.and (congruence_alignment fuel align limit) (congruence_eqb (Nat.mod base align) 0)))",
    ] {
        register(&mut env, source);
    }
    env
}

fn projection_guard(fuel: usize, limit: &str) {
    let mut env = guard_environment();
    let source = format!("def congruence_projection_guard (base requested : Nat)
      (h : @Eq Bool (congruence_access_guard {fuel} base (congruence_effective_align requested 8) {limit}) Bool.true) :
      @Eq Bool (congruence_access_guard {fuel} base (congruence_effective_align requested (congruence_align (CongruenceLayout.mk 8))) {limit}) Bool.true := h");
    eprintln!("projection_guard fuel={fuel} limit={limit} begin");
    let started = Instant::now();
    register(&mut env, &source);
    eprintln!(
        "projection_guard fuel={fuel} limit={limit} elaboration_ms={}",
        started.elapsed().as_millis()
    );
    let info = env
        .get_const(&Name::from_string("congruence_projection_guard"))
        .unwrap();
    let tc = TypeChecker::new(&env);
    let started = Instant::now();
    let inferred = tc
        .infer_type(info.value.as_ref().expect("real proof term"))
        .unwrap();
    assert!(tc.is_def_eq(&inferred, &info.type_));
    assert!(env.axiom_deps(&info.name).unwrap().is_empty());
    assert!(env.trust_marker_deps(&info.name).unwrap().is_empty());
    eprintln!(
        "projection_guard fuel={fuel} limit={limit} replay_ms={}",
        started.elapsed().as_millis()
    );
}

#[test]
fn rigid_congruence_symbolic_guard_projection_small() {
    projection_guard(8, "256");
}

#[test]
fn rigid_congruence_symbolic_guard_projection_word64() {
    projection_guard(64, "18446744073709551616");
}

fn ignored_argument_environment() -> Environment {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        "noncomputable def congruence_ignore (ignored result : Nat) : Nat := result",
    );
    env
}

fn ignored_argument(ignored: Expr, result: u64) -> Expr {
    Expr::app(
        Expr::app(Expr::const_str("congruence_ignore"), ignored),
        Expr::nat_lit(result),
    )
}

#[test]
fn rigid_congruence_ignored_argument_keeps_meta_unsolved() {
    let env = ignored_argument_environment();
    let mut metas = MetaState::new();
    let id = metas.fresh(Expr::const_str("Nat"));
    let left = ignored_argument(Expr::fvar(MetaState::to_fvar(id)), 2);
    let right = ignored_argument(Expr::nat_lit(19), 2);
    let generation = metas.generation();
    let mut unifier = Unifier::with_env(&mut metas, &env, LocalContext::new());
    assert!(matches!(unifier.unify(&left, &right), UnifyResult::Success));
    drop(unifier);
    assert_eq!(metas.generation(), generation);
    assert!(!metas.is_assigned(id));
}

#[test]
fn rigid_congruence_unequal_arguments_still_reduce_and_reject_unequal_results() {
    let env = ignored_argument_environment();
    let left = ignored_argument(Expr::nat_lit(7), 3);
    let same = ignored_argument(Expr::nat_lit(8), 3);
    let different = ignored_argument(Expr::nat_lit(8), 4);
    let mut metas = MetaState::new();
    let mut unifier = Unifier::with_env(&mut metas, &env, LocalContext::new());
    assert_eq!(unifier.rigid_congruence_context.get(), None);
    assert!(!unifier.try_rigid_congruence(&left, &same));
    assert_eq!(unifier.rigid_congruence_context.get(), None);
    assert!(matches!(unifier.unify(&left, &same), UnifyResult::Success));
    assert!(matches!(
        unifier.unify(&left, &different),
        UnifyResult::Failure(_)
    ));
    let tc = TypeChecker::new(&env);
    assert!(tc.is_def_eq(&left, &same));
    assert!(!tc.is_def_eq(&left, &different));
}

fn projected_eight() -> Expr {
    Expr::app(
        Expr::const_str("congruence_align"),
        Expr::app(Expr::const_str("CongruenceLayout.mk"), Expr::nat_lit(8)),
    )
}

fn successor(value: Expr) -> Expr {
    Expr::app(Expr::const_str("Nat.succ"), value)
}

#[test]
fn rigid_congruence_hidden_and_unknown_metas_decline_without_assignment() {
    let env = guard_environment();
    let left = successor(projected_eight());
    let right = successor(Expr::nat_lit(8));
    let mut metas = MetaState::new();
    let id = metas.fresh(Expr::const_str("Nat"));
    let mut ctx = LocalContext::new();
    ctx.push_let(
        Name::from_string("hidden"),
        Expr::const_str("Nat"),
        Expr::fvar(MetaState::to_fvar(id)),
    );
    let generation = metas.generation();
    let unifier = Unifier::with_env(&mut metas, &env, ctx);
    assert!(!unifier.try_rigid_congruence(&left, &right));
    drop(unifier);
    assert_eq!(metas.generation(), generation);
    assert!(!metas.is_assigned(id));

    // A public caller may supply a tagged FVar absent from this MetaState.
    let mut empty_metas = MetaState::new();
    let unknown = Expr::fvar(MetaState::to_fvar(id));
    let mut ctx = LocalContext::new();
    ctx.push_let(
        Name::from_string("unknown"),
        Expr::const_str("Nat"),
        unknown.clone(),
    );
    let unifier = Unifier::with_env(&mut empty_metas, &env, ctx);
    assert!(!unifier.try_rigid_congruence(&left, &right));
    drop(unifier);
    let unifier = Unifier::with_env(&mut empty_metas, &env, LocalContext::new());
    assert!(!unifier.try_rigid_congruence(&successor(unknown), &right));
}

#[test]
fn rigid_congruence_hidden_levels_and_temporary_binders_decline() {
    let env = guard_environment();
    let left = successor(projected_eight());
    let right = successor(Expr::nat_lit(8));
    let level = Level::param(Name::from_string("u_17"));
    let mut metas = MetaState::new();
    for value_hidden in [false, true] {
        let mut ctx = LocalContext::new();
        if value_hidden {
            ctx.push_let(
                Name::from_string("hidden"),
                Expr::const_str("Nat"),
                Expr::let_named(
                    Name::from_string("unused"),
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::sort(level.clone()),
                        Expr::const_str("Nat"),
                    ),
                    Expr::lam(
                        BinderInfo::Default,
                        Expr::sort(level.clone()),
                        Expr::nat_lit(8),
                    ),
                    Expr::nat_lit(8),
                    true,
                ),
            );
        } else {
            ctx.push(
                Name::from_string("hidden"),
                Expr::sort(level.clone()),
                BinderInfo::Default,
            );
        }
        let generation = metas.generation();
        let unifier = Unifier::with_env(&mut metas, &env, ctx);
        assert!(!unifier.try_rigid_congruence(&left, &right));
        drop(unifier);
        assert_eq!(metas.generation(), generation);
        assert_eq!(metas.instantiate_level(&level), level);
    }
    let unifier = Unifier::with_env(&mut metas, &env, LocalContext::new());
    assert_eq!(unifier.rigid_congruence_context.get(), None);
    assert!(unifier.try_rigid_congruence(&left, &right));
    assert_eq!(unifier.rigid_congruence_context.get(), Some(true));
    unifier.push_binder_local(&Expr::const_str("Nat")).unwrap();
    assert!(!unifier.try_rigid_congruence(&left, &right));
    unifier.pop_binder_local();
    assert!(unifier.try_rigid_congruence(&left, &right));
    drop(unifier);

    // A mismatched private pop must not let a replacement prefix borrow the
    // original prefix's cached eligibility just by restoring its length.
    let mut ctx = LocalContext::new();
    ctx.push(Name::anon(), Expr::const_str("Nat"), BinderInfo::Default);
    let unifier = Unifier::with_env(&mut metas, &env, ctx);
    {
        let checker = unifier.tc_cache.borrow();
        let checker = checker.as_ref().unwrap();
        let first = checker.local_context();
        let second = checker.local_context();
        assert_eq!(first.len(), 1);
        assert!(std::ptr::eq(&*first, &*second));
    }
    assert!(unifier.try_rigid_congruence(&left, &right));
    unifier.pop_binder_local();
    unifier.push_binder_local(&Expr::const_str("Nat")).unwrap();
    assert!(!unifier.try_rigid_congruence(&left, &right));
}

#[test]
fn rigid_congruence_transparency_and_protected_assignment_remain_unchanged() {
    let mut env = guard_environment();
    register(&mut env, "@[irreducible] def congruence_opaque : Nat := 8");
    let left = successor(projected_eight());
    let right = successor(Expr::nat_lit(8));
    let mut metas = MetaState::new();
    let unifier = Unifier::with_env_reducible(&mut metas, &env, LocalContext::new());
    assert!(!unifier.try_rigid_congruence(&left, &right));
    drop(unifier);
    let unifier = Unifier::with_env(&mut metas, &env, LocalContext::new());
    assert!(!unifier.try_rigid_congruence(&successor(Expr::const_str("congruence_opaque")), &right));
    drop(unifier);

    let id = metas.fresh(Expr::const_str("Nat"));
    let surface = Expr::app(
        Expr::app(Expr::const_str("Nat.land"), Expr::nat_lit(7)),
        Expr::nat_lit(3),
    );
    let mut unifier =
        Unifier::with_env(&mut metas, &env, LocalContext::new()).with_protected_heads();
    assert!(!unifier.try_rigid_congruence(
        &successor(surface.clone()),
        &successor(Expr::fvar(MetaState::to_fvar(id)))
    ));
    assert!(matches!(
        unifier.unify(
            &successor(surface.clone()),
            &successor(Expr::fvar(MetaState::to_fvar(id)))
        ),
        UnifyResult::Success
    ));
    drop(unifier);
    // Closed Nat.succ/bitwise arithmetic reduces before the protected-argument
    // branch. Compare with the exact old eager path, not an assumed spelling.
    let mut baseline_metas = MetaState::new();
    let baseline_id = baseline_metas.fresh(Expr::const_str("Nat"));
    let mut baseline =
        Unifier::with_env(&mut baseline_metas, &env, LocalContext::new()).with_protected_heads();
    let left = baseline.try_whnf(&successor(surface));
    let right = baseline.try_whnf(&successor(Expr::fvar(MetaState::to_fvar(baseline_id))));
    assert!(matches!(
        baseline.unify_core(&left, &right),
        UnifyResult::Success
    ));
    drop(baseline);
    assert_eq!(
        metas.get_assignment(id),
        baseline_metas.get_assignment(baseline_id)
    );
    assert_eq!(metas.get_assignment(id), Some(&Expr::nat_lit(3)));

    let mut ctx = LocalContext::new();
    let x = ctx.push(
        Name::from_string("x"),
        Expr::const_str("Nat"),
        BinderInfo::Default,
    );
    let outer = ctx.push(
        Name::from_string("outer"),
        Expr::pi(
            BinderInfo::Default,
            Expr::const_str("Nat"),
            Expr::const_str("Nat"),
        ),
        BinderInfo::Default,
    );
    let mut open_metas = MetaState::new();
    let open_id = open_metas.fresh_with_locals(
        Expr::const_str("Nat"),
        vec![(
            clean_parser::SurfaceName::generated_path("x"),
            x,
            Expr::const_str("Nat"),
        )],
    );
    let open_surface = Expr::app(
        Expr::app(Expr::const_str("Nat.land"), Expr::fvar(x)),
        Expr::nat_lit(3),
    );
    let mut unifier = Unifier::with_env(&mut open_metas, &env, ctx).with_protected_heads();
    assert!(matches!(
        unifier.unify(
            &Expr::app(Expr::fvar(outer), open_surface.clone()),
            &Expr::app(Expr::fvar(outer), Expr::fvar(MetaState::to_fvar(open_id)))
        ),
        UnifyResult::Success
    ));
    drop(unifier);
    assert_eq!(open_metas.get_assignment(open_id), Some(&open_surface));
}

#[test]
fn rigid_congruence_eligibility_limits_do_not_reject_inputs() {
    let mut env = ignored_argument_environment();
    let left = ignored_argument(Expr::nat_lit(7), 3);
    let right = ignored_argument(Expr::nat_lit(8), 3);
    let mut metas = MetaState::new();
    let unifier = Unifier::new(&mut metas);
    assert!(!unifier.try_rigid_congruence(&left, &right));
    drop(unifier);
    for _ in 0..129 {
        let id = metas.fresh(Expr::const_str("Nat"));
        assert!(metas.assign(id, Expr::nat_lit(0)));
    }
    let mut unifier = Unifier::with_env(&mut metas, &env, LocalContext::new());
    assert!(!unifier.try_rigid_congruence(&left, &right));
    assert!(matches!(unifier.unify(&left, &right), UnifyResult::Success));
    drop(unifier);
    let mut ctx = LocalContext::new();
    for _ in 0..129 {
        ctx.push(Name::anon(), Expr::const_str("Nat"), BinderInfo::Default);
    }
    let mut empty_metas = MetaState::new();
    let mut unifier = Unifier::with_env(&mut empty_metas, &env, ctx);
    assert!(!unifier.try_rigid_congruence(&left, &right));
    assert!(matches!(unifier.unify(&left, &right), UnifyResult::Success));
    drop(unifier);

    let parameters = (0..65)
        .map(|i| format!("(a{i} : Nat) "))
        .collect::<String>();
    register(
        &mut env,
        &format!("noncomputable def congruence_wide {parameters}: Nat := 3"),
    );
    let wide = |value| {
        (0..65).fold(Expr::const_str("congruence_wide"), |f, _| {
            Expr::app(f, Expr::nat_lit(value))
        })
    };
    let mut unifier = Unifier::with_env(&mut empty_metas, &env, LocalContext::new());
    assert!(!unifier.try_rigid_congruence(&wide(7), &wide(8)));
    assert!(matches!(
        unifier.unify(&wide(7), &wide(8)),
        UnifyResult::Success
    ));
}

#[test]
fn rigid_congruence_honors_checker_and_ambient_budget_exhaustion() {
    let env = guard_environment();
    let left = successor(projected_eight());
    let right = successor(Expr::nat_lit(8));
    let mut metas = MetaState::new();
    let unifier = Unifier::with_env(&mut metas, &env, LocalContext::new());
    unifier
        .tc_cache
        .borrow_mut()
        .as_mut()
        .unwrap()
        .set_heartbeat_limit(1);
    assert!(!unifier.try_rigid_congruence(&left, &right));
    assert!(unifier
        .tc_cache
        .borrow()
        .as_ref()
        .unwrap()
        .heartbeat_spent());
    assert_eq!(
        unifier
            .tc_cache
            .borrow()
            .as_ref()
            .unwrap()
            .heartbeat_limit(),
        1
    );

    drop(unifier);
    use clean_kernel::tc as decl_budget;
    struct ClearBudget;
    impl Drop for ClearBudget {
        fn drop(&mut self) {
            decl_budget::clear_declaration_budget();
        }
    }
    let unifier = Unifier::with_env(&mut metas, &env, LocalContext::new());
    decl_budget::set_declaration_budget(1);
    let _clear_budget = ClearBudget;
    assert!(!unifier.try_rigid_congruence(&left, &right));
    assert!(decl_budget::declaration_budget_exhausted());
    assert_eq!(decl_budget::declaration_budget_limit(), 1);
    assert_eq!(decl_budget::declaration_budget_remaining(), 0);
}

#[test]
fn rigid_congruence_ignored_argument_fallback_cost() {
    let env = ignored_argument_environment();
    let left = ignored_argument(Expr::nat_lit(7), 3);
    let right = ignored_argument(Expr::nat_lit(8), 3);
    let mut old_metas = MetaState::new();
    let mut old = Unifier::with_env(&mut old_metas, &env, LocalContext::new());
    let start = Instant::now();
    for _ in 0..2000 {
        // The old entry pipeline, kept as a component-level timing control.
        let old_left = old.metas.instantiate_levels(&old.metas.instantiate(&left));
        let old_right = old.metas.instantiate_levels(&old.metas.instantiate(&right));
        assert!(matches!(
            old.unify_core(&old.try_whnf(&old_left), &old.try_whnf(&old_right)),
            UnifyResult::Success
        ));
    }
    let old_elapsed = start.elapsed();
    let mut new_metas = MetaState::new();
    let mut new = Unifier::with_env(&mut new_metas, &env, LocalContext::new());
    let start = Instant::now();
    for _ in 0..2000 {
        assert!(matches!(new.unify(&left, &right), UnifyResult::Success));
    }
    eprintln!(
        "ignored-argument fallback2000 old_pipeline_us={} new_unify_us={}",
        old_elapsed.as_micros(),
        start.elapsed().as_micros()
    );
}

#[test]
fn rigid_congruence_constructor_cost() {
    let env = Environment::with_prelude();
    for count in [0, 16, 64, 129] {
        let mut ctx = LocalContext::new();
        for _ in 0..count {
            ctx.push(Name::anon(), Expr::const_str("Nat"), BinderInfo::Default);
        }
        let mut metas = MetaState::new();
        let start = Instant::now();
        for _ in 0..2000 {
            // Exact pre-optimization constructor steps, with the new private
            // admission field disabled. Both lanes include the caller's clone.
            let tc = TypeChecker::with_context(&env, ctx.clone());
            tc.set_honor_reducibility(true);
            let old = Unifier {
                metas: &mut metas,
                tc_cache: RefCell::new(Some(tc)),
                env: Some(&env),
                protect_heads: false,
                initial_context_len: ctx.len(),
                rigid_congruence_context: Cell::new(None),
                check_types_depth: Cell::new(0),
                unreduced_failures: Cell::new(0),
            };
            std::hint::black_box(old);
        }
        let old_elapsed = start.elapsed();
        let start = Instant::now();
        for _ in 0..2000 {
            std::hint::black_box(Unifier::with_env(&mut metas, &env, ctx.clone()));
        }
        eprintln!(
            "constructor2000 locals={count} old_us={} new_us={}",
            old_elapsed.as_micros(),
            start.elapsed().as_micros()
        );
    }
}
