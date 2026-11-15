// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Ordinary checked definitions expose the recursive App comparison boundary.
//! Test-only checker budgets distinguish structural comparison from expanding
//! a huge computation. No EvalIR dependency, opaque provider or runtime oracle.

use super::*;
use crate::elaborate_decl_and_register;
use crate::unify::MetaState;
use clean_kernel::{BinderInfo, Environment, Level, LocalContext, Name, TypeChecker};
use clean_parser::{parse_decl, SurfaceName};

const CHECKER_BUDGET: u32 = 512;

fn register(env: &mut Environment, source_input: &str) {
    let source = source_input;
    // These are conversion fixtures, not native programs: Bool/custom recursors
    // require noncomputable declarations in Lean's source compiler.
    let source = source
        .strip_prefix("def ")
        .map(|rest| format!("noncomputable def {rest}"));
    let source = source.as_deref().unwrap_or(source_input);
    let declaration = parse_decl(source).expect("valid fixed regression source");
    elaborate_decl_and_register(env, &declaration).expect("checked regression definition");
}

fn environment() -> Environment {
    let mut env = Environment::with_prelude();
    for source in [
        "def structural_first_pos (n : Nat) : Bool := @Nat.rec (fun (_ : Nat) => Bool) Bool.false (fun (_ : Nat) (_ : Bool) => Bool.true) n",
        "def structural_first_sub_ltb (a b : Nat) : Bool := structural_first_pos (Nat.sub b a)",
        "def structural_first_ltb (a b : Nat) : Bool := @Nat.rec (fun (_ : Nat) => Nat -> Bool) (fun (y : Nat) => structural_first_pos y) (fun (ap : Nat) (_ : Nat -> Bool) => fun (y : Nat) => @Nat.rec (fun (_ : Nat) => Bool) Bool.false (fun (yp : Nat) (_ : Bool) => structural_first_sub_ltb ap yp) y) a b",
        "def structural_first_div_go (fuel a b : Nat) : Nat := @Nat.rec (fun (_ : Nat) => Nat -> Nat) (fun (_ : Nat) => 0) (fun (_ : Nat) (ih : Nat -> Nat) => fun (x : Nat) => @Bool.rec (fun (_ : Bool) => Nat) (Nat.succ (ih (Nat.sub x b))) 0 (structural_first_ltb x b)) fuel a",
        // Same forcing context as arithmetic shift's closed sign fill. A plain
        // quotient exposes one Nat.succ in WHNF; subtraction needs its numeral.
        "def structural_first_slow (dividend divisor : Nat) : Nat := Nat.sub 18446744073709551616 (structural_first_div_go dividend dividend divisor)",
        "def structural_first_second (ignored result : Nat) : Nat := result",
        "def structural_first_folded (n : Nat) : Nat := Nat.succ n",
        "inductive StructuralFirstBox : Type where | mk (n : Nat) : StructuralFirstBox",
    ] {
        register(&mut env, source);
    }
    env
}

fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(Expr::const_str(name), args)
}

fn successor(value: u64) -> Expr {
    app("Nat.succ", [Expr::nat_lit(value)])
}

fn slow(dividend: u64, divisor: Expr) -> Expr {
    app("structural_first_slow", [Expr::nat_lit(dividend), divisor])
}

fn checker_budget(unifier: &Unifier<'_>) {
    unifier
        .tc_cache
        .borrow_mut()
        .as_mut()
        .expect("ordinary checker")
        .set_heartbeat_limit(CHECKER_BUDGET);
}

fn not_spent(unifier: &Unifier<'_>) {
    let checker = unifier.tc_cache.borrow();
    let checker = checker.as_ref().expect("ordinary checker");
    assert_eq!(checker.heartbeat_limit(), CHECKER_BUDGET);
    assert!(
        !checker.heartbeat_spent(),
        "success must not hide exhausted WHNF"
    );
}

fn strict_equality(env: &Environment, left: Expr, right: Expr) {
    let level = Level::succ(Level::zero());
    let goal = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![level.clone()]),
        [Expr::const_str("Nat"), left.clone(), right],
    );
    let proof = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![level]),
        [Expr::const_str("Nat"), left],
    );
    let mut checker = TypeChecker::new(env);
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker.set_heartbeat_limit(CHECKER_BUDGET);
    checker
        .check_type(&proof, &goal)
        .expect("independent full kernel check");
    assert!(!checker.heartbeat_spent());
    assert!(env.audit_certification(&goal, &proof).is_certified());
}

#[test]
fn ground_argument_spelling_does_not_expand_the_enclosing_computation() {
    let env = environment();
    let left = slow(u64::MAX, Expr::nat_lit(8));
    let right = slow(u64::MAX, successor(7));
    let mut metas = MetaState::new();
    let mut unifier = Unifier::with_env(&mut metas, &env, LocalContext::new());
    checker_budget(&unifier);
    assert!(matches!(
        unifier.unify_app_args(&left, &right),
        UnifyResult::Success
    ));
    not_spent(&unifier);
    strict_equality(&env, left.clone(), right);
    drop(unifier);

    // Same checked computation, fresh checker and identical budget: the old
    // leading WHNF really does consume the budget. Never run an unlimited wall.
    let mut baseline_metas = MetaState::new();
    let baseline = Unifier::with_env(&mut baseline_metas, &env, LocalContext::new());
    checker_budget(&baseline);
    let _ = baseline.try_whnf(&left);
    assert!(baseline
        .tc_cache
        .borrow()
        .as_ref()
        .unwrap()
        .heartbeat_spent());
    assert_eq!(
        baseline
            .tc_cache
            .borrow()
            .as_ref()
            .unwrap()
            .heartbeat_limit(),
        CHECKER_BUDGET
    );
}

#[test]
fn function_parts_reach_the_same_structural_argument_boundary() {
    let env = environment();
    let left_value = slow(u64::MAX, Expr::nat_lit(8));
    let right_value = slow(u64::MAX, successor(7));
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let left_function = Expr::apps(eq.clone(), [Expr::const_str("Nat"), left_value]);
    let right_function = Expr::apps(eq, [Expr::const_str("Nat"), right_value]);
    let argument = Expr::nat_lit(0);
    let left = Expr::app(left_function.clone(), argument.clone());
    let right = Expr::app(right_function.clone(), argument.clone());
    let mut metas = MetaState::new();
    let mut unifier = Unifier::with_env(&mut metas, &env, LocalContext::new());
    checker_budget(&unifier);
    assert!(matches!(
        unifier.unify_app_app_in_order(
            (&left, &right),
            (&left_function, &argument),
            (&right_function, &argument),
        ),
        UnifyResult::Success
    ));
    not_spent(&unifier);
}

#[test]
fn ground_false_arguments_and_ignored_arguments_keep_the_reduced_fallback() {
    let env = environment();
    // The quotients differ (24/8 =3, 24/9 =2), so their fills differ too.
    let left = slow(24, Expr::nat_lit(8));
    let wrong = slow(24, Expr::nat_lit(9));
    let mut metas = MetaState::new();
    let mut unifier = Unifier::with_env(&mut metas, &env, LocalContext::new());
    checker_budget(&unifier);
    assert!(matches!(
        unifier.unify_app_args(&left, &wrong),
        UnifyResult::Failure(_)
    ));
    not_spent(&unifier);
    assert!(!TypeChecker::new(&env).is_def_eq(&left, &wrong));
    let ignored = |first| {
        app(
            "structural_first_second",
            [Expr::nat_lit(first), Expr::nat_lit(2)],
        )
    };
    assert!(matches!(
        unifier.unify_app_args(&ignored(1), &ignored(9)),
        UnifyResult::Success
    ));
    assert!(unifier.unreduced_failures.get() > 0);
    not_spent(&unifier);
    strict_equality(&env, ignored(1), ignored(9));
    assert!(!unifier.unreduced_attempt_allowed(&Expr::nat_lit(1), &Expr::nat_lit(2)));
    assert!(!unifier.unreduced_attempt_allowed(
        &ignored(1),
        &app("structural_first_folded", [Expr::nat_lit(1)]),
    ));
    assert!(!unifier.unreduced_attempt_allowed(
        &ignored(1),
        &app("structural_first_second", [Expr::nat_lit(1)]),
    ));
}

#[test]
fn failed_structural_probe_rolls_back_before_solving_the_reduced_constraint() {
    let env = environment();
    let mut metas = MetaState::new();
    let id = metas.fresh(Expr::const_str("Nat"));
    let variable = Expr::fvar(MetaState::to_fvar(id));
    let left = app("structural_first_second", [variable.clone(), variable]);
    let right = app(
        "structural_first_second",
        [Expr::nat_lit(1), Expr::nat_lit(2)],
    );
    let mut unifier = Unifier::with_env(&mut metas, &env, LocalContext::new());
    assert!(unifier.unify_argument_unreduced(&left, &right));
    // The function-part probe first tries m :=1, fails the later leaf, and
    // rolls back. Its enclosing probe may then legitimately use WHNF to solve
    // the reduced constraint m =2. Assert that exact solution, not outer failure.
    assert!(unifier.unreduced_failures.get() > 0);
    assert!(
        unifier.metas.get_assignment(id) == Some(&Expr::nat_lit(2)),
        "the failed nested assignment to1 must not poison the valid solution2"
    );
    assert_eq!(
        unifier
            .tc_cache
            .borrow()
            .as_ref()
            .unwrap()
            .local_context_len(),
        0
    );
    assert_eq!(unifier.check_types_depth.get(), 0);
    assert!(matches!(
        unifier.unify_app_args(&left, &right),
        UnifyResult::Success
    ));
    drop(unifier);
    assert_eq!(metas.get_assignment(id), Some(&Expr::nat_lit(2)));
    strict_equality(&env, metas.instantiate(&left), right);
}

#[test]
fn failed_probe_reverts_fresh_expression_and_universe_assignments() {
    let env = environment();
    let mut metas = MetaState::new();
    let level = Level::param(Name::from_string("u_structural_first"));
    let initial_id = metas.fresh(Expr::const_str("Nat"));
    let next_id = metas.next_id;
    let mut unifier = Unifier::with_env(&mut metas, &env, LocalContext::new());
    assert!(!unifier.attempt_unreduced(|unifier| {
        assert!(unifier.metas.assign(initial_id, Expr::nat_lit(1)));
        let _ = unifier.metas.fresh(Expr::const_str("Nat"));
        assert!(matches!(
            unifier.unify_levels(&level, &Level::zero()),
            UnifyResult::Success
        ));
        unifier
            .metas
            .postpone_level_eq(level.clone(), Level::succ(Level::zero()));
        matches!(
            unifier.unify_core(&Expr::nat_lit(1), &Expr::nat_lit(2)),
            UnifyResult::Success
        )
    }));
    assert!(!unifier.metas.is_assigned(initial_id));
    assert_eq!(unifier.metas.iter().count(), 1);
    assert_eq!(unifier.metas.next_id, next_id);
    assert_eq!(unifier.metas.instantiate_level(&level), level);
    assert_eq!(unifier.metas.postponed_level_count(), 0);
    assert_eq!(unifier.unreduced_failures.get(), 1);
    assert_eq!(unifier.check_types_depth.get(), 0);
}

#[test]
fn flex_application_keeps_its_previous_folded_function_solution() {
    let env = environment();
    let mut context = LocalContext::new();
    let x = context.push(
        Name::from_string("x"),
        Expr::const_str("Nat"),
        BinderInfo::Default,
    );
    let argument = app("Nat.succ", [Expr::fvar(x)]);
    let mut metas = MetaState::new();
    let id = metas.fresh(Expr::arrow(Expr::const_str("Nat"), Expr::const_str("Nat")));
    let left = Expr::app(Expr::fvar(MetaState::to_fvar(id)), argument.clone());
    let right = app("structural_first_folded", [argument]);
    let mut unifier = Unifier::with_env(&mut metas, &env, context);
    assert!(matches!(
        unifier.unify_app_args(&left, &right),
        UnifyResult::Success
    ));
    drop(unifier);
    assert_eq!(
        metas.get_assignment(id),
        Some(&Expr::const_str("structural_first_folded"))
    );
}

#[test]
fn beta_flex_projection_first_and_ill_typed_projection_rollback_are_preserved() {
    let env = environment();
    let mut context = LocalContext::new();
    let predicate_type = Expr::arrow(Expr::const_str("StructuralFirstBox"), Expr::prop());
    let predicate = context.push(
        Name::from_string("P"),
        predicate_type.clone(),
        BinderInfo::Default,
    );
    let x = context.push(
        Name::from_string("x"),
        Expr::const_str("Nat"),
        BinderInfo::Default,
    );
    let argument = app("Nat.succ", [Expr::fvar(x)]);
    let mut metas = MetaState::new();
    let projection = metas.fresh(Expr::arrow(Expr::const_str("Nat"), Expr::const_str("Nat")));
    let redex = Expr::app(
        Expr::lam(
            BinderInfo::Default,
            Expr::const_str("Nat"),
            app("Nat.succ", [Expr::bvar(0)]),
        ),
        argument.clone(),
    );
    let flex = Expr::app(Expr::fvar(MetaState::to_fvar(projection)), argument.clone());
    let imitation = metas.fresh_with_locals(
        Expr::arrow(Expr::const_str("Nat"), Expr::prop()),
        vec![(
            SurfaceName::component("P", false),
            predicate,
            predicate_type,
        )],
    );
    let lambda = Expr::lam(
        BinderInfo::Default,
        Expr::const_str("Nat"),
        Expr::app(
            Expr::fvar(predicate),
            app("StructuralFirstBox.mk", [Expr::bvar(0)]),
        ),
    );
    let typed_redex = Expr::app(lambda.clone(), argument.clone());
    let typed_flex = Expr::app(Expr::fvar(MetaState::to_fvar(imitation)), argument);
    let mut unifier = Unifier::with_env(&mut metas, &env, context.clone());
    assert!(matches!(
        unifier.unify_app_args(&redex, &flex),
        UnifyResult::Success
    ));
    assert!(matches!(
        unifier.unify_app_args(&typed_redex, &typed_flex),
        UnifyResult::Success
    ));
    assert_eq!(unifier.check_types_depth.get(), 0);
    assert_eq!(
        unifier
            .tc_cache
            .borrow()
            .as_ref()
            .unwrap()
            .local_context_len(),
        context.len()
    );
    drop(unifier);
    assert_eq!(
        metas.get_assignment(projection),
        Some(&Expr::const_str("Nat.succ"))
    );
    assert_eq!(metas.get_assignment(imitation), Some(&lambda));
    let checker = TypeChecker::with_context(&env, context);
    checker
        .check_type(&lambda, &Expr::arrow(Expr::const_str("Nat"), Expr::prop()))
        .unwrap();
}

#[test]
fn spent_probe_cap_and_protected_bare_assignment_keep_existing_policy() {
    let env = environment();
    let mut metas = MetaState::new();
    let id = metas.fresh(Expr::const_str("Nat"));
    let surface = app("Nat.land", [Expr::nat_lit(7), Expr::nat_lit(3)]);
    let mut unifier =
        Unifier::with_env(&mut metas, &env, LocalContext::new()).with_protected_heads();
    assert!(matches!(
        unifier.unify_app_args(&surface, &Expr::fvar(MetaState::to_fvar(id))),
        UnifyResult::Success
    ));
    assert_eq!(unifier.metas.get_assignment(id), Some(&surface));
    unifier.unreduced_failures.set(MAX_UNREDUCED_FAILURES);
    assert!(!unifier.unify_argument_unreduced(
        &slow(u64::MAX, Expr::nat_lit(8)),
        &slow(u64::MAX, successor(7))
    ));
    assert_eq!(unifier.unreduced_failures.get(), MAX_UNREDUCED_FAILURES);
    assert!(matches!(
        unifier.unify_app_args(&slow(3, Expr::nat_lit(8)), &slow(3, successor(7))),
        UnifyResult::Success
    ));
    assert!(matches!(
        unifier.unify_app_args(&Expr::nat_lit(8), &successor(7)),
        UnifyResult::Success
    ));
    assert_eq!(unifier.metas.get_assignment(id), Some(&surface));
}

/// Lean's `tryHeuristic` guard for a GROUND pair: argument-by-argument first
/// only under a REGULAR definition head. `HMod.hMod` (a projection) is not: it
/// is unfolded and a ground `%` evaluates, where probing it descended into
/// `Nat.mod`'s unfolded body for a 128-bit operand and never returned
/// (`proof_irrel_tests`' multilimb row). A metavariable-free pair under a
/// regular head keeps the probe (rows above).
#[test]
fn ground_probe_needs_a_regular_definition_head() {
    let env = environment();
    let mut metas = MetaState::new();
    let mut unifier = Unifier::with_env(&mut metas, &env, LocalContext::new());
    let modulo = |x: u64| {
        app(
            "HMod.hMod",
            [Expr::const_str("Nat"), Expr::nat_lit(x), Expr::nat_lit(64)],
        )
    };
    assert!(
        unifier.same_regular_definition_head(&slow(1, Expr::nat_lit(8)), &slow(2, successor(7)))
    );
    assert!(!unifier.same_regular_definition_head(&modulo(3), &modulo(4)));
    assert!(!unifier.same_regular_definition_head(&slow(1, Expr::nat_lit(8)), &modulo(4)));
    // Not attempted at all: a declined probe is not a FAILED probe, so the
    // 64-failure budget is untouched (the old rule ran it, failed, counted it).
    assert!(!unifier.unify_argument_unreduced(&modulo(3), &modulo(4)));
    assert_eq!(unifier.unreduced_failures.get(), 0);
}
