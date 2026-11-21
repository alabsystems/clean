// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Equation synthesis for definitions whose recursor minors carry their own
//! redex or `let` — the shapes the nested-head match lowering emits — with
//! every definition built by the production elaborator
//! (`elaborate_decl_and_register`) and `simp only [f] at h` run through it.
//!
//! trust-ir's `Semantics/Aggregate.lean` `seqMapNotList` is this shape
//! (`| .bool b :: rest => … | _ :: _ => …`); before the fix `simp only
//! [seqMapNotList] at h` left `h` as a stuck `List.rec … []`, where Lean
//! 4.8.0 has `Except.ok [] = Except.ok ys` (checked against the pinned binary
//! 2026-09-30).

use super::*;
use crate::ElabError;

fn register(env: &mut Environment, src: &str) -> Result<(), ElabError> {
    let patterns = crate::tactic::builtins::builtin_tactic_patterns();
    let decl = clean_parser::parse_decl_with_tactics(src, &patterns)
        .map_err(|e| ElabError::ParseError(e.to_string()))?;
    crate::elaborate_decl_and_register(env, &decl).map(|_| ())
}

fn register_ok(env: &mut Environment, src: &str) {
    if let Err(err) = register(env, src) {
        panic!("should elaborate and kernel-check:\n{src}\n{err:?}");
    }
}

/// `SimpV` plus two recursive definitions over `List SimpV`: `notListV`,
/// whose cons minor applies its fallback minor to the fields (a redex), and
/// `countB`, whose arms are exhaustive only jointly and are compiled as a
/// field decision tree whose pattern variables are `let` aliases.
fn nested_head_env() -> Environment {
    let mut env = Environment::with_prelude();
    clean_olean::declare_environment_world(&mut env, "v4.8.0").expect("historical oracle fixture");
    register_ok(
        &mut env,
        "inductive SimpV where\n  | int : Nat → Int → SimpV\n  | bool : Bool → SimpV",
    );
    register_ok(
        &mut env,
        "def notListV : List SimpV → Except String (List SimpV)
  | [] => .ok []
  | .bool b :: rest =>
    match notListV rest with
    | .ok rest' => .ok (.bool (!b) :: rest')
    | .error e  => .error e
  | _ :: _ => .error \"booleans\"",
    );
    register_ok(
        &mut env,
        "def countB : List SimpV → Nat
  | [] => 0
  | .bool _ :: rest => countB rest + 1
  | .int _ _ :: rest => countB rest",
    );
    env
}

fn mentions_const(e: &Expr, name: &Name) -> bool {
    match e.kind() {
        ExprKind::Const(n, _) => n == name,
        ExprKind::App(f, a) => mentions_const(f, name) || mentions_const(a, name),
        ExprKind::Lam(_, ty, b) | ExprKind::Pi(_, ty, b) => {
            mentions_const(ty, name) || mentions_const(b, name)
        }
        ExprKind::Let(_, ty, v, b, _) => {
            mentions_const(ty, name) || mentions_const(v, name) || mentions_const(b, name)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => mentions_const(inner, name),
        _ => false,
    }
}

/// `name`'s equations, or a panic naming the shape requirement that declined
/// them and printing the compiled value it was read from.
fn equations_of(env: &Environment, def: &str) -> Vec<SimpLemma> {
    let name = Name::from_string(def);
    synthesize_rec_def_equations_or_decline(env, &name).unwrap_or_else(|why| {
        let value = env
            .get_const(&name)
            .and_then(|decl| decl.value.as_ref())
            .map_or_else(|| "<no value>".to_string(), ToString::to_string);
        panic!("`{def}` must get its equation lemmas; declined: {why}\nvalue: {value}")
    })
}

#[test]
fn test_rec_equations_minor_with_redex_or_let_synthesizes_per_ctor() {
    let env = nested_head_env();
    let list_rec = Name::from_string("List.rec");
    for def in ["notListV", "countB"] {
        let name = Name::from_string(def);
        let eqs = equations_of(&env, def);
        assert_eq!(
            eqs.len(),
            2,
            "one equation per `List` constructor for `{def}`"
        );
        for eq in &eqs {
            assert!(
                !mentions_const(&eq.rhs, &list_rec),
                "`{def}`'s equation must not leak a raw recursor: {}",
                eq.rhs
            );
        }
        assert!(
            eqs.iter().any(|eq| mentions_const(&eq.rhs, &name)),
            "the cons equation folds the recursive call back to `{def}`"
        );
    }
}

/// The refusal of a `simp only [f] at h` probe must show `h` REWRITTEN to
/// `rewritten`. Both ways the rewrite can fail also mention `Except.ok`: the
/// delta-unfold leaves a stuck `List.rec … []`, and an equation that does not
/// fire leaves `simp at h: no progress made on … (f (List.nil …)) …`. So the
/// hypothesis itself is pinned, and neither the definition's name nor "no
/// progress" may appear (the probe theorems' names avoid the definitions').
fn assert_hypothesis_rewritten(err: &str, def: &str, rewritten: &str) {
    assert!(
        err.contains(rewritten)
            && !err.contains(def)
            && !err.contains("no progress")
            && !err.contains("List.rec"),
        "simp must rewrite `{def}` in `h` with its equation, to `{rewritten}…`: {err}"
    );
}

/// Through `simp only [notListV] at h`: the probe `exact absurd h (by intro
/// hh; exact hh)` is refused (by Lean too) and prints the rewritten
/// hypothesis, Lean's `Except.ok [] = Except.ok ys` (Clean prints the type
/// arguments), not a stuck `List.rec … []`.
#[test]
fn test_rec_equations_simp_at_hypothesis_rewrites_nested_head_def() {
    let mut env = nested_head_env();
    let probe = "theorem simp_probe (ys : List SimpV) (h : notListV [] = .ok ys) : True := by
  simp only [notListV] at h
  exact absurd h (by intro hh; exact hh)";
    let err = match register(&mut env, probe) {
        Ok(()) => panic!("the probe proves `False` from `h`; it must be refused"),
        Err(err) => format!("{err}"),
    };
    assert_hypothesis_rewritten(
        &err,
        "notListV",
        "Except.ok String (List SimpV) (List.nil SimpV) = Except.ok String (List SimpV) ",
    );
}

/// The refusal of a false twin: it must stay an open goal (not "no progress",
/// not some unrelated failure) and must not be registered.
fn assert_left_unsolved(env: &Environment, err: &str, name: &str) {
    assert!(
        err.contains("unsolved goals") && env.get_const(&Name::from_string(name)).is_none(),
        "`{name}` is false: it must be left as an unsolved goal and not registered: {err}"
    );
}

/// Goal side, through `simp only [notListV, h]`: the cons equation exposes the
/// recursive call `notListV rest`, which `h` then rewrites. The delta-unfold
/// leaves a stuck `List.rec` that `h` cannot match, so without a firing
/// equation the true claim is refused. Pinned Lean 4.8.0 (2026-10-07) accepts
/// `nl_cons` and leaves `nl_cons_bad` as an unsolved goal.
#[test]
fn test_rec_equations_simp_goal_rewrites_nested_head_recursive_call_closes() {
    let mut env = nested_head_env();
    register_ok(
        &mut env,
        "theorem nl_cons (b : Bool) (rest : List SimpV) (h : notListV rest = .ok []) :
    notListV (.bool b :: rest) = .ok [.bool (!b)] := by
  simp only [notListV, h]",
    );
    let err = match register(
        &mut env,
        "theorem nl_cons_bad (b : Bool) (rest : List SimpV) (h : notListV rest = .ok []) :
    notListV (.bool b :: rest) = .ok [.bool b] := by
  simp only [notListV, h]",
    ) {
        Ok(()) => panic!("`nl_cons_bad` drops the negation; the claim is false"),
        Err(err) => format!("{err}"),
    };
    assert_left_unsolved(&env, &err, "nl_cons_bad");
}

/// `addKList (k : Nat) : List Nat → …` — a parameter written BEFORE the
/// major. The match lowering generalizes it into the motive (`fun k x =>
/// List.rec … x k`, where Lean keeps it fixed), so the major is not followed
/// by its extras; trust-ir `Semantics/Aggregate.lean` `seqMapAddKList` is this
/// shape (ledger class (82), the half closed 2026-10-05).
fn generalized_prefix_env() -> Environment {
    let mut env = Environment::with_prelude();
    clean_olean::declare_environment_world(&mut env, "v4.8.0").expect("historical oracle fixture");
    register_ok(
        &mut env,
        "def addKList (k : Nat) : List Nat → Except String (List Nat)
  | [] => .ok []
  | x :: rest =>
    match addKList k rest with
    | .ok rest' => .ok ((x + k) :: rest')
    | .error e  => .error e",
    );
    env
}

#[test]
fn test_rec_equations_generalized_prefix_param_synthesizes_per_ctor() {
    let env = generalized_prefix_env();
    let name = Name::from_string("addKList");
    let list_rec = Name::from_string("List.rec");
    let eqs = equations_of(&env, "addKList");
    assert_eq!(eqs.len(), 2, "one equation per `List` constructor");
    for (eq, ctor) in eqs.iter().zip(["List.nil", "List.cons"]) {
        assert!(
            !mentions_const(&eq.rhs, &list_rec),
            "the equation must not leak a raw recursor: {}",
            eq.rhs
        );
        // `addKList k (c …)`: the parameter stays first, the constructor sits
        // at the major's position.
        let args = eq.lhs.get_app_args();
        assert_eq!(args.len(), 2, "the LHS applies `addKList` to both binders");
        assert!(
            matches!(args[0].kind(), ExprKind::BVar(_)),
            "the leading parameter stays a variable: {}",
            eq.lhs
        );
        assert!(
            matches!(args[1].get_app_fn().kind(), ExprKind::Const(c, _) if *c == Name::from_string(ctor)),
            "the major position holds `{ctor}`: {}",
            eq.lhs
        );
    }
    assert!(
        mentions_const(&eqs[1].rhs, &name),
        "the cons equation folds the recursive call back to `addKList`"
    );
}

/// Through `simp only [addKList] at h`: the probe is refused (by Lean too,
/// which prints `h : Except.ok [] = Except.ok ys`) and its message carries the
/// rewritten hypothesis, no longer a stuck `List.rec … [] 3`.
#[test]
fn test_rec_equations_simp_at_hypothesis_rewrites_generalized_prefix_def() {
    let mut env = generalized_prefix_env();
    let probe =
        "theorem simp_probe_prefix (ys : List Nat) (h : addKList 3 [] = .ok ys) : True := by
  simp only [addKList] at h
  exact absurd h (by intro hh; exact hh)";
    let err = match register(&mut env, probe) {
        Ok(()) => panic!("the probe proves `False` from `h`; it must be refused"),
        Err(err) => format!("{err}"),
    };
    assert_hypothesis_rewritten(
        &err,
        "addKList",
        "Except.ok String (List Nat) (List.nil Nat) = Except.ok String (List Nat) ",
    );
}

/// Goal side, through `simp only [addKList, h]`: the cons equation exposes
/// `addKList k rest` with the leading parameter in place, and `h` rewrites
/// it. Pinned Lean 4.8.0 (2026-10-07) accepts `ak_cons` and leaves
/// `ak_cons_bad` as an unsolved goal.
#[test]
fn test_rec_equations_simp_goal_rewrites_generalized_prefix_recursive_call_closes() {
    let mut env = generalized_prefix_env();
    register_ok(
        &mut env,
        "theorem ak_cons (k x : Nat) (rest : List Nat) (h : addKList k rest = .ok []) :
    addKList k (x :: rest) = .ok [x + k] := by
  simp only [addKList, h]",
    );
    let err = match register(
        &mut env,
        "theorem ak_cons_bad (k x : Nat) (rest : List Nat) (h : addKList k rest = .ok []) :
    addKList k (x :: rest) = .ok [x] := by
  simp only [addKList, h]",
    ) {
        Ok(()) => panic!("`ak_cons_bad` drops `+ k`; the claim is false"),
        Err(err) => format!("{err}"),
    };
    assert_left_unsolved(&env, &err, "ak_cons_bad");
}

/// The outermost application of the constant `name` inside `e`.
fn find_app_of<'e>(e: &'e Expr, name: &Name) -> Option<&'e Expr> {
    if matches!(e.get_app_fn().kind(), ExprKind::Const(n, _) if n == name) {
        return Some(e);
    }
    match e.kind() {
        ExprKind::App(f, a) => find_app_of(f, name).or_else(|| find_app_of(a, name)),
        ExprKind::Lam(_, ty, b) | ExprKind::Pi(_, ty, b) => {
            find_app_of(ty, name).or_else(|| find_app_of(b, name))
        }
        ExprKind::Let(_, ty, v, b, _) => find_app_of(ty, name)
            .or_else(|| find_app_of(v, name))
            .or_else(|| find_app_of(b, name)),
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => find_app_of(inner, name),
        _ => None,
    }
}

/// Whether `needle` occurs in `e` (no binder is crossed where this is used).
fn occurs_in(e: &Expr, needle: &Expr) -> bool {
    e == needle
        || match e.kind() {
            ExprKind::App(f, a) => occurs_in(f, needle) || occurs_in(a, needle),
            _ => false,
        }
}

/// The cons equation computes with the CHANGING argument the recursive call
/// passes: a definition whose recursive call increments its leading
/// parameter (`stepK (k + 1) rest`). The synthesized equation itself is
/// pinned — its right side applies `stepK` to an expression in `k` that is
/// not `k`, and to the tail binder, in that order — because the `simp only
/// [stepK]` theorem below would also close by delta-unfolding and `rfl`
/// without any equation (it passes on a build with no synthesis at all). That
/// theorem is still Lean 4.8.0's (accepted there, 2026-10-07), and the same
/// claim with the unchanged `k` — false — stays refused.
#[test]
fn test_rec_equations_generalized_prefix_param_changing_argument_folds_exactly() {
    let mut env = Environment::with_prelude();
    clean_olean::declare_environment_world(&mut env, "v4.8.0").expect("historical oracle fixture");
    register_ok(
        &mut env,
        "def stepK (k : Nat) : List Nat → List Nat
  | [] => []
  | x :: rest => (x + k) :: stepK (k + 1) rest",
    );
    let step_k = Name::from_string("stepK");
    let eqs = equations_of(&env, "stepK");
    assert_eq!(eqs.len(), 2, "one equation per `List` constructor");
    let cons = &eqs[1];
    let lhs_args = cons.lhs.get_app_args();
    assert_eq!(lhs_args.len(), 2, "`stepK k (x :: rest)`: {}", cons.lhs);
    let k = lhs_args[0].clone();
    let tail = lhs_args[1]
        .get_app_args()
        .last()
        .map(|tail| (*tail).clone())
        .unwrap_or_else(|| panic!("the major is `x :: rest`: {}", cons.lhs));
    let call = find_app_of(&cons.rhs, &step_k).unwrap_or_else(|| {
        panic!(
            "the cons RHS folds the recursive call to `stepK`: {}",
            cons.rhs
        )
    });
    let call_args = call.get_app_args();
    assert!(
        call_args.len() == 2
            && *call_args[0] != k
            && occurs_in(call_args[0], &k)
            && *call_args[1] == tail,
        "the folded call must be `stepK (k + 1) rest` (LHS {}): {}",
        cons.lhs,
        cons.rhs
    );
    register_ok(
        &mut env,
        "theorem stepK_cons (k x : Nat) (rest : List Nat) :
    stepK k (x :: rest) = (x + k) :: stepK (k + 1) rest := by
  simp only [stepK]",
    );
    let err = match register(
        &mut env,
        "theorem stepK_cons_bad (k x : Nat) (rest : List Nat) :
    stepK k (x :: rest) = (x + k) :: stepK k rest := by
  simp only [stepK]",
    ) {
        Ok(()) => panic!("`stepK k rest` is not the recursive call; the claim is false"),
        Err(err) => format!("{err}"),
    };
    assert!(
        env.get_const(&Name::from_string("stepK_cons_bad"))
            .is_none(),
        "a refused claim must not be registered: {err}"
    );
}

/// Class (82), the NON-recursive nested-head face — CLOSED by G40 (ledger
/// (110)). A non-recursive nested-head definition is lowered through
/// `List.casesOn`, so `simp only [firstBoolV] at h` delta-unfolds it; the
/// arm then reduces to `Except.error "none" = Except.ok b`, and Lean's
/// `simpCtorEq` in this explicitly selected historical world makes it
/// `False`, closing the goal. Pinned Lean 4.8.0 accepts
/// `firstBoolV_nil_false` (2026-10-07, `scratchpad/match-compile/v17/oracle/F.lean`).
#[test]
fn test_rec_equations_nonrecursive_nested_head_simp_at_refutes_class_82() {
    let mut env = nested_head_env();
    register_ok(
        &mut env,
        "def firstBoolV : List SimpV → Except String Bool
  | .bool b :: _ => .ok b
  | _ => .error \"none\"",
    );
    register_ok(
        &mut env,
        "theorem firstBoolV_nil_false (b : Bool) (h : firstBoolV [] = .ok b) : False := by
  simp only [firstBoolV] at h",
    );
}

/// The right-reason twin: the cons arm with a `.bool` head IS `.ok b`, so the
/// same simp cannot refute it and the claim stays refused — for Lean's
/// reason, the open goal (pinned Lean 4.8.0, review r4t v1: "unsolved goals
/// … h : True ⊢ False").
#[test]
fn test_rec_equations_nonrecursive_nested_head_true_arm_is_not_refuted() {
    let mut env = nested_head_env();
    register_ok(
        &mut env,
        "def firstBoolV : List SimpV → Except String Bool
  | .bool b :: _ => .ok b
  | _ => .error \"none\"",
    );
    let theorem = "theorem firstBoolV_bool_false (b : Bool) (h : firstBoolV [.bool b] = .ok b) : \
                   False := by
  simp only [firstBoolV] at h";
    let err = match register(&mut env, theorem) {
        Ok(()) => panic!("`firstBoolV [.bool b] = .ok b` holds; nothing may refute it"),
        Err(err) => format!("{err}"),
    };
    assert!(
        err.contains("unsolved goals")
            && err.contains("False")
            && env
                .get_const(&Name::from_string("firstBoolV_bool_false"))
                .is_none(),
        "refused because `False` stays open, as in Lean: {err}"
    );
}

/// `let x := e; pair x x`, `levels` deep over a constant: linear as written,
/// `≈ 3·2^levels` nodes once ζ-reduced (the shape a `let`-bound match
/// alternative takes, G76).
fn let_tower(levels: usize) -> Expr {
    let c = |name: &str| Expr::const_(Name::from_string(name), vec![]);
    let mut e = c("leaf");
    for _ in 0..levels {
        e = Expr::let_named(
            Name::from_string("x"),
            c("T"),
            e,
            Expr::app(Expr::app(c("pair"), Expr::bvar(0)), Expr::bvar(0)),
            false,
        );
    }
    e
}

/// `beta_normal` declines a ζ-reduct past `BETA_NORMAL_MAX_NODES` instead of
/// building it: trust-ir `simp [Pred.impliesFuel]` grew past 8 GB here.
#[test]
fn test_beta_normal_declines_an_exponential_zeta_reduct() {
    assert!(beta_normal(&let_tower(20)).is_none());
    let small = beta_normal(&let_tower(3)).expect("a small reduct is normalized");
    assert!(!matches!(small.kind(), ExprKind::Let(..)));
}

#[test]
fn test_polymorphic_rec_equations_preserve_recursive_calls() {
    let mut env = Environment::with_prelude();
    clean_olean::declare_environment_world(&mut env, "v4.8.0").expect("oracle fixture");
    register_ok(&mut env, "def polyPick {α : Type u} : List α → Nat → Option α\n  | [], _ => none\n  | a :: _, 0 => some a\n  | _ :: xs, i + 1 => polyPick xs i");
    let eqs = equations_of(&env, "polyPick");
    assert_eq!(eqs.len(), 2);
    assert!(eqs
        .iter()
        .any(|eq| mentions_const(&eq.rhs, &Name::from_string("polyPick"))));
    assert!(eqs
        .iter()
        .all(|eq| !mentions_const(&eq.rhs, &Name::from_string("List.rec"))));
    register_ok(&mut env, "theorem polyPick_step {α : Type u} (x : α) (xs : List α) (i : Nat) (h : polyPick xs i = none) : polyPick (x :: xs) (Nat.succ i) = none := by\n  simp only [polyPick, h]");
    register_ok(&mut env, "theorem polyPick_levels (x : Nat) (X : Type u) : polyPick [x] 0 = some x ∧ polyPick [X] 0 = some X := by\n  constructor <;> simp only [polyPick]");
    let bad = register(&mut env, "theorem polyPick_false {α : Type u} (x : α) (xs : List α) (i : Nat) (h : polyPick xs i = some x) : polyPick (x :: xs) (Nat.succ i) = none := by\n  simp only [polyPick, h]");
    assert!(bad.is_err(), "false recursive conclusion must be refused");
    assert!(env
        .get_const(&Name::from_string("polyPick_false"))
        .is_none());
}

#[test]
fn test_polymorphic_rec_equations_refuse_undeclared_universes() {
    let mut env = Environment::with_prelude();
    register_ok(
        &mut env,
        "def polyTail {α : Type u} : List α → List α\n  | [] => []\n  | _ :: xs => polyTail xs",
    );
    let name = Name::from_string("polyTail");
    let mut malformed = env.get_const(&name).expect("registered definition").clone();
    assert!(!malformed.level_params.is_empty());
    malformed.level_params.clear();
    env.add_constant_unchecked_for_test(malformed);
    assert!(matches!(
        synthesize_rec_def_equations_or_decline(&env, &name),
        Err("undeclared universe parameter")
    ));
}

#[path = "rec_equations_predicate_tests.rs"]
mod source_predicate;
