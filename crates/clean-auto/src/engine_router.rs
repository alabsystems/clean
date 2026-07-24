// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Per-goal engine router for [`crate::AutomationEngine`].
//!
//! Root capability this addresses: the historical pipeline ran a *fixed*
//! `smt → superposition → oracle` order (plus the recently-added induction lane)
//! for every goal. The solver-cache weak-area telemetry
//! ([`crate::solver_cache::analysis`]) measured the VBS − SBS gap and found that
//! the best engine for a goal is largely determined by the goal's *structure /
//! theory* — a per-class argmax router captures essentially all of that headroom
//! without a learned model.
//!
//! This module is a lightweight, deterministic classifier + engine orderer:
//!
//!   1. [`classify_goal`] reads the goal `Expr` and assigns a [`GoalClass`]
//!      (inductive / propositional / arithmetic / equational / general) from
//!      cheap structural features — no environment, no type inference.
//!   2. [`engine_plan`] turns a class into a *best-first* ordering of all four
//!      engines. Every plan is a permutation of the full engine set, so a
//!      misclassification only changes *order*, never *coverage* — the search
//!      still falls back to trying every engine.
//!
//! # Soundness
//!
//! The router is on the search side, with **zero** soundness weight: it only
//! decides the order in which engines are *attempted*. Each engine still emits a
//! proof term that the kernel re-checks downstream (`TypeChecker::infer_type` +
//! `is_def_eq`); reordering or even mis-ordering the attempts cannot make an
//! unsound proof accepted. The classifier never decides provability.

use clean_kernel::{Expr, ExprKind, Name};

/// One of the four proof engines the router can dispatch to, in the order they
/// are attempted within a [`engine_plan`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RoutedEngine {
    /// SMT bridge / DPLL(T) (equality, linear arithmetic, propositional).
    Smt,
    /// Structural-induction lane (`Nat.rec`), see [`crate::engine_induction`].
    Induction,
    /// Saturation-based superposition / paramodulation (equational rewriting).
    Superposition,
    /// Neural / LLM proof oracle (external; always attempted last).
    Oracle,
}

/// The structural / theory class of a goal, used to pick a best-first engine
/// ordering. Determined purely from the goal `Expr` by [`classify_goal`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum GoalClass {
    /// `∀ (n : Nat), P n` — needs the `Nat.rec` eliminator (induction first).
    Inductive,
    /// Top-level logical connective or an implication over a proposition
    /// (`P → Q`, `P ∧ Q`, …) — DPLL(T) handles the boolean structure (SMT first).
    Propositional,
    /// Carries an arithmetic operation/relation (`Nat.*` / `Int.* `/ `HAdd` …) —
    /// the SMT theory solver is strongest here (SMT first).
    Arithmetic,
    /// An equation `f(…) = g(…)` between *compound* terms with no arithmetic —
    /// superposition's paramodulation/rewriting is strongest (superposition first).
    Equational,
    /// No discriminating structure — keep the historical SMT-first order.
    General,
}

/// The canonical fallback order, used to fill a plan after its leading engine.
const CANONICAL: [RoutedEngine; 4] = [
    RoutedEngine::Smt,
    RoutedEngine::Induction,
    RoutedEngine::Superposition,
    RoutedEngine::Oracle,
];

/// Classify `goal` into a [`GoalClass`] from cheap structural features.
///
/// Precedence (first match wins): inductive → propositional → arithmetic →
/// equational → general. The order matters: `∀ (n:Nat), 0 + n = n` is inductive
/// (not arithmetic) because the leading `∀` over `Nat` is the dominating
/// feature, and `2 + 3 = 5` is arithmetic (not equational) because the
/// arithmetic symbol outranks the bare `Eq` head.
#[must_use]
pub fn classify_goal(goal: &Expr) -> GoalClass {
    let g = goal.strip_mdata();

    // 1. Inductive: leading `∀ (x : I …), _` where the domain `I` is a *data*
    //    type former (a `Const`-headed type that is not a logical
    //    connective/relation) — Nat, List, Bool, Option, Sum, a structure, …. The
    //    induction lane (`engine_induction`) fires on any registered non-mutual,
    //    index-free inductive, so the router leads with it for all of them, not
    //    just `Nat`. A `∀ (h : a = b), _` / `P → Q` keeps its `Const` head in the
    //    logical set and falls through to the propositional class below; a
    //    domain that is not a registered inductive merely costs one declined
    //    induction probe (the plan still tries every engine).
    if let ExprKind::Pi(_, dom, _) = g.kind() {
        if is_data_type_domain(dom) {
            return GoalClass::Inductive;
        }
    }

    // 2. Propositional: a top-level connective, or an implication whose
    //    antecedent is itself a proposition (`P → Q`).
    if is_propositional(g) {
        return GoalClass::Propositional;
    }

    // 3. Arithmetic: any arithmetic operation/relation symbol anywhere in the goal.
    if contains_arith_symbol(g, 0) {
        return GoalClass::Arithmetic;
    }

    // 4. Equational: an equation between compound (applied) terms.
    if is_compound_equation(g) {
        return GoalClass::Equational;
    }

    GoalClass::General
}

/// Best-first engine ordering for a [`GoalClass`].
///
/// Every returned array is a permutation of all four engines, so the search
/// "falls back to trying all" even on a misclassification. Only the inductive
/// and equational classes reorder; arithmetic / propositional / general keep the
/// historical SMT-first order (the router's win for those is that it does not
/// pay the induction/superposition probes ahead of SMT, which is already best).
#[must_use]
pub fn engine_plan(class: GoalClass) -> [RoutedEngine; 4] {
    match class {
        GoalClass::Inductive => plan_led_by(RoutedEngine::Induction),
        GoalClass::Equational => plan_led_by(RoutedEngine::Superposition),
        GoalClass::Propositional | GoalClass::Arithmetic | GoalClass::General => CANONICAL,
    }
}

/// Convenience: classify `goal` and return its best-first engine plan.
#[must_use]
pub fn route_goal(goal: &Expr) -> [RoutedEngine; 4] {
    engine_plan(classify_goal(goal))
}

/// Build a plan that leads with `primary`, then the remaining engines in
/// [`CANONICAL`] order.
fn plan_led_by(primary: RoutedEngine) -> [RoutedEngine; 4] {
    let mut plan = [primary; 4];
    let mut idx = 1;
    for engine in CANONICAL {
        if engine != primary {
            plan[idx] = engine;
            idx += 1;
        }
    }
    plan
}

/// `true` iff `e`'s application-spine head is a `Const` that is a *data* type
/// former — i.e. not one of the logical connective/relation heads
/// ([`ANTECEDENT_HEADS`], which already includes the connectives plus `Eq`/`Ne`/
/// the order relations). Used to spot `∀ (x : I …), _` over an inductive data
/// type so the router leads with the induction lane, while keeping `a = b → _`
/// and `P → Q` in the propositional class.
fn is_data_type_domain(e: &Expr) -> bool {
    head_const_name(e.strip_mdata()).is_some_and(|head| !ANTECEDENT_HEADS.contains(&head.as_str()))
}

/// Top-level logical connective heads: a goal headed by one of these *is*
/// propositional. `Eq`/`Ne`/inequalities are deliberately excluded — a goal that
/// is itself an (in)equation belongs to the arithmetic/equational classes (where
/// the theory solver / superposition own it), not the propositional class.
const CONNECTIVE_HEADS: &[&str] = &["And", "Or", "Not", "Iff", "Exists", "Xor", "False", "True"];

/// Heads that, when they head an implication's *antecedent*, mark the goal as a
/// propositional implication (`P → Q`). Includes the connectives plus the
/// relations that build a `Prop` (`Eq`, `Ne`, `≤`, `<`, …), so `a = b → …` and
/// `a ≤ b → …` route to the DPLL(T)/EUF engine first.
const ANTECEDENT_HEADS: &[&str] = &[
    "And", "Or", "Not", "Iff", "Exists", "Xor", "False", "True", "Eq", "Ne", "LE.le", "LT.lt",
    "GE.ge", "GT.gt",
];

/// `true` iff the goal's outermost structure is logical: a connective head, or a
/// `Pi` whose antecedent is a proposition (an implication `P → Q`).
fn is_propositional(g: &Expr) -> bool {
    if let Some(head) = head_const_name(g) {
        if CONNECTIVE_HEADS.contains(&head.as_str()) {
            return true;
        }
    }
    if let ExprKind::Pi(_, dom, _) = g.kind() {
        // An arrow `dom → body`: propositional when the antecedent is a
        // proposition (its head builds a `Prop`). Dependent `∀ (x : T), _` over
        // a data type `T` falls through to the other classes.
        if let Some(dom_head) = head_const_name(dom.strip_mdata()) {
            return ANTECEDENT_HEADS.contains(&dom_head.as_str());
        }
    }
    false
}

/// The name of the head constant of `e`'s application spine, if any.
fn head_const_name(e: &Expr) -> Option<String> {
    match e.strip_mdata().get_app_fn().kind() {
        ExprKind::Const(name, _) => Some(name.to_string()),
        _ => None,
    }
}

/// `true` iff any constant in `e` (to a bounded depth) is an arithmetic
/// operation or relation. Recognises the `Nat.`/`Int.` operation namespaces and
/// the heterogeneous `HAdd`/`HMul`/… operator classes.
fn contains_arith_symbol(e: &Expr, depth: u32) -> bool {
    const MAX_DEPTH: u32 = 24;
    if depth > MAX_DEPTH {
        return false;
    }
    match e.kind() {
        ExprKind::Const(name, _) => is_arith_name(&name.to_string()),
        ExprKind::App(f, a) => {
            contains_arith_symbol(f, depth + 1) || contains_arith_symbol(a, depth + 1)
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            contains_arith_symbol(ty, depth + 1) || contains_arith_symbol(body, depth + 1)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            contains_arith_symbol(ty, depth + 1)
                || contains_arith_symbol(val, depth + 1)
                || contains_arith_symbol(body, depth + 1)
        }
        ExprKind::MData(_, inner) => contains_arith_symbol(inner, depth),
        ExprKind::Proj(_, _, s) => contains_arith_symbol(s, depth + 1),
        _ => false,
    }
}

/// `true` iff `name` denotes an arithmetic operation or relation.
fn is_arith_name(name: &str) -> bool {
    // Arithmetic operation/relation namespaces. The bare type names (`Nat`,
    // `Int`) and the constructors (`Nat.zero`/`Nat.succ`) are intentionally NOT
    // treated as arithmetic on their own — they appear in inductive goals the
    // induction lane owns; a real arithmetic *operation* (`Nat.add`, `Nat.le`)
    // is what biases toward the SMT theory solver.
    const OP_PREFIXES: &[&str] = &[
        "Nat.add", "Nat.sub", "Nat.mul", "Nat.div", "Nat.mod", "Nat.pow", "Nat.le", "Nat.lt",
        "Nat.ble", "Nat.blt", "Nat.gcd", "Nat.max", "Nat.min", "Int.add", "Int.sub", "Int.mul",
        "Int.div", "Int.mod", "Int.le", "Int.lt", "Int.neg",
    ];
    const OP_CLASSES: &[&str] = &[
        "HAdd.hAdd",
        "HSub.hSub",
        "HMul.hMul",
        "HDiv.hDiv",
        "HMod.hMod",
        "HPow.hPow",
        "Add.add",
        "Sub.sub",
        "Mul.mul",
        "Div.div",
        "Neg.neg",
    ];
    OP_PREFIXES.iter().any(|p| name.starts_with(p)) || OP_CLASSES.contains(&name)
}

/// `true` iff `g` is `@Eq T L R` where at least one of `L`/`R` is an applied
/// (compound) term — the rewriting shape superposition is strongest on. A bare
/// atom equality `a = b` (both sides atoms) is *not* compound: EUF/SMT closes
/// those, so they stay in the SMT-first classes.
fn is_compound_equation(g: &Expr) -> bool {
    let head = g.get_app_fn();
    let args = g.get_app_args();
    let is_eq = matches!(head.kind(), ExprKind::Const(name, _) if *name == Name::from_string("Eq"));
    if !is_eq || args.len() != 3 {
        return false;
    }
    is_applied(args[1]) || is_applied(args[2])
}

/// `true` iff `e` (modulo mdata) is an application.
fn is_applied(e: &Expr) -> bool {
    matches!(e.strip_mdata().kind(), ExprKind::App(_, _))
}
