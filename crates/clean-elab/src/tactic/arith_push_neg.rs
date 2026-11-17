// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Push negation and contraposition tactics
//!
//! - `push_neg`: Pushes negations inward through propositions (De Morgan's laws)
//! - `contrapose`: Transforms goals to their contrapositive form

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind};

mod proof_rewrite;
mod proof_rules;
mod proof_utils;

use proof_rewrite::contrapose_with_proof;
pub(crate) use proof_rewrite::{build_local_hyp_cast, push_neg_expr_with_proof};
use proof_utils::is_nat_type;

use super::{ProofState, TacticError, TacticResult};

// ============================================================================
// Push Negation (push_neg)
// ============================================================================

/// Push negations inward through a proposition.
///
/// Applies De Morgan's laws and other negation rules to push `¬` as
/// far inside a proposition as possible.
///
/// # Transformations
/// - `¬(P ∧ Q)` → `¬P ∨ ¬Q`
/// - `¬(P ∨ Q)` → `¬P ∧ ¬Q`
/// - `¬(P → Q)` → `P ∧ ¬Q`
/// - `¬(∀ x, P x)` → `∃ x, ¬P x`
/// - `¬(∃ x, P x)` → `∀ x, ¬P x`
/// - `¬¬P` → `P`
/// - `¬(a ≤ b)` → `b < a`
/// - `¬(a < b)` → `b ≤ a`
/// - `¬(a = b)` → `a ≠ b`
///
/// # Example
/// ```text
/// -- Goal: ¬(∀ x, P x ∧ Q x)
/// push_neg
/// -- Goal: ∃ x, ¬P x ∨ ¬Q x
/// ```
///
/// Returns `Err(NoGoals)` when there is no active goal.
/// REQUIRES: `state.goals` is non-empty when success is expected.
/// ENSURES: On `Ok(())`, the current goal target becomes `push_neg_expr` of
/// the instantiated original target.
/// ENSURES: Returns `Err(NoProgress)` when the target is unchanged; `Err(NoGoals)`
/// leaves `state` unchanged.
pub fn push_neg(state: &mut ProofState) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    // Get the current target
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.metas.instantiate(&goal.target);

    let result = push_neg_expr_with_proof(state, &goal, &target)?;

    if result.expr == target {
        return Err(TacticError::no_progress("push_neg"));
    }

    let eq_proof = result.proof.ok_or_else(|| {
        TacticError::TypeCheckFailed(
            "push_neg: rewrite changed the target but did not produce an equality proof".into(),
        )
    })?;
    state.replace_target_eq(result.expr, eq_proof)
}

/// Push negations inward in an expression
/// REQUIRES: `expr` is a well-formed proposition or proposition-containing expression.
/// ENSURES: Recognized negated connectives and inequalities are rewritten to
/// pushed-negation form and double negations are eliminated.
/// ENSURES: Unsupported negations stay encoded as `Not`, while non-negation
/// `Pi`/`App` nodes are rebuilt recursively.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn push_neg_expr(expr: &Expr, state: &mut ProofState) -> Expr {
    // Check if this is a negation: Not P or ¬P
    if let Some(inner) = match_not(expr) {
        // Double negation: ¬¬P → P
        if let Some(inner_inner) = match_not(&inner) {
            return push_neg_expr(&inner_inner, state);
        }

        // ¬(P ∧ Q) → ¬P ∨ ¬Q
        if let Some((p, q)) = match_and(&inner) {
            let pushed_p = push_neg_expr(&p, state);
            let not_p = make_not(&pushed_p);
            let pushed_q = push_neg_expr(&q, state);
            let not_q = make_not(&pushed_q);
            return make_or(&not_p, &not_q);
        }

        // ¬(P ∨ Q) → ¬P ∧ ¬Q
        if let Some((p, q)) = match_or(&inner) {
            let pushed_p = push_neg_expr(&p, state);
            let not_p = make_not(&pushed_p);
            let pushed_q = push_neg_expr(&q, state);
            let not_q = make_not(&pushed_q);
            return make_and(&not_p, &not_q);
        }

        // ¬(P → Q) → P ∧ ¬Q
        if let Some((p, q)) = match_implies(&inner) {
            let pushed_q = push_neg_expr(&q, state);
            let not_q = make_not(&pushed_q);
            return make_and(&p, &not_q);
        }

        // ¬(∀ x : A, P x) → ∃ x : A, ¬P x
        if let Some((binder_ty, body)) = match_forall_push_neg(&inner) {
            let pushed_body = push_neg_expr(&body, state);
            let not_body = make_not(&pushed_body);
            return make_exists_push_neg(&binder_ty, &not_body, state);
        }

        // ¬(∃ x : A, P x) → ∀ x : A, ¬P x
        if let Some((binder_ty, body)) = match_exists_push_neg(&inner) {
            let pushed_body = push_neg_expr(&body, state);
            let not_body = make_not(&pushed_body);
            return make_forall_push_neg(&binder_ty, &not_body);
        }

        // ¬(a ≤ b) → b < a. Both spellings, and the result keeps the spelling
        // the input had — see [`match_le_any`] / [`is_raw_nat_rel`].
        if let Some((_ty, a, b)) = match_le_any(&inner) {
            if is_nat_type(&_ty) {
                return if is_raw_nat_rel(&inner) {
                    nat_lt_raw(b, a)
                } else {
                    super::tc_app::nat_lt_tc(b, a)
                };
            }
        }

        // ¬(a < b) → b ≤ a
        if let Some((_ty, a, b)) = match_lt_any(&inner) {
            if is_nat_type(&_ty) {
                return if is_raw_nat_rel(&inner) {
                    nat_le_raw(b, a)
                } else {
                    super::tc_app::nat_le_tc(b, a)
                };
            }
        }

        // Can't push further - return as is
        return make_not(&inner);
    }

    // Not a negation - recurse into structure
    match expr.kind() {
        ExprKind::Pi(bi, dom, cod) if !is_prop(dom) => {
            // Forall: push_neg into body
            Expr::pi(*bi, (**dom).clone(), push_neg_expr(cod, state))
        }
        ExprKind::App(f, arg) => {
            // Recurse into applications
            Expr::app(push_neg_expr(f, state), push_neg_expr(arg, state))
        }
        _ => expr.clone(),
    }
}

/// Match a Not/negation expression
/// REQUIRES: `expr` is a well-formed expression tree.
/// ENSURES: Returns `Some(P)` only for direct `Not P` applications or the
/// arrow-to-`False` encoding of negation.
/// ENSURES: Returns `None` for non-negation expressions.
pub fn match_not(expr: &Expr) -> Option<Expr> {
    // Not P = P → False
    if let ExprKind::Pi(_, dom, cod) = expr.kind() {
        if is_false(cod) {
            return Some((**dom).clone());
        }
    }

    // Direct Not application
    if let ExprKind::App(f, arg) = expr.kind() {
        if let ExprKind::Const(name, _) = f.kind() {
            if name.to_string() == "Not" {
                return Some((**arg).clone());
            }
        }
    }

    None
}

/// Match the `Not` HEAD only, as Mathlib's `push_neg` does
/// (`transformNegationStep`: `whnfR e` then `Expr.not?`, which is
/// `e.app1? ``Not`). `whnfR` never turns an arrow into `Not`, so a
/// hypothesis or goal written `P → False` is not a negation to `push_neg`:
/// Mathlib leaves it as written. [`match_not`] reads both spellings and stays
/// for the tactics that want both.
/// REQUIRES: `expr` is a well-formed expression tree.
/// ENSURES: Returns `Some(P)` exactly for `Not P`, `None` otherwise. An
/// `MData` wrapper is not looked through here: the caller's traversal
/// descends into it and keeps it around the rewritten proposition.
pub(crate) fn match_not_head(expr: &Expr) -> Option<Expr> {
    match expr.kind() {
        ExprKind::App(f, arg) => match f.kind() {
            ExprKind::Const(name, _) if name.to_string() == "Not" => Some((**arg).clone()),
            _ => None,
        },
        _ => None,
    }
}

/// Match an And expression
/// REQUIRES: `expr` is a well-formed expression tree.
/// ENSURES: Returns `(lhs, rhs)` only for fully-applied `And lhs rhs` spines.
/// ENSURES: Returned expressions are clones of the matched arguments.
pub fn match_and(expr: &Expr) -> Option<(Expr, Expr)> {
    if let ExprKind::App(f1, q) = expr.kind() {
        if let ExprKind::App(f2, p) = f1.kind() {
            if let ExprKind::Const(name, _) = f2.kind() {
                if name.to_string() == "And" {
                    return Some(((**p).clone(), (**q).clone()));
                }
            }
        }
    }
    None
}

/// Match an Or expression
/// REQUIRES: `expr` is a well-formed expression tree.
/// ENSURES: Returns `(lhs, rhs)` only for fully-applied `Or lhs rhs` spines.
/// ENSURES: Returned expressions are clones of the matched arguments.
pub fn match_or(expr: &Expr) -> Option<(Expr, Expr)> {
    if let ExprKind::App(f1, q) = expr.kind() {
        if let ExprKind::App(f2, p) = f1.kind() {
            if let ExprKind::Const(name, _) = f2.kind() {
                if name.to_string() == "Or" {
                    return Some(((**p).clone(), (**q).clone()));
                }
            }
        }
    }
    None
}

/// Match an Iff expression (biconditional P ↔ Q)
/// REQUIRES: `expr` is a well-formed expression tree.
/// ENSURES: Returns `(lhs, rhs)` only for fully-applied `Iff lhs rhs` spines.
/// ENSURES: Returned expressions are clones of the matched arguments.
pub fn match_iff(expr: &Expr) -> Option<(Expr, Expr)> {
    if let ExprKind::App(f1, q) = expr.kind() {
        if let ExprKind::App(f2, p) = f1.kind() {
            if let ExprKind::Const(name, _) = f2.kind() {
                if name.to_string() == "Iff" {
                    return Some(((**p).clone(), (**q).clone()));
                }
            }
        }
    }
    None
}

/// Match an implication P → Q (where Q is not False)
/// REQUIRES: `expr` is a well-formed expression tree.
/// ENSURES: Returns `Some((P, Q))` only for proposition-domain `Pi`
/// expressions whose codomain is not `False`.
/// ENSURES: Negation encodings `P -> False` are rejected.
#[cfg_attr(not(test), allow(dead_code))]
fn match_implies(expr: &Expr) -> Option<(Expr, Expr)> {
    if let ExprKind::Pi(_, dom, cod) = expr.kind() {
        if is_prop(dom) && !is_false(cod) {
            return Some(((**dom).clone(), (**cod).clone()));
        }
    }
    None
}

/// Match a forall for push_neg: ∀ x : A, P x (where A is not Prop)
/// REQUIRES: `expr` is a well-formed expression tree.
/// ENSURES: Returns `(binder_ty, body)` only for `Pi` binders over
/// non-`Prop` domains.
/// ENSURES: Implication-style `Pi` nodes over propositions are rejected.
#[cfg_attr(not(test), allow(dead_code))]
fn match_forall_push_neg(expr: &Expr) -> Option<(Expr, Expr)> {
    if let ExprKind::Pi(_, dom, cod) = expr.kind() {
        if !is_prop(dom) {
            return Some(((**dom).clone(), (**cod).clone()));
        }
    }
    None
}

/// Match an exists for push_neg: ∃ x : A, P x
/// REQUIRES: `expr` is a well-formed expression tree.
/// ENSURES: Returns `(binder_ty, body)` only for `Exists ty (fun _ => body)`
/// spines.
/// ENSURES: Returns `None` for malformed or non-`Exists` applications.
fn match_exists_push_neg(expr: &Expr) -> Option<(Expr, Expr)> {
    // Exists α P = App (App (Const Exists) α) P
    if let ExprKind::App(f1, body) = expr.kind() {
        if let ExprKind::App(f2, ty) = f1.kind() {
            if let ExprKind::Const(name, _) = f2.kind() {
                if name.to_string() == "Exists" {
                    // body is a lambda: λ x : ty, P x
                    if let ExprKind::Lam(_, _lam_ty, lam_body) = body.kind() {
                        return Some(((**ty).clone(), (**lam_body).clone()));
                    }
                }
            }
        }
    }
    None
}

/// Match a ≤ comparison
/// REQUIRES: `expr` is a well-formed comparison expression.
/// ENSURES: Returns `(ty, lhs, rhs)` only for fully-applied `LE.le` spines.
/// ENSURES: Typeclass instance arguments are discarded.
pub fn match_le(expr: &Expr) -> Option<(Expr, Expr, Expr)> {
    let args = expr.get_app_args();
    if args.len() >= 4 {
        if let ExprKind::Const(name, _) = expr.get_app_fn().kind() {
            if name.to_string().contains("LE.le") {
                return Some((
                    args[args.len() - 4].clone(),
                    args[args.len() - 2].clone(),
                    args[args.len() - 1].clone(),
                ));
            }
        }
    }
    None
}

/// Match a < comparison
/// REQUIRES: `expr` is a well-formed comparison expression.
/// ENSURES: Returns `(ty, lhs, rhs)` only for fully-applied `LT.lt` spines.
/// ENSURES: Typeclass instance arguments are discarded.
pub fn match_lt(expr: &Expr) -> Option<(Expr, Expr, Expr)> {
    let args = expr.get_app_args();
    if args.len() >= 4 {
        if let ExprKind::Const(name, _) = expr.get_app_fn().kind() {
            if name.to_string().contains("LT.lt") {
                return Some((
                    args[args.len() - 4].clone(),
                    args[args.len() - 2].clone(),
                    args[args.len() - 1].clone(),
                ));
            }
        }
    }
    None
}

/// Match a RAW `Nat` comparison `Nat.le a b` / `Nat.lt a b` — the spelling that
/// names the kernel constant directly instead of going through the `LE`/`LT`
/// typeclass.
///
/// Both spellings denote the same proposition: `instLENat` / `instLTNat` are
/// reducible wrappers, so `@LE.le Nat instLENat a b` and `Nat.le a b` are
/// definitionally equal and the kernel accepts a proof of either against the
/// other. The argument is recorded in
/// `clean-kernel/src/env/nat_totality_proof.rs`'s module header, which is why
/// `Nat.not_lt` / `Nat.not_le` can be declared in one spelling and applied in
/// the other.
///
/// REQUIRES: `head` is `"Nat.le"` or `"Nat.lt"`.
/// ENSURES: Returns `(Nat, lhs, rhs)` only for an EXACTLY two-argument
/// application whose head is the named constant; the type component is the
/// `Nat` constant, which no typeclass argument carries in this spelling.
/// ENSURES: Returns `None` for every other head, arity or spelling — in
/// particular for the typeclass spine, which [`match_le`] / [`match_lt`] own.
fn match_nat_rel_raw(expr: &Expr, head: &str) -> Option<(Expr, Expr, Expr)> {
    let args = expr.get_app_args();
    if args.len() != 2 {
        return None;
    }
    let ExprKind::Const(name, _) = expr.get_app_fn().kind() else {
        return None;
    };
    if name.to_string() != head {
        return None;
    }
    Some((super::tc_app::nat_type(), args[0].clone(), args[1].clone()))
}

/// Match a `≤` comparison in EITHER spelling — the `LE.le` typeclass spine or
/// the raw `Nat.le a b` constant application.
///
/// Only the typeclass spelling was matched before this existed, so a
/// hypothesis written `Not (Nat.le x y)` was invisible to
/// `omega`'s negated-relation normalization and to `push_neg`; `omega` then
/// failed on goals it proves in the sugar spelling. See the sibling
/// [`match_lt_any`].
///
/// ENSURES: Returns exactly what [`match_le`] returns when that matches.
/// ENSURES: Otherwise returns the raw-spelling match, with `Nat` as the type.
pub(crate) fn match_le_any(expr: &Expr) -> Option<(Expr, Expr, Expr)> {
    match_le(expr).or_else(|| match_nat_rel_raw(expr, "Nat.le"))
}

/// Match a `<` comparison in EITHER spelling — the `LT.lt` typeclass spine or
/// the raw `Nat.lt a b` constant application.
///
/// ENSURES: Returns exactly what [`match_lt`] returns when that matches.
/// ENSURES: Otherwise returns the raw-spelling match, with `Nat` as the type.
pub(crate) fn match_lt_any(expr: &Expr) -> Option<(Expr, Expr, Expr)> {
    match_lt(expr).or_else(|| match_nat_rel_raw(expr, "Nat.lt"))
}

/// Build the raw `Nat.le lhs rhs` application.
///
/// ENSURES: Returns `App(App(Const("Nat.le", []), lhs), rhs)`.
pub(crate) fn nat_le_raw(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.le"), vec![]), lhs),
        rhs,
    )
}

/// Build the raw `Nat.lt lhs rhs` application.
///
/// ENSURES: Returns `App(App(Const("Nat.lt", []), lhs), rhs)`.
pub(crate) fn nat_lt_raw(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.lt"), vec![]), lhs),
        rhs,
    )
}

/// Whether `expr` is the RAW `Nat.le` / `Nat.lt` spelling rather than the
/// typeclass spine.
///
/// The rewrite built for a raw-spelled hypothesis must keep the raw head on
/// both sides of its `Eq`, so that the rewritten hypothesis matches a
/// raw-spelled goal syntactically rather than only definitionally.
///
/// ENSURES: `true` only for a two-argument application of `Nat.le` or `Nat.lt`.
pub(crate) fn is_raw_nat_rel(expr: &Expr) -> bool {
    match_nat_rel_raw(expr, "Nat.le").is_some() || match_nat_rel_raw(expr, "Nat.lt").is_some()
}

/// Match a ≥ comparison
/// REQUIRES: `expr` is a well-formed comparison expression.
/// ENSURES: Returns `(ty, lhs, rhs)` only for fully-applied `GE.ge` spines.
/// ENSURES: Typeclass instance arguments are discarded.
pub fn match_ge(expr: &Expr) -> Option<(Expr, Expr, Expr)> {
    let args = expr.get_app_args();
    if args.len() >= 4 {
        if let ExprKind::Const(name, _) = expr.get_app_fn().kind() {
            if name.to_string().contains("GE.ge") {
                return Some((
                    args[args.len() - 4].clone(),
                    args[args.len() - 2].clone(),
                    args[args.len() - 1].clone(),
                ));
            }
        }
    }
    None
}

/// Match a > comparison
/// REQUIRES: `expr` is a well-formed comparison expression.
/// ENSURES: Returns `(ty, lhs, rhs)` only for fully-applied `GT.gt` spines.
/// ENSURES: Typeclass instance arguments are discarded.
pub fn match_gt(expr: &Expr) -> Option<(Expr, Expr, Expr)> {
    let args = expr.get_app_args();
    if args.len() >= 4 {
        if let ExprKind::Const(name, _) = expr.get_app_fn().kind() {
            if name.to_string().contains("GT.gt") {
                return Some((
                    args[args.len() - 4].clone(),
                    args[args.len() - 2].clone(),
                    args[args.len() - 1].clone(),
                ));
            }
        }
    }
    None
}

/// Match an `=` comparison `@Eq ty lhs rhs`.
/// REQUIRES: `expr` is a well-formed equality expression.
/// ENSURES: Returns `(ty, lhs, rhs)` only for fully-applied `Eq` spines.
pub fn match_eq(expr: &Expr) -> Option<(Expr, Expr, Expr)> {
    let args = expr.get_app_args();
    if args.len() == 3 {
        if let ExprKind::Const(name, _) = expr.get_app_fn().kind() {
            if name.to_string() == "Eq" {
                return Some((args[0].clone(), args[1].clone(), args[2].clone()));
            }
        }
    }
    None
}

/// Check if expression is False
/// ENSURES: Returns `true` iff `expr` is the `False` constant.
pub fn is_false(expr: &Expr) -> bool {
    if let ExprKind::Const(name, _) = expr.kind() {
        return name.to_string() == "False";
    }
    false
}

/// Check if expression is Prop (very approximate)
/// REQUIRES: `expr` is well-formed.
/// ENSURES: Returns `true` only for `Sort 0` and the explicit `Prop`
/// constant.
/// ENSURES: Other proposition encodings may return `false`; this check is
/// intentionally approximate.
fn is_prop(expr: &Expr) -> bool {
    if let ExprKind::Sort(level) = expr.kind() {
        return level.is_zero();
    }
    // Also check for Prop constant
    if let ExprKind::Const(name, _) = expr.kind() {
        return name.to_string() == "Prop";
    }
    false
}

/// Make a Not expression
/// False, And, Or are not universe-polymorphic (Prop-level), so vec![] is correct.
/// REQUIRES: `p` is a proposition expression.
/// ENSURES: Returns `Not p`, with the `Not` head, as Mathlib's `push_neg`
/// states it (`¬(P ∨ Q)` becomes `¬P ∧ ¬Q`): simp reads a negation off that
/// head only, so the unfolded `p → False` left `push_neg at h; simp only [h]`
/// unable to rewrite `P` to `False`. `match_not` still reads both forms.
pub(crate) fn make_not(p: &Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Not"), vec![]), p.clone())
}

/// Make an And expression
/// REQUIRES: `p` and `q` are proposition expressions.
/// ENSURES: Returns the fully-applied Prop-level `And p q` expression.
fn make_and(p: &Expr, q: &Expr) -> Expr {
    let and_const = Expr::const_(Name::from_string("And"), vec![]);
    Expr::app(Expr::app(and_const, p.clone()), q.clone())
}

/// Make an Or expression
/// REQUIRES: `p` and `q` are proposition expressions.
/// ENSURES: Returns the fully-applied Prop-level `Or p q` expression.
fn make_or(p: &Expr, q: &Expr) -> Expr {
    let or_const = Expr::const_(Name::from_string("Or"), vec![]);
    Expr::app(Expr::app(or_const, p.clone()), q.clone())
}

/// Make a forall expression for push_neg
/// REQUIRES: `ty` and `body` form a well-typed dependent proposition.
/// ENSURES: Returns `Pi (_ : ty), body` with `BinderInfo::Default`.
fn make_forall_push_neg(ty: &Expr, body: &Expr) -> Expr {
    Expr::pi(BinderInfo::Default, ty.clone(), body.clone())
}

/// Make an exists expression for push_neg
/// Exists is universe-polymorphic (u_1), needs proper levels.
/// REQUIRES: `ty` and `body` form a well-typed dependent proposition in
/// `state`'s environment.
/// ENSURES: Returns `Exists ty (fun _ => body)` using
/// `state.mk_const_str("Exists")`.
#[cfg_attr(not(test), allow(dead_code))]
fn make_exists_push_neg(ty: &Expr, body: &Expr, state: &mut ProofState) -> Expr {
    let exists_const = state.mk_const_str("Exists");
    let lam = Expr::lam(BinderInfo::Default, ty.clone(), body.clone());
    Expr::app(Expr::app(exists_const, ty.clone()), lam)
}

// ============================================================================
// Contraposition (contrapose)
// ============================================================================

/// Contraposition tactic.
///
/// Transforms a goal of the form `P → Q` to `¬Q → ¬P` (the contrapositive).
/// This is often useful when the contrapositive is easier to prove.
///
/// # Example
/// ```text
/// -- Goal: P → Q
/// contrapose
/// -- Goal: ¬Q → ¬P
///
/// -- With hypothesis:
/// -- h : P → Q
/// -- Goal: R
/// contrapose h
/// -- h : ¬Q → ¬P
/// -- Goal: R
/// ```
///
/// Returns `Err(NoGoals)` when there is no active goal and
/// `Err(GoalMismatch)` when the target is not an implication.
/// REQUIRES: `state.goals` is non-empty when success is expected.
/// ENSURES: On `Ok(())`, the current goal target becomes `¬Q -> ¬P`.
/// ENSURES: On error, the current goal target is unchanged.
pub fn contrapose(state: &mut ProofState) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let target = state
        .current_goal()
        .ok_or(TacticError::NoGoals)?
        .target
        .clone();

    let (contrapositive, eq_proof) = contrapose_with_proof(state, &target)?;
    state.replace_target_eq(contrapositive, eq_proof)
}

/// Contraposition tactic applied to a hypothesis.
///
/// Transforms a hypothesis `h : P → Q` to `h : ¬Q → ¬P`.
///
/// Returns `Err(NoGoals)` when there is no active goal,
/// `Err(HypothesisNotFound)` for missing hypotheses, and `Err(GoalMismatch)`
/// for non-implication hypotheses.
/// REQUIRES: `hyp_name` names a local hypothesis when success is expected.
/// ENSURES: On `Ok(())`, only the named hypothesis type is rewritten to
/// `¬Q -> ¬P`.
/// ENSURES: On error, the goal target and local context are unchanged.
pub fn contrapose_hyp(
    state: &mut ProofState,
    hyp_name: &clean_parser::SurfaceName,
) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let hyp_decl = goal
        .local_ctx
        .iter()
        .rev()
        .find(|d| crate::tactic::pattern::names::hypothesis_named(&d.name, hyp_name))
        .ok_or_else(|| TacticError::HypothesisNotFound(hyp_name.to_string()))?;
    let hyp_decl = hyp_decl.clone();
    let (contrapositive, eq_proof) = contrapose_with_proof(state, &hyp_decl.ty)?;
    let hyp_cast = build_local_hyp_cast(
        state,
        &goal,
        &hyp_decl.ty,
        &contrapositive,
        eq_proof,
        hyp_decl.fvar,
    )?;
    state.replace_local_decl_with_cast(hyp_decl.fvar, contrapositive, hyp_cast)
}
