// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! What omega's propositional layer lets the linear pipeline see.
//!
//! Lean 4.8's `omega` refutes only the facts `MetaProblem.addFact` collects
//! (`Lean/Elab/Tactic/Omega/Frontend.lean`): `Nat`/`Int` comparisons, `≠`,
//! `¬` of those, and divisibility by a literal, over linear combinations
//! whose non-linear subterms (`x * y`, `2 ^ c`, `x / y`) are opaque ATOMS.
//! It never reads `False`, an opaque `P` and its negation, or a `p → False`
//! as a contradiction, and it never multiplies two atoms.
//!
//! Clean's linear pipeline is broader than that — it has non-omega lanes that
//! use any hypothesis and reason through products once an equality pins a
//! factor. At the root that pipeline keeps its own verdict (the propositional
//! layer only adds to what it already proved), but everything the layer
//! builds — a case-split branch, a goal moved to `False`, a restated leaf — is
//! a context Lean's `omega` would read, so the pipeline is run there on
//! [`restrict_to_facts`]'s view: the target must itself be such a fact or
//! `False`, and every other proposition is cleared first. Clearing only
//! removes what a proof may use, so the view can refuse more than Lean, never
//! accept more through a hypothesis Lean does not read.

use std::collections::HashSet;

use clean_kernel::{Expr, ExprKind, FVarId};

use super::super::builtins_replace::mentions_fvar;
use super::super::decide_eq::match_ne;
use super::super::{
    is_false, match_and, match_eq, match_ge, match_gt, match_iff, match_le_any, match_lt_any,
    match_or,
};
use super::hyp_facts::{carrier_name, is_prop, match_not_app};
use super::{Goal, ProofState, TacticError, TacticResult};

/// Narrow the current goal to the facts Lean's `omega` reads, or refuse.
///
/// ENSURES: on `Ok`, the target is `False` or an atom-faithful fact
///   ([`is_omega_fact`]) and every remaining propositional local is one; on
///   `Err`, the state is unchanged (callers run this under a rollback point
///   anyway).
pub(super) fn restrict_to_facts(state: &mut ProofState) -> TacticResult {
    let goal = state.current_goal().cloned().ok_or(TacticError::NoGoals)?;
    let target = state.metas.instantiate(&goal.target);
    if !is_false(&target) && !is_omega_fact(&target) {
        return Err(refusal(
            "the goal is not a Nat/Int fact omega reads with Lean's atoms",
        ));
    }
    let clear: HashSet<FVarId> = goal
        .local_ctx
        .iter()
        .filter(|d| d.value.is_none())
        .filter(|d| {
            let ty = state.metas.instantiate(&d.ty);
            !is_omega_fact(&ty) && is_prop(state, &goal, &ty)
        })
        .map(|d| d.fvar)
        .collect();
    if clear.is_empty() {
        return Ok(());
    }
    // A cleared proof another kept local (or the target) depends on cannot be
    // removed; keeping it would hand the pipeline a fact Lean never reads.
    let pinned = clear.iter().any(|&fvar| {
        mentions_fvar(&target, fvar)
            || goal.local_ctx.iter().any(|d| {
                !clear.contains(&d.fvar)
                    && (mentions_fvar(&d.ty, fvar)
                        || d.value.as_ref().is_some_and(|v| mentions_fvar(v, fvar)))
            })
    });
    if pinned {
        return Err(refusal(
            "a hypothesis omega does not read is needed by another local",
        ));
    }
    if let Some(current) = state.goals.front_mut() {
        current.local_ctx.retain(|d| !clear.contains(&d.fvar));
    }
    state.invalidate_tc_cache();
    Ok(())
}

/// Whether Lean 4.8's instance search finds `Decidable prop`, read
/// structurally: `True`, `False`, a `Nat`/`Int` comparison or `≠`
/// (`Nat.decLe`, `Int.decEq`, ...), `¬`/`∧`/`∨`/`↔`/`→` of decidable
/// propositions (`instDecidableNot`, `instDecidableAnd`, ...), or a
/// proposition a local `Decidable` instance names. Anything else counts as
/// undecidable — the conservative side, where the goal is dropped and adds no
/// fact.
pub(super) fn lean_decidable(state: &ProofState, goal: &Goal, prop: &Expr) -> bool {
    if is_false(prop) || head_is(prop, "True") || is_comparison(prop) {
        return true;
    }
    if let Some(inner) = match_not_app(prop) {
        return lean_decidable(state, goal, &inner);
    }
    if let Some((p, q)) = match_and(prop)
        .or_else(|| match_or(prop))
        .or_else(|| match_iff(prop))
    {
        return lean_decidable(state, goal, &p) && lean_decidable(state, goal, &q);
    }
    if let ExprKind::Pi(_, dom, cod) = prop.kind() {
        if !cod.has_loose_bvars() && is_prop(state, goal, dom) && is_prop(state, goal, cod) {
            return lean_decidable(state, goal, dom) && lean_decidable(state, goal, cod);
        }
    }
    goal.local_ctx.iter().any(|d| {
        let ty = state.metas.instantiate(&d.ty);
        head_is(&ty, "Decidable") && ty.get_app_args().first().is_some_and(|p| **p == *prop)
    })
}

fn refusal(why: &str) -> TacticError {
    TacticError::ArithmeticFailed {
        tactic: "omega".into(),
        reason: format!("hypothesis case split: {why}"),
    }
}

/// A fact Lean's `omega` collects, with no subterm it would read as a
/// product of atoms: a `Nat`/`Int` comparison or `≠`, its `Not`, or `k ∣ e`
/// for a literal `k`. `¬` is the `Not` APPLICATION only: Lean reads
/// `p → False` as an implication (`¬p ∨ False`), not as `¬p`.
pub(super) fn is_omega_fact(ty: &Expr) -> bool {
    let atom = match_not_app(ty).unwrap_or_else(|| ty.clone());
    (is_comparison(&atom) || is_literal_dvd(&atom)) && !has_nonlinear(&atom)
}

fn is_comparison(ty: &Expr) -> bool {
    match_le_any(ty)
        .or_else(|| match_lt_any(ty))
        .or_else(|| match_ge(ty))
        .or_else(|| match_gt(ty))
        .or_else(|| match_eq(ty))
        .map(|(carrier, _, _)| carrier)
        .or_else(|| match_ne(ty).map(|(_, carrier, _, _)| carrier))
        .is_some_and(|carrier| carrier_name(&carrier).is_some())
}

/// `@Dvd.dvd C _ k e` over `Nat`/`Int` with a literal `k`.
fn is_literal_dvd(ty: &Expr) -> bool {
    let args = ty.get_app_args();
    head_is(ty, "Dvd.dvd")
        && args.len() == 4
        && carrier_name(args[0]).is_some()
        && is_numeral(args[2])
}

/// `true` when `e` contains a subterm Lean's `omega` reads as an opaque atom
/// built from other terms: a product with no literal factor, a division or
/// modulus by a non-literal, or a power that is not literal on both sides.
pub(super) fn has_nonlinear(e: &Expr) -> bool {
    let args = e.get_app_args();
    let (lhs, rhs) = match args.len() {
        n if n >= 2 => (args[n - 2], args[n - 1]),
        _ => return children_nonlinear(e),
    };
    let binary = |names: &[&str], arity: usize| args.len() == arity && head_in(e, names);
    let product = (binary(&["HMul.hMul"], 6) || binary(&["Mul.mul"], 4))
        || binary(&["Nat.mul", "Int.mul"], 2);
    let quotient = (binary(&["HDiv.hDiv", "HMod.hMod"], 6) || binary(&["Div.div", "Mod.mod"], 4))
        || binary(
            &[
                "Nat.div", "Nat.mod", "Int.div", "Int.mod", "Int.ediv", "Int.emod", "Int.fdiv",
                "Int.fmod", "Int.tdiv", "Int.tmod",
            ],
            2,
        );
    let power = binary(&["HPow.hPow"], 6)
        || binary(&["Pow.pow", "Monoid.npow"], 4)
        || binary(&["Nat.pow", "Int.pow"], 2);
    if (product && !is_numeral(lhs) && !is_numeral(rhs))
        || (quotient && !is_numeral(rhs))
        || (power && !(is_numeral(lhs) && is_numeral(rhs)))
    {
        return true;
    }
    children_nonlinear(e)
}

fn children_nonlinear(e: &Expr) -> bool {
    match e.kind() {
        ExprKind::App(f, a) => has_nonlinear(f) || has_nonlinear(a),
        ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => has_nonlinear(t) || has_nonlinear(b),
        ExprKind::Let(_, t, v, b, _) => has_nonlinear(t) || has_nonlinear(v) || has_nonlinear(b),
        ExprKind::MData(_, inner) | ExprKind::Proj(_, _, inner) => has_nonlinear(inner),
        _ => false,
    }
}

/// A closed numeral: a literal, `OfNat.ofNat _ n _`, a cast or negation of
/// one, or `+`/`-`/`*` of numerals. Anything else counts as non-literal (the
/// conservative side: a missed numeral only makes the view refuse).
fn is_numeral(e: &Expr) -> bool {
    if matches!(e.kind(), ExprKind::Lit(_))
        || (head_is(e, "Nat.zero") && e.get_app_args().is_empty())
    {
        return true;
    }
    let args = e.get_app_args();
    let Some(last) = args.last() else {
        return false;
    };
    if head_is(e, "OfNat.ofNat") && args.len() == 3 {
        return matches!(args[1].kind(), ExprKind::Lit(_));
    }
    let unary = [
        "Nat.succ",
        "Int.ofNat",
        "Int.negSucc",
        "Int.neg",
        "Neg.neg",
        "Nat.cast",
        "NatCast.natCast",
        "Int.cast",
        "IntCast.intCast",
    ];
    if head_in(e, &unary) {
        return is_numeral(last);
    }
    let binary = [
        "HAdd.hAdd",
        "HSub.hSub",
        "HMul.hMul",
        "Nat.add",
        "Nat.sub",
        "Nat.mul",
        "Int.add",
        "Int.sub",
        "Int.mul",
    ];
    if head_in(e, &binary) && args.len() >= 2 {
        return is_numeral(args[args.len() - 2]) && is_numeral(last);
    }
    false
}

fn head_is(e: &Expr, name: &str) -> bool {
    matches!(e.get_app_fn().kind(), ExprKind::Const(n, _) if n.to_string() == name)
}

fn head_in(e: &Expr, names: &[&str]) -> bool {
    matches!(e.get_app_fn().kind(), ExprKind::Const(n, _) if names.contains(&n.to_string().as_str()))
}
