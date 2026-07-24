// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Linarith proof reconstruction helpers.

use clean_kernel::expr::ExprKind;
use clean_kernel::{Expr, FVarId};

use super::arith_linarith::LinarithCertificate;
use super::arith_linarith_chain;
use super::arith_linarith_close::{try_close_contradictory_le_generic, wrap_false_elim};
use super::arith_linarith_scale::{choose_real_accumulation_mode, SortLeAcc};
use super::arithmetic::big_nat_to_i64;
use super::Goal;

/// Look up the type of a hypothesis FVarId from the goal's local context.
///
/// REQUIRES: `goal` is a valid goal
/// ENSURES: On `Some(ty)`, `fvar` exists in `goal.local_ctx` and `ty` is its type
/// ENSURES: On `None`, `fvar` is not in `goal.local_ctx`
pub(crate) fn find_hyp_type(goal: &Goal, fvar: FVarId) -> Option<Expr> {
    goal.local_ctx
        .iter()
        .find(|d| d.fvar == fvar)
        .map(|d| d.ty.clone())
}

/// Extract `(α, a, b)` from a comparison expression.
///
/// REQUIRES: `ty` is a well-formed kernel expression
/// ENSURES: On `Some((α, a, b))`, `ty` is `@{LE.le|LT.lt|GE.ge|GT.gt} α inst a b`
///   or a direct `{Nat|Int|Rat|Real}.{le|lt} a b` comparison.
/// ENSURES: On `None`, `ty` does not match a supported comparison expression
pub(crate) fn extract_le_args(ty: &Expr) -> Option<(Expr, Expr, Expr)> {
    let args = ty.get_app_args();
    // LE.le / LT.lt: 4 args = [α, inst, a, b]
    if args.len() == 4 {
        let fn_expr = ty.get_app_fn();
        if let ExprKind::Const(name, _) = fn_expr.kind() {
            let s = name.to_string();
            if s == "LE.le" || s == "LT.lt" || s == "GE.ge" || s == "GT.gt" {
                return Some((args[0].clone(), args[2].clone(), args[3].clone()));
            }
        }
    }
    if args.len() == 2 {
        let fn_expr = ty.get_app_fn();
        if let ExprKind::Const(name, _) = fn_expr.kind() {
            if let Some(alpha) = direct_comparison_sort(&name.to_string()) {
                return Some((alpha, args[0].clone(), args[1].clone()));
            }
        }
    }
    None
}

fn direct_comparison_sort(name: &str) -> Option<Expr> {
    let sort = match name {
        "Nat.le" | "Nat.lt" => "Nat",
        "Int.le" | "Int.lt" => "Int",
        "Rat.le" | "Rat.lt" => "Rat",
        "Real.le" | "Real.lt" => "Real",
        _ => return None,
    };
    Some(Expr::const_(clean_kernel::Name::from_string(sort), vec![]))
}

/// Prove a strict Int goal `Int.lt a (b + 1)` (surface `a < b + 1`) from a
/// single hypothesis `h : Int.le a b`, via `Int.add_le_add_right`.
///
/// `Int.lt a c` is DEFINITIONALLY `Int.le (a + 1) c` (the prelude defines
/// `Int.lt := fun a b => Int.le (a + 1) b`). So the registered lemma
/// `@Int.add_le_add_right a b h 1 : Int.le (a + 1) (b + 1)` is kernel-def-eq to
/// the goal `Int.lt a (b + 1)`. This builds that candidate only when the goal
/// is a strict `<` over `Int` whose LHS matches the hypothesis LHS; the caller's
/// `close_goal` re-checks it, so it is accepted iff the goal RHS is genuinely
/// `b + 1` — any other RHS, or a `≤`/false goal, is rejected (fail closed). The
/// analog of the Nat direct-inequality weakening prover, but Int has no
/// `Nat.le.step`, so it is proved from the registered Int order lemma instead.
///
/// REQUIRES: `hyp_lhs`, `hyp_rhs` are the args of `h : Int.le hyp_lhs hyp_rhs`.
/// ENSURES: On `Some(proof)`, `proof` is a candidate for `goal_target`;
///   soundness is guaranteed by the caller's `close_goal` kernel re-check.
fn try_int_lt_succ_weakening(
    goal_target: &Expr,
    h_proof: &Expr,
    hyp_lhs: &Expr,
    hyp_rhs: &Expr,
) -> Option<Expr> {
    // Goal head must be a strict `<` (surface `LT.lt` or direct `Int.lt`).
    let goal_head = goal_target.get_app_fn();
    let is_lt = matches!(goal_head.kind(), ExprKind::Const(n, _)
        if { let s = n.to_string(); s == "LT.lt" || s == "Int.lt" });
    if !is_lt {
        return None;
    }
    // Goal must be over `Int` with LHS matching the hypothesis LHS `a`.
    let (g_alpha, g_lhs, _g_rhs) = extract_le_args(goal_target)?;
    let is_int = matches!(g_alpha.kind(), ExprKind::Const(n, _) if n.to_string() == "Int");
    if !is_int || &g_lhs != hyp_lhs {
        return None;
    }
    // `1 : Int` as `Int.ofNat 1`; build `@Int.add_le_add_right a b h 1`.
    let one = Expr::app(
        Expr::const_(clean_kernel::Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(1),
    );
    let add_le = Expr::const_(
        clean_kernel::Name::from_string("Int.add_le_add_right"),
        vec![],
    );
    Some(Expr::app(
        Expr::app(
            Expr::app(Expr::app(add_le, hyp_lhs.clone()), hyp_rhs.clone()),
            h_proof.clone(),
        ),
        one,
    ))
}

/// Recognize a `1` Nat literal, in either raw (`Nat.Lit 1`) or `Nat.succ
/// Nat.zero` form.
fn is_nat_one(e: &Expr) -> bool {
    if let ExprKind::Lit(clean_kernel::expr::Literal::Nat(n)) = e.kind() {
        return big_nat_to_i64(n) == Some(1);
    }
    let head = e.get_app_fn();
    let args = e.get_app_args();
    if let ExprKind::Const(name, _) = head.kind() {
        if name.to_string() == "Nat.succ" && args.len() == 1 {
            let inner = args[0].get_app_fn();
            return matches!(inner.kind(), ExprKind::Const(n, _) if n.to_string() == "Nat.zero");
        }
    }
    false
}

/// Recognize the Int literal `1` as `Int.ofNat 1` or `@OfNat.ofNat Int 1 _`.
fn is_int_one_literal(e: &Expr) -> bool {
    let head = e.get_app_fn();
    let args = e.get_app_args();
    if let ExprKind::Const(name, _) = head.kind() {
        let s = name.to_string();
        if s == "Int.ofNat" && args.len() == 1 {
            return is_nat_one(args[0]);
        }
        // `@OfNat.ofNat Int <numeral> inst` — the numeral is the second arg.
        if s == "OfNat.ofNat" && args.len() >= 2 {
            return is_nat_one(args[1]);
        }
    }
    false
}

/// True iff `g_rhs` is structurally `hyp_rhs + 1` — an addition (`HAdd.hAdd`
/// or `Int.add`) whose left operand is `hyp_rhs` and whose right operand is a
/// `1` literal. Excludes the identity goal (bare `hyp_rhs`, no addition) so the
/// raw-hypothesis closer keeps handling `a ≤ b`, and excludes `b + k` (k ≠ 1),
/// which is requeued.
fn rhs_is_hyp_plus_one(g_rhs: &Expr, hyp_rhs: &Expr) -> bool {
    let head = g_rhs.get_app_fn();
    let is_add = matches!(head.kind(), ExprKind::Const(n, _)
        if { let s = n.to_string(); s == "HAdd.hAdd" || s == "Int.add" });
    if !is_add {
        return false;
    }
    let args = g_rhs.get_app_args();
    if args.len() < 2 {
        return false;
    }
    let left = args[args.len() - 2];
    let right = args[args.len() - 1];
    left == hyp_rhs && is_int_one_literal(right)
}

/// Prove a non-strict Int goal `Int.le a (b + 1)` (surface `a ≤ b + 1`) from a
/// single hypothesis `h : Int.le a b`, via `Int.le_trans` + `Int.le_self_add_one`.
///
/// `Int.le_self_add_one b : Int.le b (b + 1)`, so
/// `@Int.le_trans a b (b+1) h (Int.le_self_add_one b) : Int.le a (b + 1)` (both
/// are registered kernel theorems). This is the non-strict analog of
/// `try_int_lt_succ_weakening`. Unlike the strict case, `≤` has a raw-hypothesis
/// closer for the identity `a ≤ b`, so this fires ONLY when the goal RHS is
/// structurally `b + 1` (`rhs_is_hyp_plus_one`) — never on `a ≤ b` — to avoid
/// shadowing it. The caller's `close_goal` re-checks the candidate (fail closed),
/// so any non-`b+1` RHS that slips the structural guard is still rejected.
///
/// REQUIRES: `hyp_lhs`, `hyp_rhs` are the args of `h : Int.le hyp_lhs hyp_rhs`.
/// ENSURES: On `Some(proof)`, `proof` is a candidate for `goal_target`;
///   soundness is guaranteed by the caller's `close_goal` kernel re-check.
fn try_int_le_succ_weakening(
    goal_target: &Expr,
    h_proof: &Expr,
    hyp_lhs: &Expr,
    hyp_rhs: &Expr,
) -> Option<Expr> {
    // Goal head must be non-strict `≤` (surface `LE.le` or direct `Int.le`),
    // NOT `<` (that is `try_int_lt_succ_weakening`'s job).
    let goal_head = goal_target.get_app_fn();
    let is_le = matches!(goal_head.kind(), ExprKind::Const(n, _)
        if { let s = n.to_string(); s == "LE.le" || s == "Int.le" });
    if !is_le {
        return None;
    }
    let (g_alpha, g_lhs, g_rhs) = extract_le_args(goal_target)?;
    let is_int = matches!(g_alpha.kind(), ExprKind::Const(n, _) if n.to_string() == "Int");
    if !is_int || &g_lhs != hyp_lhs {
        return None;
    }
    if !rhs_is_hyp_plus_one(&g_rhs, hyp_rhs) {
        return None;
    }
    // `Int.le_self_add_one b : Int.le b (b + 1)`.
    let le_self = Expr::app(
        Expr::const_(
            clean_kernel::Name::from_string("Int.le_self_add_one"),
            vec![],
        ),
        hyp_rhs.clone(),
    );
    // `@Int.le_trans a b (b+1) h (Int.le_self_add_one b)`.
    let le_trans = Expr::const_(clean_kernel::Name::from_string("Int.le_trans"), vec![]);
    Some(Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(le_trans, hyp_lhs.clone()), hyp_rhs.clone()),
                g_rhs.clone(),
            ),
            h_proof.clone(),
        ),
        le_self,
    ))
}

/// Build a proof term from a linarith certificate.
pub(crate) fn build_linarith_proof(
    _state: &super::ProofState,
    goal: &Goal,
    certificate: &LinarithCertificate,
    hypothesis_fvars: &[FVarId],
) -> Option<Expr> {
    if certificate.coefficients.iter().all(|&c| c == 0) {
        tracing::debug!("build_linarith_proof: all-zero coefficients");
        return None;
    }

    let active: Vec<(usize, i128)> = certificate
        .coefficients
        .iter()
        .enumerate()
        .filter(|&(i, &c)| c > 0 && i < hypothesis_fvars.len())
        .map(|(i, &c)| (i, c))
        .collect();

    if active.is_empty() {
        tracing::debug!("build_linarith_proof: no active hypotheses");
        return None;
    }

    let goal_target = &goal.target;

    // Simple case: single hypothesis with coefficient 1
    if active.len() == 1 && active[0].1 == 1 {
        let (hyp_idx, _) = active[0];
        if hyp_idx < hypothesis_fvars.len() {
            let h_fvar = hypothesis_fvars[hyp_idx];
            let proof = Expr::fvar(h_fvar);
            if let Some(h_ty) = find_hyp_type(goal, h_fvar) {
                if let Some((alpha, lhs, rhs)) = extract_le_args(&h_ty) {
                    if let Some(sort) = arith_linarith_chain::detect_sort(&alpha) {
                        if let Some(closed) = try_close_contradictory_le_generic(
                            sort,
                            &proof,
                            &lhs,
                            &rhs,
                            goal_target,
                        ) {
                            return Some(closed);
                        }
                    }
                    // Int weakening: prove a strict goal `Int.lt a (b + 1)` from a
                    // single consistent hypothesis `h : Int.le a b` (the shape the
                    // contradiction-closer above cannot reach — it needs the
                    // negated goal, which the certificate excludes). See
                    // `try_int_lt_succ_weakening`. `close_goal` re-checks the
                    // candidate, so a wrong-shape goal is rejected (fail closed).
                    if let Some(w) = try_int_lt_succ_weakening(goal_target, &proof, &lhs, &rhs) {
                        return Some(w);
                    }
                    // B111: non-strict Int weakening `a ≤ b + 1` from `h : a ≤ b`
                    // (via Int.le_trans + Int.le_self_add_one). Fires only when the
                    // goal RHS is structurally `b + 1`, so the identity `a ≤ b`
                    // still falls through to the raw-hypothesis closer below.
                    if let Some(w) = try_int_le_succ_weakening(goal_target, &proof, &lhs, &rhs) {
                        return Some(w);
                    }
                }
            }
            return Some(proof);
        }
    }

    // Phase E.3 (#2422): sort-generic N-hypothesis le_trans chain.
    if active.iter().all(|&(_, c)| c == 1) && active.len() >= 2 {
        if let Some((proof, sort, chain_op, chain_lhs, chain_rhs)) =
            arith_linarith_chain::build_chain_proof(&active, hypothesis_fvars, goal)
        {
            if chain_op == arith_linarith_chain::CmpOp::Lt && chain_lhs == chain_rhs {
                let false_proof =
                    arith_linarith_chain::mk_lt_irrefl_false(sort, &chain_lhs, &proof);
                return Some(wrap_false_elim(false_proof, goal_target));
            }
            if let Some(closed) = try_close_contradictory_le_generic(
                sort,
                &proof,
                &chain_lhs,
                &chain_rhs,
                goal_target,
            ) {
                return Some(closed);
            }
            return Some(proof);
        }
    }

    // Combine coefficient-1 hypotheses with sort-generic addition.
    if active.iter().all(|&(_, c)| c == 1) && active.len() >= 2 {
        if let Some(proof) = build_add_le_add_proof(&active, hypothesis_fvars, goal) {
            return Some(proof);
        }
    }

    // Try to build proof with scaling for coefficients > 1
    if active.iter().any(|&(_, c)| c > 1) {
        if let Some(proof) = build_scaled_proof(&active, hypothesis_fvars, goal) {
            return Some(proof);
        }
    }

    tracing::debug!(
        active_count = active.len(),
        has_scaling = active.iter().any(|&(_, c)| c > 1),
        "build_linarith_proof: all proof-construction paths exhausted"
    );
    None
}

/// Combine coefficient-1 hypotheses with sort-generic addition.
pub(crate) fn build_add_le_add_proof(
    active: &[(usize, i128)],
    hypothesis_fvars: &[FVarId],
    goal: &Goal,
) -> Option<Expr> {
    if active.len() < 2 {
        return None;
    }
    for &(idx, _) in active {
        if idx >= hypothesis_fvars.len() {
            return None;
        }
    }
    let real_mode = choose_real_accumulation_mode(active, hypothesis_fvars, goal)?;
    let first_fvar = hypothesis_fvars[active[0].0];
    let mut acc = SortLeAcc::from_hypothesis(first_fvar, goal, real_mode)?;
    for &(idx, _) in &active[1..] {
        let h_fvar = hypothesis_fvars[idx];
        let next = SortLeAcc::from_hypothesis(h_fvar, goal, real_mode)?;
        acc = acc.combine(next)?;
    }
    if let Some(closed) =
        try_close_contradictory_le_generic(acc.sort, &acc.proof, &acc.lhs, &acc.rhs, &goal.target)
    {
        return Some(closed);
    }
    Some(acc.proof)
}

/// Build a proof with scaling for coefficients > 1.
pub(crate) fn build_scaled_proof(
    active: &[(usize, i128)],
    hypothesis_fvars: &[FVarId],
    goal: &Goal,
) -> Option<Expr> {
    if active.is_empty() {
        return None;
    }
    let real_mode = choose_real_accumulation_mode(active, hypothesis_fvars, goal)?;
    let mut accs: Vec<SortLeAcc> = Vec::new();
    for &(idx, coeff) in active {
        if idx >= hypothesis_fvars.len() {
            return None;
        }
        let h_fvar = hypothesis_fvars[idx];
        if coeff == 1 {
            accs.push(SortLeAcc::from_hypothesis(h_fvar, goal, real_mode)?);
        } else if coeff > 1 {
            accs.push(SortLeAcc::from_scaled(h_fvar, coeff, goal, real_mode)?);
        } else {
            return None;
        }
    }
    if accs.len() == 1 {
        let acc = accs.remove(0);
        if let Some(closed) = try_close_contradictory_le_generic(
            acc.sort,
            &acc.proof,
            &acc.lhs,
            &acc.rhs,
            &goal.target,
        ) {
            return Some(closed);
        }
        return Some(acc.proof);
    }
    let mut acc = accs.remove(0);
    for next in accs {
        acc = acc.combine(next)?;
    }
    if let Some(closed) =
        try_close_contradictory_le_generic(acc.sort, &acc.proof, &acc.lhs, &acc.rhs, &goal.target)
    {
        return Some(closed);
    }
    Some(acc.proof)
}
