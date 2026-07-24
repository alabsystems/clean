// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Linarith-specific chain ordering and proof assembly.
//!
//! Low-level arithmetic proof builders (ArithSort, CmpOp, mk_chain_step,
//! mk_lt_irrefl_false, detect_sort, combine_ops) are shared from
//! [`clean_auto::arith_proof`]. This module keeps only the linarith-local
//! logic: hypothesis extraction, chain ordering, and proof assembly.
//!
//! Part of #2422 Phase E.3, consolidated in #2905.

use clean_kernel::expr::ExprKind;
use clean_kernel::{Expr, FVarId};

use super::Goal;

// Re-export shared types so existing callers (`arith_linarith_chain::CmpOp`, etc.) still resolve.
pub(crate) use clean_auto::arith_proof::{
    combine_ops, detect_sort, mk_chain_step, mk_lt_irrefl_false, ArithSort, CmpOp,
};

/// Detect the comparison operator from the function name of a LE/LT expression.
fn detect_cmp_op(fn_name: &str) -> Option<CmpOp> {
    match fn_name {
        "LE.le" | "GE.ge" => Some(CmpOp::Le),
        "LT.lt" | "GT.gt" => Some(CmpOp::Lt),
        _ => None,
    }
}

/// Extract (α, cmp_op, lhs, rhs) from a typeclass comparison or direct
/// `{Nat|Int|Rat|Real}.{le|lt}` comparison.
pub(crate) fn extract_le_args_full(ty: &Expr) -> Option<(Expr, CmpOp, Expr, Expr)> {
    let args = ty.get_app_args();
    if args.len() == 4 {
        let fn_expr = ty.get_app_fn();
        if let ExprKind::Const(name, _) = fn_expr.kind() {
            let op = detect_cmp_op(&name.to_string())?;
            return Some((args[0].clone(), op, args[2].clone(), args[3].clone()));
        }
    }
    if args.len() == 2 {
        let fn_expr = ty.get_app_fn();
        if let ExprKind::Const(name, _) = fn_expr.kind() {
            let name = name.to_string();
            let op = direct_cmp_op(&name)?;
            let alpha = direct_cmp_sort(&name)?;
            return Some((alpha, op, args[0].clone(), args[1].clone()));
        }
    }
    None
}

fn direct_cmp_op(name: &str) -> Option<CmpOp> {
    match name {
        "Nat.le" | "Int.le" | "Rat.le" | "Real.le" => Some(CmpOp::Le),
        "Nat.lt" | "Int.lt" | "Rat.lt" | "Real.lt" => Some(CmpOp::Lt),
        _ => None,
    }
}

fn direct_cmp_sort(name: &str) -> Option<Expr> {
    let sort = match name {
        "Nat.le" | "Nat.lt" => "Nat",
        "Int.le" | "Int.lt" => "Int",
        "Rat.le" | "Rat.lt" => "Rat",
        "Real.le" | "Real.lt" => "Real",
        _ => return None,
    };
    Some(Expr::const_(clean_kernel::Name::from_string(sort), vec![]))
}

/// Hypothesis info extracted for chain construction.
struct HypInfo {
    fvar: FVarId,
    sort: ArithSort,
    op: CmpOp,
    lhs: Expr,
    rhs: Expr,
}

/// Build an N-hypothesis le_trans chain proof.
///
/// For hypotheses that form a transitivity chain (h1.rhs == h2.lhs, etc.),
/// builds an iterative proof using the shared `mk_chain_step` builder.
///
/// Returns `(proof, sort, chain_op, chain_lhs, chain_rhs)` on success.
pub(crate) fn build_chain_proof(
    active: &[(usize, i128)],
    hypothesis_fvars: &[FVarId],
    goal: &Goal,
) -> Option<(Expr, ArithSort, CmpOp, Expr, Expr)> {
    let mut hyps: Vec<HypInfo> = Vec::with_capacity(active.len());
    for &(idx, _) in active {
        if idx >= hypothesis_fvars.len() {
            return None;
        }
        let fvar = hypothesis_fvars[idx];
        let ty = super::arith_linarith_proof::find_hyp_type(goal, fvar)?;
        let (alpha, op, lhs, rhs) = extract_le_args_full(&ty)?;
        let sort = detect_sort(&alpha)?;
        hyps.push(HypInfo {
            fvar,
            sort,
            op,
            lhs,
            rhs,
        });
    }

    let sort = hyps[0].sort;
    if !hyps.iter().all(|h| h.sort == sort) {
        return None;
    }

    let chain_order = find_chain_order(&hyps)?;

    let first = &hyps[chain_order[0]];
    let mut proof = Expr::fvar(first.fvar);
    let chain_lhs = first.lhs.clone();
    let mut chain_rhs = &first.rhs;
    let mut chain_op = first.op;

    for &ci in &chain_order[1..] {
        let h = &hyps[ci];
        let result_op = combine_ops(chain_op, h.op);
        proof = mk_chain_step_registered(
            sort,
            &chain_lhs,
            chain_rhs,
            &h.rhs,
            chain_op,
            h.op,
            &proof,
            &Expr::fvar(h.fvar),
        );
        chain_rhs = &h.rhs;
        chain_op = result_op;
    }

    Some((proof, sort, chain_op, chain_lhs, chain_rhs.clone()))
}

/// Build a transitivity chain step using only lemmas that
/// `Environment::with_prelude()` actually registers.
///
/// The shared [`mk_chain_step`] maps a strict-strict (`Lt`-`Lt`) step for `Nat`
/// and `Int` to `{Nat,Int}.lt_trans`, which the prelude does NOT register (an
/// env probe confirms both resolve to `UnknownConst`). Every other (op1, op2)
/// combination maps to a REGISTERED lemma, so we delegate those unchanged. For
/// the `Lt`-`Lt` case we rebuild the step from registered lemmas:
///
/// - `Int`: `a < b`, `b < c`  ⟹  `Int.lt_of_lt_of_le a b c h1 (Int.le_of_lt b c h2)`
///   (`Int.lt_of_lt_of_le` + `Int.le_of_lt` are both registered).
/// - `Nat`: `a < b`, `b < c`  ⟹  `Nat.lt_of_le_of_lt a b c (Nat.le_of_lt a b h1) h2`
///   (`Nat.lt_of_le_of_lt` + `Nat.le_of_lt` are registered; `Nat.lt_of_lt_of_le`
///   is not).
///
/// `Real`/`Rat` keep the shared lemma (unchanged behavior). The assembled term
/// is kernel-rechecked downstream, so a wrong reconstruction fails closed.
#[allow(clippy::too_many_arguments)]
fn mk_chain_step_registered(
    sort: ArithSort,
    a: &Expr,
    b: &Expr,
    c: &Expr,
    left_op: CmpOp,
    right_op: CmpOp,
    h1: &Expr,
    h2: &Expr,
) -> Expr {
    if matches!((left_op, right_op), (CmpOp::Lt, CmpOp::Lt)) {
        match sort {
            ArithSort::Int => {
                // Int.le_of_lt b c h2 : Int.le b c.
                let h2_le = mk_apply_c("Int.le_of_lt", &[b, c, h2]);
                // Int.lt_of_lt_of_le a b c h1 h2_le : Int.lt a c.
                return mk_apply_c("Int.lt_of_lt_of_le", &[a, b, c, h1, &h2_le]);
            }
            ArithSort::Nat => {
                // Nat.le_of_lt a b h1 : Nat.le a b.
                let h1_le = mk_apply_c("Nat.le_of_lt", &[a, b, h1]);
                // Nat.lt_of_le_of_lt a b c h1_le h2 : Nat.lt a c.
                return mk_apply_c("Nat.lt_of_le_of_lt", &[a, b, c, &h1_le, h2]);
            }
            ArithSort::Real | ArithSort::Rat => {}
        }
    }
    mk_chain_step(sort, a, b, c, left_op, right_op, h1, h2)
}

/// `@Name arg0 arg1 …` with no universe params (the order lemmas here are
/// non-polymorphic prelude theorems).
fn mk_apply_c(name: &str, args: &[&Expr]) -> Expr {
    Expr::apps(
        Expr::const_(clean_kernel::Name::from_string(name), vec![]),
        args.iter().map(|a| (*a).clone()),
    )
}

/// Find a valid chain ordering for hypotheses.
///
/// Returns indices into `hyps` such that hyps[order[i]].rhs == hyps[order[i+1]].lhs.
fn find_chain_order(hyps: &[HypInfo]) -> Option<Vec<usize>> {
    use std::collections::{HashMap, HashSet};

    let n = hyps.len();
    if n < 2 {
        return None;
    }

    // Use structural Expr equality (PartialEq + Hash) for chain matching.
    // Expr is Arc-backed so clone is O(1), and its Hash uses a cached 32-bit
    // hash with structural PartialEq for collision resolution.
    let mut forward: HashMap<Expr, Vec<(Expr, usize)>> = HashMap::new();
    let mut rhs_set: HashSet<Expr> = HashSet::new();
    let mut lhs_keys: Vec<Expr> = Vec::with_capacity(n);

    for (i, h) in hyps.iter().enumerate() {
        forward
            .entry(h.lhs.clone())
            .or_default()
            .push((h.rhs.clone(), i));
        rhs_set.insert(h.rhs.clone());
        lhs_keys.push(h.lhs.clone());
    }

    let maybe_start_idx = lhs_keys
        .iter()
        .enumerate()
        .find(|(_, lhs)| !rhs_set.contains(*lhs))
        .map(|(i, _)| i);
    let (start_idx, is_cycle) = maybe_start_idx.map(|i| (i, false)).unwrap_or((0, true));
    let start_lhs = lhs_keys[start_idx].clone();

    let mut chain: Vec<usize> = Vec::with_capacity(n);
    let mut used = vec![false; n];
    chain.push(start_idx);
    used[start_idx] = true;
    let mut current_rhs = hyps[start_idx].rhs.clone();

    for _ in 1..n {
        let neighbors = forward.get(&current_rhs)?;
        let &(ref next_rhs, idx) = neighbors.iter().find(|(_, idx)| !used[*idx])?;
        chain.push(idx);
        used[idx] = true;
        current_rhs = next_rhs.clone();
    }

    if chain.len() != n {
        return None;
    }
    if is_cycle && current_rhs != start_lhs {
        return None;
    }
    Some(chain)
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::name::Name;

    fn mk_var(name: &str) -> Expr {
        Expr::const_(Name::from_string(name), vec![])
    }

    fn mk_hyp(fvar_idx: u64, sort: ArithSort, op: CmpOp, lhs: Expr, rhs: Expr) -> HypInfo {
        HypInfo {
            fvar: FVarId::new(fvar_idx),
            sort,
            op,
            lhs,
            rhs,
        }
    }

    /// Build `@LE.le α inst a b` (4-arg application).
    fn mk_le_type(alpha: &Expr, a: &Expr, b: &Expr) -> Expr {
        let le = Expr::const_(Name::from_string("LE.le"), vec![]);
        let inst = Expr::const_(Name::from_string("inst"), vec![]);
        Expr::app(
            Expr::app(Expr::app(Expr::app(le, alpha.clone()), inst), a.clone()),
            b.clone(),
        )
    }

    fn mk_test_goal(hyps: &[(FVarId, Expr)]) -> Goal {
        use crate::tactic::LocalDecl;
        use crate::unify::MetaId;
        let local_ctx = hyps
            .iter()
            .enumerate()
            .map(|(i, (fvar, ty))| LocalDecl {
                fvar: *fvar,
                name: format!("h{i}"),
                ty: ty.clone(),
                value: None,
            })
            .collect();
        Goal {
            meta_id: MetaId(0),
            target: Expr::const_(Name::from_string("False"), vec![]),
            local_ctx,
            tag: None,
        }
    }

    /// 3-node linear chain: a ≤ b, b ≤ c, c ≤ d → order [0, 1, 2].
    #[test]
    fn test_find_chain_order_linear_3_node() {
        let a = mk_var("a");
        let b = mk_var("b");
        let c = mk_var("c");
        let d = mk_var("d");
        let hyps = vec![
            mk_hyp(0, ArithSort::Int, CmpOp::Le, a, b.clone()),
            mk_hyp(1, ArithSort::Int, CmpOp::Le, b, c.clone()),
            mk_hyp(2, ArithSort::Int, CmpOp::Le, c, d),
        ];
        let order = find_chain_order(&hyps).expect("linear chain should produce an ordering");
        assert_eq!(order.len(), 3);
        // Verify chain connectivity: hyps[order[i]].rhs == hyps[order[i+1]].lhs
        for w in order.windows(2) {
            assert_eq!(
                hyps[w[0]].rhs, hyps[w[1]].lhs,
                "chain break at order indices [{}, {}]",
                w[0], w[1]
            );
        }
    }

    /// Cyclic chain: a < b, b ≤ c, c < a → ends back at start.
    #[test]
    fn test_find_chain_order_cyclic_3_node() {
        let a = mk_var("a");
        let b = mk_var("b");
        let c = mk_var("c");
        let hyps = vec![
            mk_hyp(0, ArithSort::Nat, CmpOp::Lt, a.clone(), b.clone()),
            mk_hyp(1, ArithSort::Nat, CmpOp::Le, b, c.clone()),
            mk_hyp(2, ArithSort::Nat, CmpOp::Lt, c, a),
        ];
        let order = find_chain_order(&hyps).expect("cyclic chain should produce an ordering");
        assert_eq!(order.len(), 3);
        // Verify cyclic connectivity: last rhs == first lhs
        let first = &hyps[order[0]];
        let last = &hyps[*order.last().unwrap()];
        assert_eq!(
            last.rhs, first.lhs,
            "cyclic chain must return to starting point"
        );
    }

    /// Disconnected hypotheses: a ≤ b, c ≤ d → no valid ordering.
    #[test]
    fn test_find_chain_order_disconnected_returns_none() {
        let a = mk_var("a");
        let b = mk_var("b");
        let c = mk_var("c");
        let d = mk_var("d");
        let hyps = vec![
            mk_hyp(0, ArithSort::Real, CmpOp::Le, a, b),
            mk_hyp(1, ArithSort::Real, CmpOp::Le, c, d),
        ];
        assert!(
            find_chain_order(&hyps).is_none(),
            "disconnected hypotheses should not produce an ordering"
        );
    }

    /// Smoke test: build_chain_proof with 2 Int ≤ hypotheses returns correct sort/op/endpoints.
    #[test]
    fn test_build_chain_proof_two_le_returns_le_chain() {
        let int_ty = mk_var("Int");
        let a = mk_var("a");
        let b = mk_var("b");
        let c = mk_var("c");

        let fvar0 = FVarId::new(100);
        let fvar1 = FVarId::new(101);

        let h0_ty = mk_le_type(&int_ty, &a, &b);
        let h1_ty = mk_le_type(&int_ty, &b, &c);

        let goal = mk_test_goal(&[(fvar0, h0_ty), (fvar1, h1_ty)]);
        let hypothesis_fvars = vec![fvar0, fvar1];
        let active = vec![(0usize, 1i128), (1usize, 1i128)];

        let result = build_chain_proof(&active, &hypothesis_fvars, &goal);
        let (_, sort, op, chain_lhs, chain_rhs) =
            result.expect("2-hypothesis Int le chain should produce a proof");
        assert_eq!(sort, ArithSort::Int);
        assert_eq!(op, CmpOp::Le);
        assert_eq!(chain_lhs, a, "chain lhs should be first hypothesis lhs");
        assert_eq!(chain_rhs, c, "chain rhs should be last hypothesis rhs");
    }
}
