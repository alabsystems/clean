// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bounded case-split lane for `omega` (brick 87).
//!
//! Proves the everyday case-split family
//! `(h : n ≤ k) ⊢ n = c₀ ∨ n = c₁ ∨ … ∨ n = cₘ` — one `Nat` variable, one
//! ground upper bound, disjuncts covering every value in `[0, k]`. Compound
//! `Or` goals cannot parse into a single `OmegaConstraint`, so the constraint
//! pipeline silently drops them, finds the hypotheses-only system satisfiable,
//! and falls through to the (failing) linarith delegate — this family always
//! failed before this lane.
//!
//! The proof is a CLOSED term (no metavariables, no tactic-scope FVars) built
//! by interval descent, then re-checked by `close_goal` (kernel-grade strict
//! inference), so soundness never rests on the detection logic:
//!
//! ```text
//! descend(v, h_le : n ≤ v):
//!   Or.rec (n < v) (n = v) (λ _. goal)
//!     (λ hlt. v = 0 ? False.elim goal (Nat.not_succ_le_zero n hlt)
//!                  : descend(v-1, Nat.le_of_succ_le_succ n (v-1) hlt))
//!     (λ heq. Or-intro of the disjunct with value v, witnessed by heq)
//!     (Nat.lt_or_eq_of_le n v h_le)
//! ```
//!
//! NOTE on the `interval_cases` machinery (interval_cases.rs:30): its
//! `build_or_elim_chain` proof links sub-goal METAS whose per-value equality
//! hypothesis is an out-of-band FVar (`ctx.len() + 1000`,
//! interval_cases.rs:119) with no matching binder in the assembled term (the
//! true-branch lambda is anonymous, finite_cases_proof.rs:190-194, and the
//! LAST branch has no binder at all, finite_cases_proof.rs:176-177). A
//! sub-proof that USES the equality witness — which this family requires —
//! therefore cannot survive the final FVar→BVar close. Hence the closed-term
//! descent here, which follows the same Or-elimination proof pattern with
//! real binders.

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, Level};

use super::super::arith_mathverse_parse::extract_constant;
use super::super::{match_eq, match_le, match_lt};
use super::{Goal, ProofState, TacticError, TacticResult};
use crate::unify::MetaState;

/// Largest upper bound the lane will case-split on (matches the certified
/// pipeline's "small ground bound" spirit; `interval_cases` caps at 100).
const MAX_SPLIT_BOUND: u64 = 32;

/// Prelude constants the closed proof term references. If any is missing
/// (minimal test environments), the lane disengages and the pipeline is
/// byte-identical to before this brick.
const REQUIRED_CONSTANTS: [&str; 7] = [
    "Nat.lt_or_eq_of_le",
    "Nat.le_of_succ_le_succ",
    "Nat.not_succ_le_zero",
    "False.elim",
    "Or.rec",
    "Or.inl",
    "Or.inr",
];

/// A detected bounded case-split goal.
struct BoundedOrSplit {
    /// The single `Nat` variable all disjuncts equate.
    var: FVarId,
    /// Ground upper bound: `var ≤ upper` holds by hypothesis.
    upper: u64,
    /// The bounding hypothesis.
    hyp_fvar: FVarId,
    /// `true` when the hypothesis is `var < upper + 1` rather than `var ≤ upper`.
    hyp_is_lt: bool,
    /// Right-nested disjunct types `A_i` in goal order with their ground values.
    disjuncts: Vec<(Expr, u64)>,
}

/// Try to prove a bounded Nat case-split disjunction goal.
///
/// ENSURES: returns `None` iff the goal is outside the slice (shape, bound,
///   or environment gate failed) — the caller's pipeline proceeds unchanged
/// ENSURES: returns `Some(Ok(()))` only when `close_goal` kernel-accepted the
///   synthesized closed proof term for the current goal
/// ENSURES: returns `Some(Err(_))` (loud, tactic "omega") when a value in
///   `[0, upper]` has no matching disjunct (goal false or out of slice) or
///   when the kernel rejected the reconstruction; `state` is unchanged
pub(crate) fn try_bounded_or_case_split(
    state: &mut ProofState,
    goal: &Goal,
) -> Option<TacticResult> {
    if REQUIRED_CONSTANTS
        .iter()
        .any(|c| state.env().get_const(&Name::from_string(c)).is_none())
    {
        return None;
    }
    let target = state.metas.instantiate(&goal.target);
    let split = detect_bounded_or_split(goal, &target)?;

    // Per-value coverage: every value the bound admits must appear among the
    // disjuncts, or the goal is false (n could BE the missing value) / out of
    // slice. FAIL LOUD rather than fall through to a misleading Sat report.
    let mut index_of_value = Vec::with_capacity(split.upper as usize + 1);
    for v in 0..=split.upper {
        match split.disjuncts.iter().position(|(_, c)| *c == v) {
            Some(i) => index_of_value.push(i),
            None => {
                return Some(Err(TacticError::ArithmeticFailed {
                    tactic: "omega".into(),
                    reason: format!(
                        "bounded case split: the hypothesis admits the value {v} \
                         (bound {}), but no disjunct states it — the goal is \
                         false or outside the case-split slice",
                        split.upper
                    ),
                }))
            }
        }
    }

    let proof = build_case_split_proof(&target, &split, &index_of_value);
    Some(match state.close_goal(goal, proof) {
        Ok(()) => Ok(()),
        Err(err) => Err(TacticError::ArithmeticFailed {
            tactic: "omega".into(),
            reason: format!("bounded case split: kernel rejected the reconstructed proof: {err:?}"),
        }),
    })
}

/// Detect `⊢ n = c₀ ∨ … ∨ n = cₘ` with a ground `n ≤ k` / `n < k+1` bound.
fn detect_bounded_or_split(goal: &Goal, target: &Expr) -> Option<BoundedOrSplit> {
    let leaves = flatten_or(target);
    if leaves.len() < 2 {
        return None;
    }
    let mut var: Option<FVarId> = None;
    let mut disjuncts = Vec::with_capacity(leaves.len());
    for leaf in leaves {
        let (carrier, lhs, rhs) = match_eq(&leaf)?;
        if !is_nat_const(&carrier) {
            return None;
        }
        let ExprKind::FVar(id) = lhs.kind() else {
            return None;
        };
        if MetaState::from_fvar(*id).is_some() {
            return None;
        }
        match var {
            None => var = Some(*id),
            Some(v) if v == *id => {}
            Some(_) => return None,
        }
        let value = u64::try_from(extract_constant(&rhs)?).ok()?;
        disjuncts.push((leaf, value));
    }
    let var = var?;
    if !goal
        .local_ctx
        .iter()
        .any(|d| d.fvar == var && is_nat_const(&d.ty))
    {
        return None;
    }
    // Tightest ground upper bound on `var` among the hypotheses.
    let mut best: Option<(u64, FVarId, bool)> = None;
    for decl in &goal.local_ctx {
        if let Some((k, is_lt)) = hyp_upper_bound(&decl.ty, var) {
            if best.is_none_or(|(b, _, _)| k < b) {
                best = Some((k, decl.fvar, is_lt));
            }
        }
    }
    let (upper, hyp_fvar, hyp_is_lt) = best?;
    if upper > MAX_SPLIT_BOUND {
        return None;
    }
    Some(BoundedOrSplit {
        var,
        upper,
        hyp_fvar,
        hyp_is_lt,
        disjuncts,
    })
}

/// Flatten a right-nested `Or A (Or B …)` into its leaves.
fn flatten_or(target: &Expr) -> Vec<Expr> {
    let mut leaves = Vec::new();
    let mut cur = target.clone();
    loop {
        let next = {
            let args = cur.get_app_args();
            let is_or = args.len() == 2
                && matches!(cur.get_app_fn().kind(), ExprKind::Const(n, _) if n.to_string() == "Or");
            if is_or {
                Some((args[0].clone(), args[1].clone()))
            } else {
                None
            }
        };
        match next {
            Some((head, rest)) => {
                leaves.push(head);
                cur = rest;
            }
            None => {
                leaves.push(cur);
                return leaves;
            }
        }
    }
}

/// Ground upper bound `var ≤ k` (from `var ≤ k` or `var < k+1`) stated by `ty`.
fn hyp_upper_bound(ty: &Expr, var: FVarId) -> Option<(u64, bool)> {
    if let Some((carrier, lhs, rhs)) = match_le(ty) {
        if is_nat_const(&carrier) && matches!(lhs.kind(), ExprKind::FVar(id) if *id == var) {
            let k = u64::try_from(extract_constant(&rhs)?).ok()?;
            return Some((k, false));
        }
    }
    if let Some((carrier, lhs, rhs)) = match_lt(ty) {
        if is_nat_const(&carrier) && matches!(lhs.kind(), ExprKind::FVar(id) if *id == var) {
            let k = u64::try_from(extract_constant(&rhs)?).ok()?;
            if k >= 1 {
                return Some((k - 1, true));
            }
        }
    }
    None
}

/// Build the closed interval-descent proof of `target`.
fn build_case_split_proof(target: &Expr, split: &BoundedOrSplit, index_of_value: &[usize]) -> Expr {
    let n = Expr::fvar(split.var);
    let h = Expr::fvar(split.hyp_fvar);
    let h_le = if split.hyp_is_lt {
        // h : n < upper+1 ≡ Nat.le (succ n) (succ upper); peel one succ.
        Expr::apps(
            cst("Nat.le_of_succ_le_succ"),
            [n, Expr::nat_lit(split.upper), h],
        )
    } else {
        h
    };
    descend(target, split, index_of_value, split.upper, h_le)
}

/// Proof of `target` from `h_le : n ≤ v`, by `Or.rec` over
/// `Nat.lt_or_eq_of_le n v h_le : n < v ∨ n = v`.
///
/// `h_le` may reference `BVar(0)` of the caller's enclosing lambda; it is only
/// placed in the major-premise application spine (never under a binder), so
/// no de Bruijn lifting is required.
fn descend(
    target: &Expr,
    split: &BoundedOrSplit,
    index_of_value: &[usize],
    v: u64,
    h_le: Expr,
) -> Expr {
    let n = Expr::fvar(split.var);
    let v_lit = Expr::nat_lit(v);
    let lt_ty = nat_lt_tc(n.clone(), v_lit.clone());
    let eq_ty = nat_eq(n.clone(), v_lit.clone());
    let major = Expr::apps(cst("Nat.lt_or_eq_of_le"), [n.clone(), v_lit, h_le]);
    let motive = Expr::lam(
        BinderInfo::Default,
        or_of(lt_ty.clone(), eq_ty.clone()),
        target.clone(),
    );
    let minor_inr = Expr::lam(
        BinderInfo::Default,
        eq_ty.clone(),
        or_intro(&split.disjuncts, index_of_value[v as usize], Expr::bvar(0)),
    );
    let minor_inl = if v == 0 {
        // λ (hlt : n < 0). False.elim target (Nat.not_succ_le_zero n hlt)
        let false_pf = Expr::apps(cst("Nat.not_succ_le_zero"), [n, Expr::bvar(0)]);
        Expr::lam(
            BinderInfo::Default,
            lt_ty.clone(),
            Expr::apps(
                Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
                [target.clone(), false_pf],
            ),
        )
    } else {
        // λ (hlt : n < v). descend(v-1, Nat.le_of_succ_le_succ n (v-1) hlt)
        let h_le_next = Expr::apps(
            cst("Nat.le_of_succ_le_succ"),
            [n, Expr::nat_lit(v - 1), Expr::bvar(0)],
        );
        Expr::lam(
            BinderInfo::Default,
            lt_ty.clone(),
            descend(target, split, index_of_value, v - 1, h_le_next),
        )
    };
    Expr::apps(
        cst("Or.rec"),
        [lt_ty, eq_ty, motive, minor_inl, minor_inr, major],
    )
}

/// Or-introduction of disjunct `d`, witnessed by `eq_pf : n = value(d)`.
fn or_intro(disjuncts: &[(Expr, u64)], d: usize, eq_pf: Expr) -> Expr {
    let last = disjuncts.len() - 1;
    let mut pf = if d == last {
        eq_pf
    } else {
        Expr::apps(
            cst("Or.inl"),
            [disjuncts[d].0.clone(), suffix_ty(disjuncts, d + 1), eq_pf],
        )
    };
    for j in (0..d).rev() {
        pf = Expr::apps(
            cst("Or.inr"),
            [disjuncts[j].0.clone(), suffix_ty(disjuncts, j + 1), pf],
        );
    }
    pf
}

/// The right-nested suffix type `A_from ∨ (A_{from+1} ∨ …)`.
fn suffix_ty(disjuncts: &[(Expr, u64)], from: usize) -> Expr {
    let mut ty = disjuncts[disjuncts.len() - 1].0.clone();
    for j in (from..disjuncts.len() - 1).rev() {
        ty = or_of(disjuncts[j].0.clone(), ty);
    }
    ty
}

fn cst(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn is_nat_const(e: &Expr) -> bool {
    matches!(e.kind(), ExprKind::Const(n, _) if n.to_string() == "Nat")
}

/// `@LT.lt.{0} Nat instLTNat lhs rhs` (the form `Nat.lt_or_eq_of_le` states).
fn nat_lt_tc(lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
        [
            cst("Nat"),
            Expr::const_(Name::from_string("instLTNat"), vec![]),
            lhs,
            rhs,
        ],
    )
}

/// `@Eq.{1} Nat lhs rhs`.
fn nat_eq(lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [cst("Nat"), lhs, rhs],
    )
}

fn or_of(a: Expr, b: Expr) -> Expr {
    Expr::apps(cst("Or"), [a, b])
}
