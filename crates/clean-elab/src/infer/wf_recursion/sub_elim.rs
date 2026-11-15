// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Truncated-subtraction elimination for the decreasing cascade** (WF phase
//! 4, 2026-08-27).
//!
//! Phase 3 lowered a SUM measure over several parameters and closed the
//! obligations a two-branch subtractive Euclid owes, because each of those is a
//! congruence of one summand over `Nat.sub_lt`. The class it could not reach is
//! the one whose truth depends on WHICH side of a truncated subtraction is
//! larger — where `a - b` is `0` in one order and a genuine difference in the
//! other. The motivating program is the BRANCH-FREE Euclid,
//!
//! ```lean
//! def gcdB (a b : Nat) : Nat :=
//!   if h : 0 < b then gcdB ((a - b) + (b - a)) (a - (a - b)) else a
//! termination_by a + 2 * b
//! ```
//!
//! — one guard, one self-call, no fuel — whose obligation is
//! `((a-b)+(b-a)) + 2*(a-(a-b)) < a + 2*b` under `0 < b`. On `Nat`,
//! `(a-b)+(b-a)` is `|a-b|` and `a-(a-b)` is `min a b`, so the left side is
//! exactly `a + b`; but NO tier of the cascade can see that, because every one
//! of them treats `a - b` as an opaque atom.
//!
//! # Three tiers, none of them shape-specific
//!
//! * [`ElabCtx::try_positivity_discharge`] — `0 < x + y` from `0 < x` (or
//!   `0 < y`), through `Nat.le_trans` and `Nat.le_add_right`. `Nat.lt 0 t` IS
//!   `Nat.le 1 t` by δ, so this is transitivity, not a new lemma.
//! * [`ElabCtx::try_linear_residual_discharge`] — **the strict residual.** Both
//!   sides of `L < R` are parsed into canonical linear forms (the same parser
//!   `omega`'s equality lane uses). If `R - L` has no negative coefficient and
//!   is not identically zero, it IS a residual `S`, and the obligation reduces
//!   to `0 < S` plus the linear equality `L + S = R`. The proof is
//!   `Nat.add_lt_add_left 0 S hS L`, whose type `Nat.lt (L + 0) (L + S)` is
//!   DEFINITIONALLY `L < L + S`, transported along that equality.
//!   A residual of zero is REFUSED — that is the whole reason `swapper`
//!   (`swapper b a` under `a < b`, measure `a + b`) stays rejected.
//! * [`ElabCtx::try_sub_case_split_discharge`] — **the elimination.** Pick a
//!   subtraction atom `x - y` whose two sides are both parameters, split on
//!   `Nat.le_total x y`, and in each branch replace the LARGER parameter by
//!   `smaller + (larger - smaller)` (justified by
//!   `Nat.ulpRound.sub_add_cancel`). Every subtraction in the branch then has a
//!   closed form that [`super::nat_rewrite`] rewrites away with named prelude
//!   theorems, and the residual goal is subtraction-free — so the tiers above,
//!   and every earlier tier, apply to it unchanged. Hypotheses mentioning the
//!   substituted parameter are transported into the branch too, so `0 < b`
//!   arrives as `0 < a + d` where the branch needs it.
//!
//! # Why this cannot accept a false sibling
//!
//! Nothing here decides anything. Each tier PROPOSES a term; the term is a
//! composition of named, axiom-free prelude theorems; and
//! `super::decreasing::ElabCtx::recheck_decreasing_proof` re-infers its type
//! with the strict kernel inference and requires def-eq against the ACTUAL
//! goal before it is accepted — after which `add_decl` re-checks the whole
//! definition. A measure that does not decrease has no residual (or has a
//! negative one, or leaves a branch whose positivity side-condition is not in
//! scope), the tier abstains, and the definition is refused. The e2e battery
//! pins that directionally: `gcdB` with `termination_by a + b` — one character
//! different, and genuinely non-terminating-as-measured — must still be
//! REFUSED, and it is, in the `a ≤ b` branch, where `0 < a` is not available.
//!
//! # The boundaries this does NOT move
//!
//! * The split pair must be two distinct **free variables**. A literal
//!   subtrahend (`b - 1`) keeps the `Nat.sub_lt` tier that already owns it, and
//!   a compound side is not split at all — so `lex`, `lexShadowed` and `halve`
//!   are untouched.
//! * All three tiers run AFTER the tactic tier, so every obligation that the
//!   cascade already discharged keeps the byte-identical proof term it had.

use std::collections::HashMap;

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, Level};
use clean_parser::SurfaceName;

use super::decreasing::{split_nat_lt, Budget};
use super::encoding;
use super::nat_rewrite::{
    congr_arg_prop, cst, eq_mp, eq_mpr, eq_trans, is_zero, match_add, match_positivity, match_sub,
    nadd, nat_eq_ty, nat_lam, nat_ty, nle, nlt, nmul, nzero, to_raw_nat, REQUIRED_CONSTANTS,
};
use super::ElabCtx;
use crate::tactic::arith_linarith_nat_eq::{parse_nat_linear_form, try_prove_nat_equality_direct};

/// `@Eq.trans.{1} Prop a b c h1 h2` — the `Prop`-level chain the two goal
/// transports need (`Prop : Sort 1`, so the level is 1, not 0).
fn prop_eq_trans(a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.trans"),
            vec![Level::succ(Level::zero())],
        ),
        [Expr::sort(Level::zero()), a, b, c, h1, h2],
    )
}

/// `Nat.succ Nat.zero` — the `1` in `Nat.lt 0 t ≡ Nat.le 1 t`.
fn one() -> Expr {
    Expr::app(cst("Nat.succ"), nzero())
}

impl ElabCtx<'_> {
    /// Is every constant these tiers name present? A minimal environment makes
    /// them disengage wholesale rather than emit a term the kernel would
    /// reject.
    fn sub_elim_env_ready(&self) -> bool {
        REQUIRED_CONSTANTS
            .iter()
            .all(|c| self.env.get_const(&Name::from_string(c)).is_some())
    }

    /// **Positivity of a sum.** `0 < x + y` from `0 < x` or `0 < y`.
    ///
    /// `Nat.lt Nat.zero t` unfolds to `Nat.le (Nat.succ Nat.zero) t`, so the
    /// proof is `Nat.le_trans 1 x (x + y) hx (Nat.le_add_right x y)` — pure
    /// transitivity over two named, axiom-free prelude theorems. The recursion
    /// is on a strictly smaller summand and additionally budget-bounded.
    pub(super) fn try_positivity_discharge(&mut self, goal: &Expr, budget: Budget) -> Option<Expr> {
        if budget.pos == 0 || !self.sub_elim_env_ready() {
            return None;
        }
        let (lhs, rhs) = split_nat_lt(goal)?;
        if !is_zero(&lhs) {
            return None;
        }
        let rhs = to_raw_nat(&rhs);

        // Route 0: a positivity hypothesis whose subject is LINEARLY equal to
        // the one asked for. `Nat.add` is commutative but not definitionally
        // so, and the residual tier orders a residual's atoms canonically, so
        // `0 < a + d` in scope and `0 < d + a` wanted is the everyday case.
        // The transport is a proved equality from the same synthesizer the
        // residual tier uses, which returns `None` for any pair whose canonical
        // linear forms differ — so a hypothesis about a DIFFERENT quantity can
        // never be re-labelled as one about this one.
        if let Some(proof) = self.try_positivity_from_hypothesis(goal, &rhs) {
            return Some(proof);
        }

        let (x, y) = match_add(&rhs)?;
        let next = budget.descend_pos();
        let le_trans = cst("Nat.le_trans");

        // From `0 < x`, with `x ≤ x + y`.
        if let Some(hx) = self.discharge_decreasing_goal_at(&nlt(nzero(), x.clone()), next) {
            if let Some(le) = self.le_witness(&x, &rhs) {
                let candidate =
                    Expr::apps(le_trans.clone(), [one(), x.clone(), rhs.clone(), hx, le]);
                if self.recheck_decreasing_proof(&candidate, goal) {
                    return Some(candidate);
                }
            }
        }

        // From `0 < y`, with `y ≤ x + y` (through `Nat.add_comm`).
        let hy = self.discharge_decreasing_goal_at(&nlt(nzero(), y.clone()), next)?;
        let le = self.le_witness(&y, &rhs)?;
        let candidate = Expr::apps(le_trans, [one(), y, rhs, hy, le]);
        self.recheck_decreasing_proof(&candidate, goal)
            .then_some(candidate)
    }

    /// Route 0 of the positivity tier: transport a positivity hypothesis along
    /// a proved linear equality between its subject and `subject`.
    fn try_positivity_from_hypothesis(&mut self, goal: &Expr, subject: &Expr) -> Option<Expr> {
        let hole = self.fresh_fvar();
        for (_, fvar, ty) in self.locals.clone() {
            let Some(known) = match_positivity(&ty) else {
                continue;
            };
            let known = to_raw_nat(&known);
            if &known == subject {
                // Tier 1 would have taken this; keep the cheap term anyway.
                if self.recheck_decreasing_proof(&Expr::fvar(fvar), goal) {
                    return Some(Expr::fvar(fvar));
                }
                continue;
            }
            let Some(heq) =
                try_prove_nat_equality_direct(&nat_eq_ty(known.clone(), subject.clone()))
            else {
                continue;
            };
            let candidate = eq_mp(
                nlt(nzero(), known.clone()),
                nlt(nzero(), subject.clone()),
                congr_arg_prop(
                    known,
                    subject.clone(),
                    nat_lam(hole, nlt(nzero(), Expr::fvar(hole))),
                    heq,
                ),
                Expr::fvar(fvar),
            );
            if self.recheck_decreasing_proof(&candidate, goal) {
                return Some(candidate);
            }
        }
        None
    }

    /// **The strict linear residual.** `L < R` when `R - L` is a non-negative,
    /// non-zero linear residual `S` and `0 < S` is dischargeable.
    ///
    /// The decision gate is the linear-form comparison, and it is where a
    /// non-decreasing measure dies: a residual with any negative coefficient,
    /// or one that is identically zero (`swapper`'s `b + a < a + b`), makes the
    /// tier abstain.
    pub(super) fn try_linear_residual_discharge(
        &mut self,
        goal: &Expr,
        budget: Budget,
    ) -> Option<Expr> {
        if budget.residual == 0 || !self.sub_elim_env_ready() {
            return None;
        }
        let (lhs, rhs) = split_nat_lt(goal)?;
        let lhs = to_raw_nat(&lhs);
        let rhs = to_raw_nat(&rhs);
        let residual = self.strict_residual(&lhs, &rhs)?;
        // No progress: `0 < S` would be the goal we started from.
        if residual == rhs && is_zero(&lhs) {
            return None;
        }

        // `heq : L + S = R`, from the linear-equality synthesizer. It returns
        // `None` for any pair whose canonical forms differ, so a mis-built
        // residual cannot be papered over here either.
        let heq = try_prove_nat_equality_direct(&nat_eq_ty(
            nadd(lhs.clone(), residual.clone()),
            rhs.clone(),
        ))?;
        let hs = self.discharge_decreasing_goal_at(
            &nlt(nzero(), residual.clone()),
            budget.without_residual(),
        )?;

        // `Nat.add_lt_add_left 0 S hs L : Nat.lt (L + 0) (L + S)`, and `L + 0`
        // ι-reduces to `L`, so this already inhabits `L < L + S`.
        let core = Expr::apps(
            cst("Nat.add_lt_add_left"),
            [nzero(), residual.clone(), hs, lhs.clone()],
        );
        let hole = self.fresh_fvar();
        let sum = nadd(lhs.clone(), residual);
        let candidate = eq_mp(
            nlt(lhs.clone(), sum.clone()),
            nlt(lhs.clone(), rhs.clone()),
            congr_arg_prop(sum, rhs, nat_lam(hole, nlt(lhs, Expr::fvar(hole))), heq),
            core,
        );
        self.recheck_decreasing_proof(&candidate, goal)
            .then_some(candidate)
    }

    /// `R - L` as a `Nat` expression, when it is a genuine strict residual:
    /// every coefficient and the constant non-negative, and not all zero.
    ///
    /// The atom order is the debug encoding, purely for determinism; the
    /// resulting term's correctness is settled by the equality synthesizer and
    /// the kernel, never by the order.
    fn strict_residual(&self, lhs: &Expr, rhs: &Expr) -> Option<Expr> {
        let lf = parse_nat_linear_form(lhs)?;
        let rf = parse_nat_linear_form(rhs)?;
        let mut diff: HashMap<Expr, i64> = rf.coeffs.clone();
        for (atom, c) in &lf.coeffs {
            *diff.entry(atom.clone()).or_insert(0) -= *c;
        }
        diff.retain(|_, c| *c != 0);
        let constant = rf.constant.checked_sub(lf.constant)?;
        if constant < 0 || diff.values().any(|c| *c < 0) {
            return None;
        }
        let mut atoms: Vec<(Expr, i64)> = diff.into_iter().collect();
        atoms.sort_by_key(|(atom, _)| format!("{atom:?}"));
        // A coefficient that does not fit a `u64` ABSTAINS rather than being
        // clamped: a clamped coefficient would build a residual the goal does
        // not name, and while the equality synthesizer and the kernel would
        // both reject it, the honest answer at this layer is "not my class".
        let terms: Option<Vec<Expr>> = atoms
            .into_iter()
            .map(|(atom, c)| {
                if c == 1 {
                    Some(atom)
                } else {
                    Some(nmul(Expr::nat_lit(u64::try_from(c).ok()?), atom))
                }
            })
            .collect();
        let mut terms = terms?;
        if constant > 0 {
            terms.push(Expr::nat_lit(u64::try_from(constant).ok()?));
        }
        let last = terms.pop()?;
        Some(terms.into_iter().rfold(last, |acc, t| nadd(t, acc)))
    }

    /// **Truncated-subtraction elimination by case split.**
    ///
    /// Splits on `Nat.le_total x y` for a subtraction atom `x - y` whose sides
    /// are two distinct parameters, and proves the goal in BOTH branches. Both
    /// must succeed — a `Or.rec` with one branch missing is not a proof — which
    /// is exactly why a measure that decreases in only one order is refused.
    pub(super) fn try_sub_case_split_discharge(
        &mut self,
        goal: &Expr,
        budget: Budget,
    ) -> Option<Expr> {
        if budget.split == 0 || !self.sub_elim_env_ready() {
            return None;
        }
        let (lhs, rhs) = split_nat_lt(goal)?;
        let raw_goal = nlt(to_raw_nat(&lhs), to_raw_nat(&rhs));
        let (x, y) = find_split_pair(&raw_goal)?;
        let (ex, ey) = (Expr::fvar(x), Expr::fvar(y));

        let left = self.build_split_branch(&raw_goal, x, y, budget)?;
        let right = self.build_split_branch(&raw_goal, y, x, budget)?;

        let (a_ty, b_ty) = (nle(ex.clone(), ey.clone()), nle(ey.clone(), ex.clone()));
        let motive = Expr::lam(
            BinderInfo::Default,
            Expr::apps(cst("Or"), [a_ty.clone(), b_ty.clone()]),
            raw_goal,
        );
        let candidate = Expr::apps(
            cst("Or.rec"),
            [
                a_ty,
                b_ty,
                motive,
                left,
                right,
                Expr::apps(cst("Nat.le_total"), [ex, ey]),
            ],
        );
        self.recheck_decreasing_proof(&candidate, goal)
            .then_some(candidate)
    }

    /// One branch of the split: `fun (h : lo ≤ hi) => <proof of goal>`.
    ///
    /// The local stack is unwound to its entry depth on BOTH the success and
    /// the failure path, so a refused branch cannot leave the context the next
    /// tier reports against corrupted.
    fn build_split_branch(
        &mut self,
        goal: &Expr,
        lo: FVarId,
        hi: FVarId,
        budget: Budget,
    ) -> Option<Expr> {
        let hyp_ty = nle(Expr::fvar(lo), Expr::fvar(hi));
        let depth = self.locals.len();
        let h = self.push_local(SurfaceName::unspellable("_wf_split_le", 0), hyp_ty.clone());
        let body = self.build_split_branch_core(goal, lo, hi, h, budget);
        while self.locals.len() > depth {
            self.pop_local();
        }
        let body = body?;
        Some(Expr::lam(
            BinderInfo::Default,
            hyp_ty,
            body.abstract_fvar(h),
        ))
    }

    fn build_split_branch_core(
        &mut self,
        goal: &Expr,
        lo: FVarId,
        hi: FVarId,
        h: FVarId,
        budget: Budget,
    ) -> Option<Expr> {
        let (elo, ehi) = (Expr::fvar(lo), Expr::fvar(hi));
        // `d := hi - lo` and `hd : lo + d = hi`, from
        // `Nat.ulpRound.sub_add_cancel hi lo h : (hi - lo) + lo = hi` commuted.
        let d = super::nat_rewrite::nsub(ehi.clone(), elo.clone());
        let subst = nadd(elo.clone(), d.clone());
        let hd = eq_trans(
            subst.clone(),
            nadd(d.clone(), elo.clone()),
            ehi.clone(),
            Expr::apps(cst("Nat.add_comm"), [elo.clone(), d.clone()]),
            Expr::apps(
                cst("Nat.ulpRound.sub_add_cancel"),
                [ehi.clone(), elo, Expr::fvar(h)],
            ),
        );

        // Every hypothesis mentioning `hi` is carried into the branch in its
        // substituted form. Without this the branch would lose exactly the
        // facts it needs (`0 < b` becomes `0 < a + d` and nothing else states
        // it).
        let hole = self.fresh_fvar();
        let mut carried: Vec<(Expr, Expr)> = Vec::new();
        for (_, fvar, ty) in self.locals.clone() {
            if fvar == h || !encoding::contains_fvar(&ty, hi) {
                continue;
            }
            let substituted = ty.clone().subst_fvar(hi, &subst);
            let cong = congr_arg_prop(
                subst.clone(),
                ehi.clone(),
                Expr::lam(BinderInfo::Default, nat_ty(), ty.clone().abstract_fvar(hi)),
                hd.clone(),
            );
            carried.push((
                substituted.clone(),
                eq_mpr(substituted, ty, cong, Expr::fvar(fvar)),
            ));
        }
        let mut carried_fvars: Vec<FVarId> = Vec::new();
        for (ty, _) in &carried {
            carried_fvars
                .push(self.push_local(SurfaceName::unspellable("_wf_split_carry", 0), ty.clone()));
        }

        // The goal with `hi` substituted, then normalized side by side.
        let goal2 = goal.clone().subst_fvar(hi, &subst);
        let (l2, r2) = split_nat_lt(&goal2)?;
        let (l3, pl) = self.normalize_nat(&l2, hole);
        let (r3, pr) = self.normalize_nat(&r2, hole);
        let goal3 = nlt(l3.clone(), r3.clone());
        let sub = self.discharge_decreasing_goal_at(&goal3, budget.descend_split())?;

        // `goal2 = goal3`, one side at a time.
        let mid = nlt(l3.clone(), r2.clone());
        let step_l = congr_arg_prop(
            l2.clone(),
            l3.clone(),
            nat_lam(hole, nlt(Expr::fvar(hole), r2.clone())),
            pl,
        );
        let step_r = congr_arg_prop(r2.clone(), r3, nat_lam(hole, nlt(l3, Expr::fvar(hole))), pr);
        let goal2_lt = nlt(l2, r2);
        let to_goal3 = prop_eq_trans(goal2_lt.clone(), mid, goal3.clone(), step_l, step_r);
        let mut body = eq_mpr(goal2_lt, goal3, to_goal3, sub);

        // Discharge the carried hypotheses by application, innermost last.
        for ((ty, term), fvar) in carried.iter().zip(carried_fvars.iter()).rev() {
            body = Expr::app(
                Expr::lam(BinderInfo::Default, ty.clone(), body.abstract_fvar(*fvar)),
                term.clone(),
            );
        }

        // Undo the substitution: `congrArg (fun t => goal[hi := t]) hd`.
        let cong = congr_arg_prop(
            subst,
            ehi,
            Expr::lam(
                BinderInfo::Default,
                nat_ty(),
                goal.clone().abstract_fvar(hi),
            ),
            hd,
        );
        Some(eq_mp(goal2, goal.clone(), cong, body))
    }
}

/// The first subtraction atom whose two sides are DISTINCT free variables,
/// in a left-to-right traversal.
///
/// Restricting to free variables is what keeps this tier away from the shapes
/// earlier tiers own: `b - 1` has a literal subtrahend and stays with
/// `Nat.sub_lt`, and a compound side (`a - (a - b)`) is not split on directly —
/// its own inner atom `a - b` supplies the pair, which is the split that
/// actually resolves it.
fn find_split_pair(e: &Expr) -> Option<(FVarId, FVarId)> {
    if let Some((x, y)) = match_sub(e) {
        if let (ExprKind::FVar(xi), ExprKind::FVar(yi)) = (x.kind(), y.kind()) {
            if xi != yi {
                return Some((*xi, *yi));
            }
        }
    }
    match e.kind() {
        ExprKind::App(f, a) => find_split_pair(f).or_else(|| find_split_pair(a)),
        ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
            find_split_pair(t).or_else(|| find_split_pair(b))
        }
        ExprKind::MData(_, inner) | ExprKind::Proj(_, _, inner) => find_split_pair(inner),
        _ => None,
    }
}
