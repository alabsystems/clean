// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Decreasing proof generation for well-founded recursion.
//!
//! When a recursive function is defined with `termination_by`, each
//! recursive call site generates a proof obligation:
//!   `measure(rec_arg) < measure(current_arg)`
//!
//! The PRODUCTION entry point is [`ElabCtx::discharge_decreasing_goal`]
//! (first production caller wired 2026-08-10, WF phase 1): a fail-closed
//! cascade — hypothesis lookup → `Nat.sub_lt` → `Nat.mod_lt` → sum congruence
//! → `omega`/`simp_arith` → the phase-4 truncated-subtraction lane (sum
//! positivity → the strict linear residual → a case split on `Nat.le_total`,
//! all in [`super::sub_elim`]) — where every candidate is strictly re-checked
//! (`infer_type_full` + def-eq against the goal, sorry refused) before it is
//! accepted, and failure returns `None` so the caller rejects the definition
//! loudly. It NEVER falls back to `sorry` or a metavariable.
//!
//! The tier ORDER is load-bearing for term stability: the phase-4 tiers sit
//! after the tactic tier, so every obligation an earlier tier already
//! discharged reaches that tier first and keeps the byte-identical proof term
//! it had.
//!
//! Both named-theorem tiers key on a POSITIVITY proof of `0 < B`, and
//! [`ElabCtx::positivity_candidates`] is where the local context is turned
//! into candidates for one: the hypothesis itself (`h : 0 < b`), or
//! `Nat.pos_of_ne_zero` applied to a disequality — including the
//! `¬((b == 0) = true)` a Bool test binds once `call_sites::ite_to_dite` has
//! made the `if` dependent. Every route is a named axiom-free prelude theorem,
//! and every assembled candidate still goes through the same strict recheck.
//!
//! The older `solve_decreasing_obligation` scaffold (user `decreasing_by` →
//! `simp_arith` → `mathverse` → unresolved metavariable) remains staged and
//! unit-tested but has no production caller — its metavariable fallback is
//! exactly what the fail-closed contract forbids.
//!
//! Reference: Lean 4 `src/Lean/Elab/PreDefinition/WF/Fix.lean`
//!            (mkDecreasingProof, solveDecreasingGoals)

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind, FVarId};
use clean_parser::{SurfaceName, SurfaceTactic};

use super::{measure_shape, ElabCtx};
use crate::ElabError;

impl ElabCtx<'_> {
    /// Discharge a decreasing obligation `Nat.lt (measure arg) (measure param)`
    /// against the CURRENT local context (which includes every hypothesis the
    /// call-site traversal has opened, e.g. a `dite` branch's `h : 0 < n`).
    ///
    /// Cascade (first hit wins):
    /// 1. a hypothesis whose type is already def-eq to the goal;
    /// 2. `Nat.sub_lt` — the canonical `n - k < n` shape, keyed on a
    ///    positivity proof (see [`Self::positivity_candidates`]);
    /// 3. `Nat.mod_lt` — the `a % b < b` shape (what `gcd` decreases by),
    ///    keyed on the same positivity proofs;
    /// 4. SUM CONGRUENCE — `Nat.add_lt_add_left` / `_right` / `Nat.add_lt_add`
    ///    for a goal whose two sides are both `+`, recursing on the summand
    ///    that actually moved (what a multi-parameter SUM measure decreases
    ///    by);
    /// 5. tactics: `omega`, then `simp_arith`;
    /// 6. POSITIVITY of a sum — `0 < x + y` from a positive summand, or from a
    ///    positivity hypothesis whose subject is linearly equal to this one;
    /// 7. the STRICT LINEAR RESIDUAL — `L < R` when `R - L` is a non-negative,
    ///    non-zero linear residual `S` and `0 < S` is dischargeable;
    /// 8. TRUNCATED-SUBTRACTION ELIMINATION — a case split on `Nat.le_total`
    ///    that substitutes the larger parameter and rewrites every `-` away,
    ///    feeding two subtraction-free obligations back through this cascade.
    ///
    /// Tiers 2–4 are deliberately ahead of the tactics: they produce a
    /// term whose head is a NAMED, axiom-free prelude theorem, so the
    /// decrease's provenance is readable in the emitted definition instead of
    /// resting on whatever a tactic happened to synthesize. Tiers 6–8 are
    /// deliberately BEHIND them, so nothing that already worked changes shape;
    /// they too emit only named, axiom-free prelude theorems.
    ///
    /// SOUNDNESS: every candidate — including tactic-produced terms — is
    /// re-checked with STRICT kernel inference (`infer_type_full`, the same
    /// standard `Environment::add_decl` applies) before being accepted, and
    /// sorry-carrying terms are refused. `None` means "not discharged": the
    /// caller fails closed; this function never fabricates a proof.
    pub(super) fn discharge_decreasing_goal(&mut self, goal: &Expr) -> Option<Expr> {
        self.discharge_decreasing_goal_at(goal, Budget::default())
    }

    /// [`Self::discharge_decreasing_goal`] with every recursion budget made
    /// explicit. Each field bounds exactly one tier; at `Budget::none()` the
    /// cascade is byte-identical to the pre-phase-3 one.
    pub(super) fn discharge_decreasing_goal_at(
        &mut self,
        goal: &Expr,
        budget: Budget,
    ) -> Option<Expr> {
        let depth = budget.sum;
        let locals: Vec<(SurfaceName, FVarId, Expr)> = self.locals.clone();

        // Tier 1: a hypothesis already proves the goal.
        for (_, fvar, ty) in &locals {
            if self.is_def_eq(ty, goal) {
                return Some(Expr::fvar(*fvar));
            }
        }

        // Tier 2: `Nat.sub_lt B k h hk` for the `B - k < B` family.
        if let Some(proof) = self.try_nat_sub_lt_discharge(goal, &locals) {
            return Some(proof);
        }

        // Tier 3: `Nat.mod_lt A B h` for the `A % B < B` family.
        if let Some(proof) = self.try_nat_mod_lt_discharge(goal, &locals) {
            return Some(proof);
        }

        // Tier 4: sum congruence, for a multi-parameter SUM measure.
        if depth > 0 {
            if let Some(proof) = self.try_sum_congruence_discharge(goal, budget) {
                return Some(proof);
            }
        }

        // Tier 5: tactic cascade.
        for tactic in ["omega", "simp_arith"] {
            let tacs = [SurfaceTactic::Named {
                span: clean_parser::Span::dummy(),
                name: tactic.to_owned(),
                args: vec![],
            }];
            if let Ok(proof) = self.try_tactic_on_goal(goal, &tacs) {
                if self.recheck_decreasing_proof(&proof, goal) {
                    return Some(proof);
                }
            }
        }

        // Tiers 6–8 are the phase-4 truncated-subtraction lane
        // (`super::sub_elim`). They sit AFTER the tactic tier on purpose: every
        // obligation the cascade already discharged reaches its old tier first
        // and keeps the byte-identical proof term it had, so this widening is
        // strictly additive.

        // Tier 6: positivity of a sum — `0 < x + y` from a positive summand.
        if let Some(proof) = self.try_positivity_discharge(goal, budget) {
            return Some(proof);
        }

        // Tier 7: the strict linear residual — `L < R` when `R - L` is a
        // non-negative, non-zero linear residual whose positivity is provable.
        if let Some(proof) = self.try_linear_residual_discharge(goal, budget) {
            return Some(proof);
        }

        // Tier 8: truncated-subtraction elimination by case split on
        // `Nat.le_total`, which turns one obligation carrying `-` into two that
        // do not, both of which go back through this same cascade.
        if let Some(proof) = self.try_sub_case_split_discharge(goal, budget) {
            return Some(proof);
        }

        None
    }

    /// **Tier 4 — sum congruence.** `Nat.lt (l₁ + l₂) (r₁ + r₂)` reduces to a
    /// decrease in the summand that actually moved:
    ///
    /// * `l₁ ≡ r₁` → `Nat.add_lt_add_left  l₂ r₂ ⟨l₂ < r₂⟩ l₁`
    /// * `l₂ ≡ r₂` → `Nat.add_lt_add_right l₁ r₁ ⟨l₁ < r₁⟩ l₂`
    /// * otherwise  → `Nat.add_lt_add l₁ r₁ l₂ r₂ ⟨l₁ < r₁⟩ ⟨l₂ < r₂⟩`
    ///
    /// This is what a multi-parameter SUM measure needs, and it is
    /// compositional rather than new capability: the sub-obligation goes back
    /// through the SAME cascade, so `gcdSub`'s `(a - b) + b < a + b` becomes
    /// `a - b < a`, which tier 2 already owns. `a + b + c` nests one level
    /// deeper, hence the budget.
    ///
    /// All three lemmas are constructive, axiom-free prelude `Theorem`s
    /// (`clean-kernel/src/env/nat_arith_order_proof.rs`, #3604), so this tier
    /// only makes existing proofs reachable — it admits nothing. Every
    /// assembled candidate still goes through the strict recheck, and a
    /// missing lemma makes the tier abstain rather than emit a term naming a
    /// constant the kernel would reject.
    fn try_sum_congruence_discharge(&mut self, goal: &Expr, budget: Budget) -> Option<Expr> {
        let (lhs, rhs) = split_nat_lt(goal)?;
        let (l1, l2) = measure_shape::split_nat_add(&lhs)?;
        let (r1, r2) = measure_shape::split_nat_add(&rhs)?;

        let named = |ctx: &Self, n: &str| {
            let name = Name::from_string(n);
            ctx.env.get_const(&name).map(|_| Expr::const_(name, vec![]))
        };

        // The left summands agree: the right ones must carry the decrease.
        if self.is_def_eq(&l1, &r1) {
            if let Some(lemma) = named(self, "Nat.add_lt_add_left") {
                let sub_goal = nat_lt_goal(l2.clone(), r2.clone());
                if let Some(sub) =
                    self.discharge_decreasing_goal_at(&sub_goal, budget.descend_sum())
                {
                    let candidate = Expr::apps(lemma, [l2.clone(), r2.clone(), sub, l1.clone()]);
                    if self.recheck_decreasing_proof(&candidate, goal) {
                        return Some(candidate);
                    }
                }
            }
        }

        // The right summands agree: the left ones must carry the decrease.
        if self.is_def_eq(&l2, &r2) {
            if let Some(lemma) = named(self, "Nat.add_lt_add_right") {
                let sub_goal = nat_lt_goal(l1.clone(), r1.clone());
                if let Some(sub) =
                    self.discharge_decreasing_goal_at(&sub_goal, budget.descend_sum())
                {
                    let candidate = Expr::apps(lemma, [l1.clone(), r1.clone(), sub, l2.clone()]);
                    if self.recheck_decreasing_proof(&candidate, goal) {
                        return Some(candidate);
                    }
                }
            }
        }

        // Neither summand is fixed: both must strictly decrease.
        let lemma = named(self, "Nat.add_lt_add")?;
        let left_goal = nat_lt_goal(l1.clone(), r1.clone());
        let left = self.discharge_decreasing_goal_at(&left_goal, budget.descend_sum())?;
        let right_goal = nat_lt_goal(l2.clone(), r2.clone());
        let right = self.discharge_decreasing_goal_at(&right_goal, budget.descend_sum())?;
        let candidate = Expr::apps(lemma, [l1, r1, l2, r2, left, right]);
        self.recheck_decreasing_proof(&candidate, goal)
            .then_some(candidate)
    }

    /// Try `Nat.sub_lt B k h hk` for the `B - k < B` family, in two passes:
    /// first for small LITERAL `k` (`k = 1 … 4`, the pre-existing behaviour,
    /// kept first so every goal it already discharged keeps the identical proof
    /// term), then for the VARIABLE subtrahend read off the goal's left-hand
    /// side — `a - b < a`, which is what a subtractive recursion decreases by.
    ///
    /// Wrong candidates are weeded out by the strict recheck (a hypothesis that
    /// is not a `0 < B` proof simply fails inference), so this needs no
    /// syntactic hypothesis matching — definitional equality does the work,
    /// including unfolding `HSub.hSub`/`OfNat` sugar in the goal.
    fn try_nat_sub_lt_discharge(
        &mut self,
        goal: &Expr,
        locals: &[(SurfaceName, FVarId, Expr)],
    ) -> Option<Expr> {
        // The caller constructs the goal as `Nat.lt <m arg> <m param>`;
        // extract the right-hand side `B := m param`.
        let ExprKind::App(lhs_fn, rhs) = goal.kind() else {
            return None;
        };
        let ExprKind::App(head, _) = lhs_fn.kind() else {
            return None;
        };
        let nat_lt_name = Name::from_string("Nat.lt");
        match head.kind() {
            ExprKind::Const(n, _) if *n == nat_lt_name => {}
            _ => return None,
        }
        let sub_lt_name = Name::from_string("Nat.sub_lt");
        let zls_name = Name::from_string("Nat.zero_lt_succ");
        if self.env.get_const(&sub_lt_name).is_none() || self.env.get_const(&zls_name).is_none() {
            return None;
        }
        let sub_lt = Expr::const_(sub_lt_name, vec![]);
        let zls = Expr::const_(zls_name, vec![]);
        let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let b = Expr::clone(rhs);
        let positivity = self.positivity_candidates(&b, locals);
        for pos in &positivity {
            for k in 1..=4u64 {
                let k_expr = Expr::app(succ.clone(), Expr::nat_lit(k - 1));
                let k_pos = Expr::app(zls.clone(), Expr::nat_lit(k - 1));
                let candidate = Expr::apps(sub_lt.clone(), [b.clone(), k_expr, pos.clone(), k_pos]);
                if self.recheck_decreasing_proof(&candidate, goal) {
                    return Some(candidate);
                }
            }
        }

        // A VARIABLE subtrahend — `a - b < a`, which is what a subtractive
        // recursion decreases by and what the literal loop above cannot reach.
        // The subtrahend is read off the goal's LEFT-hand side (in either `-`
        // spelling); its positivity comes from the same `positivity_candidates`
        // as the minuend's, so a `b ≠ 0` guard in scope is enough. The
        // MINUEND is deliberately NOT read from the left-hand side — `b` above
        // is the goal's right-hand side — so a mismatched `x - k < y` can never
        // be papered over, and the strict recheck refuses it if it is.
        //
        // Placed AFTER the literal loop so every goal the pre-phase-3 cascade
        // already discharged keeps the byte-identical proof term it had.
        let subtrahend = sub_subtrahend(&lhs_of(goal)?)?;
        let subtrahend_positivity = self.positivity_candidates(&subtrahend, locals);
        for pos in &positivity {
            for k_pos in &subtrahend_positivity {
                let candidate = Expr::apps(
                    sub_lt.clone(),
                    [b.clone(), subtrahend.clone(), pos.clone(), k_pos.clone()],
                );
                if self.recheck_decreasing_proof(&candidate, goal) {
                    return Some(candidate);
                }
            }
        }
        None
    }

    /// Try `Nat.mod_lt A B h` for every hypothesis `h` in scope — the
    /// `A % B < B` family, which is exactly `gcd`'s decrease.
    ///
    /// `Nat.mod_lt : ∀ (a n : Nat), Nat.lt 0 n → Nat.lt (Nat.mod a n) n` is a
    /// constructive, AXIOM-FREE prelude `Theorem`
    /// (`clean-kernel/src/env/data_types_nat_div_mod_lemmas.rs`, proven over
    /// the genuine `Nat.modCore` structural definition), so nothing new is
    /// admitted here: the tier only makes an existing proof reachable.
    ///
    /// The numerator is read off the goal's left-hand side in either spelling
    /// the elaborator produces — the raw `Nat.mod a b`, or the `%` notation
    /// `@HMod.hMod Nat Nat Nat instHModNat a b`. The DIVISOR is not read from
    /// the left-hand side at all: it is taken from the goal's right-hand side,
    /// so a mismatched `a % k < b` can never be papered over. As in the
    /// `Nat.sub_lt` tier, a wrong hypothesis is weeded out by the strict
    /// recheck rather than by syntactic matching.
    fn try_nat_mod_lt_discharge(
        &mut self,
        goal: &Expr,
        locals: &[(SurfaceName, FVarId, Expr)],
    ) -> Option<Expr> {
        let (lhs, divisor) = split_nat_lt(goal)?;
        let numerator = mod_numerator(&lhs)?;
        let mod_lt_name = Name::from_string("Nat.mod_lt");
        self.env.get_const(&mod_lt_name)?;
        let mod_lt = Expr::const_(mod_lt_name, vec![]);
        for pos in self.positivity_candidates(&divisor, locals) {
            let candidate = Expr::apps(mod_lt.clone(), [numerator.clone(), divisor.clone(), pos]);
            if self.recheck_decreasing_proof(&candidate, goal) {
                return Some(candidate);
            }
        }
        None
    }

    /// Candidate proofs of `Nat.lt Nat.zero b`, assembled from the local
    /// context. Every candidate is a hypothesis, or a NAMED axiom-free prelude
    /// theorem applied to one — nothing here is a tactic result, and nothing is
    /// accepted on the strength of its shape: each is re-inferred and def-eq
    /// checked by the caller's [`Self::recheck_decreasing_proof`], so a
    /// candidate built from an unrelated hypothesis simply fails inference and
    /// is dropped.
    ///
    /// Four routes, in the order a reader would try them:
    ///
    /// 1. **the hypothesis itself** — `h : 0 < b`, which is what the `dite`
    ///    spelling `if h : 0 < b then …` binds. This is the pre-existing
    ///    behaviour and stays first.
    /// 2. **`Nat.pos_of_ne_zero b h`** — for `h : ¬(b = 0)`, e.g. a
    ///    `if h : b ≠ 0 then …` spelling.
    /// 3. **`Nat.pos_of_ne_zero b (of_not_decide_eq_true _ _ h)`** — for
    ///    `h : ¬((b == 0) = true)`, which is what a **Bool test** binds once
    ///    `ite` has been normalized to `dite` (see `call_sites::ite_to_dite`).
    ///    This is the route that unblocks the verbatim
    ///    `if b == 0 then a else gcd b (a % b)`.
    /// 4. **a positive difference** — for `b ≡ B - k` and `h : k < B`, see
    ///    [`Self::difference_positivity_candidates`].
    ///
    /// Route 3 needs the Prop the Bool test decides and its `Decidable`
    /// instance. Rather than destructure the hypothesis — whose `==` elaborates
    /// through `BEq.beq`/`instBEqOfDecidableEq`, not through a literal `decide`
    /// head — both are RECONSTRUCTED from the divisor `b`, which the goal
    /// already gives us: `instBEqOfDecidableEq` is defined as
    /// `fun a b => @decide (@Eq α a b) (@decEq α inst a b)`, so the canonical
    /// instance for `b == 0` is `@decEq.{1} Nat instDecidableEqNat b 0`. If the
    /// hypothesis actually came from some other Bool test, the reconstructed
    /// term is not def-eq to it, inference fails, and the candidate is dropped
    /// — the fail-closed direction.
    ///
    /// Zero is offered in both spellings (`Nat.zero` and the literal `0`)
    /// because a source `0` elaborates through `OfNat.ofNat`; they are
    /// definitionally equal, and trying both costs two candidates rather than a
    /// dependence on which normal form the elaborator happened to leave behind.
    fn positivity_candidates(&self, b: &Expr, locals: &[(SurfaceName, FVarId, Expr)]) -> Vec<Expr> {
        let mut out: Vec<Expr> = locals.iter().map(|(_, fv, _)| Expr::fvar(*fv)).collect();
        // Route 4 goes LAST so every obligation an earlier route discharged
        // keeps the proof term it had.
        let difference = self.difference_positivity_candidates(b, locals);
        let out_with_difference = |mut out: Vec<Expr>| {
            out.extend(difference.iter().cloned());
            out
        };

        let pos_name = Name::from_string("Nat.pos_of_ne_zero");
        if self.env.get_const(&pos_name).is_none() {
            return out_with_difference(out);
        }
        let pos_of_ne_zero = Expr::const_(pos_name, vec![]);
        let bridge_name = Name::from_string("of_not_decide_eq_true");
        let bridge = self
            .env
            .get_const(&bridge_name)
            .map(|_| Expr::const_(bridge_name, vec![]));

        // `Nat`, `Eq`/`decEq` at `Sort 1` (Nat : Type 0), and the two `0`s.
        let l1 = clean_kernel::level::Level::succ(clean_kernel::level::Level::zero());
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let eq_c = Expr::const_(Name::from_string("Eq"), vec![l1.clone()]);
        let dec_eq_fn = Expr::const_(Name::from_string("decEq"), vec![l1]);
        let dec_eq_nat = Expr::const_(Name::from_string("instDecidableEqNat"), vec![]);
        let zeros = [
            Expr::const_(Name::from_string("Nat.zero"), vec![]),
            Expr::nat_lit(0),
        ];

        for (_, fvar, _) in locals {
            let h = Expr::fvar(*fvar);
            // Route 2: h : ¬(b = 0).
            out.push(Expr::apps(pos_of_ne_zero.clone(), [b.clone(), h.clone()]));
            // Route 3: h : ¬((b == 0) = true).
            let Some(bridge) = bridge.as_ref() else {
                continue;
            };
            for zero in &zeros {
                let eq_b_zero = Expr::apps(eq_c.clone(), [nat.clone(), b.clone(), zero.clone()]);
                let inst = Expr::apps(
                    dec_eq_fn.clone(),
                    [nat.clone(), dec_eq_nat.clone(), b.clone(), zero.clone()],
                );
                let ne = Expr::apps(bridge.clone(), [eq_b_zero, inst, h.clone()]);
                out.push(Expr::apps(pos_of_ne_zero.clone(), [b.clone(), ne]));
            }
        }
        out_with_difference(out)
    }

    /// **Route 4 — a positive difference.** Candidate proofs of
    /// `Nat.lt 0 (B - k)` from a hypothesis `h : k < B`: the count-up loop's
    /// obligation (`go (i + 1)` under `if h : i < limit`, measure
    /// `limit - i`, K5 probe b2) is `limit - (i + 1) < limit - i`, which is
    /// definitionally `(limit - i) - 1 < limit - i`, so tier 2's
    /// `Nat.sub_lt (limit - i) 1 pos _` closes it once `pos : 0 < limit - i`
    /// is in hand. Lean's `Nat.sub_pos_of_lt` is not in the prelude, so the
    /// candidate is assembled from three that are (all constructive,
    /// axiom-free prelude theorems):
    ///
    /// ```text
    /// h₁ : 1 + k ≤ B           := Eq.subst (Nat.add_comm k 1) h      -- h : k + 1 ≤ B
    /// h₂ : (1 + k) - k ≤ B - k := Nat.sub_le_sub_right (1 + k) B k h₁
    /// h₃ : 1 ≤ B - k           := Eq.subst (Nat.add_sub_cancel 1 k) h₂
    /// ```
    ///
    /// and `1 ≤ B - k` is `0 < B - k`. As for every route, a candidate built
    /// from an unrelated hypothesis fails the caller's strict recheck.
    fn difference_positivity_candidates(
        &self,
        b: &Expr,
        locals: &[(SurfaceName, FVarId, Expr)],
    ) -> Vec<Expr> {
        let Some((minuend, subtrahend)) = sub_parts(b) else {
            return Vec::new();
        };
        let names = [
            "Eq.subst",
            "Nat.add_comm",
            "Nat.add_sub_cancel",
            "Nat.sub_le_sub_right",
            "Nat.le",
            "Nat.add",
            "Nat.sub",
        ];
        if names
            .iter()
            .any(|n| self.env.get_const(&Name::from_string(n)).is_none())
        {
            return Vec::new();
        }
        let c = |n: &str| Expr::const_(Name::from_string(n), vec![]);
        let l1 = clean_kernel::level::Level::succ(clean_kernel::level::Level::zero());
        let eq_subst = Expr::const_(Name::from_string("Eq.subst"), vec![l1]);
        let nat = c("Nat");
        let one = Expr::nat_lit(1);
        let add = |x: Expr, y: Expr| Expr::apps(c("Nat.add"), [x, y]);
        let sub = |x: Expr, y: Expr| Expr::apps(c("Nat.sub"), [x, y]);
        let le_motive = |rhs: &Expr| {
            Expr::lam(
                clean_kernel::BinderInfo::Default,
                nat.clone(),
                Expr::apps(c("Nat.le"), [Expr::bvar(0), rhs.clone()]),
            )
        };
        let k_plus_one = add(subtrahend.clone(), one.clone());
        let one_plus_k = add(one.clone(), subtrahend.clone());
        let difference = sub(minuend.clone(), subtrahend.clone());
        locals
            .iter()
            .map(|(_, fvar, _)| {
                let h1 = Expr::apps(
                    eq_subst.clone(),
                    [
                        nat.clone(),
                        le_motive(&minuend),
                        k_plus_one.clone(),
                        one_plus_k.clone(),
                        Expr::apps(c("Nat.add_comm"), [subtrahend.clone(), one.clone()]),
                        Expr::fvar(*fvar),
                    ],
                );
                let h2 = Expr::apps(
                    c("Nat.sub_le_sub_right"),
                    [one_plus_k.clone(), minuend.clone(), subtrahend.clone(), h1],
                );
                Expr::apps(
                    eq_subst.clone(),
                    [
                        nat.clone(),
                        le_motive(&difference),
                        sub(one_plus_k.clone(), subtrahend.clone()),
                        one.clone(),
                        Expr::apps(c("Nat.add_sub_cancel"), [one.clone(), subtrahend.clone()]),
                        h2,
                    ],
                )
            })
            .collect()
    }

    /// Strict validation of a decreasing-proof candidate: no sorry, and the
    /// STRICTLY-inferred type (App arguments checked) is def-eq to the goal.
    /// Terms with unsolved metavariables fail inference (a meta instantiates
    /// to an unknown fvar) and are therefore refused too.
    pub(super) fn recheck_decreasing_proof(&self, proof: &Expr, goal: &Expr) -> bool {
        if proof.has_sorry() {
            return false;
        }
        match self.infer_type_full(proof) {
            Ok(ty) => self.is_def_eq(&ty, goal),
            Err(_) => false,
        }
    }
}

/// The strategy used to discharge a decreasing proof obligation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DecreasingStrategy {
    /// User-provided `decreasing_by` tactic succeeded.
    UserTactic,
    /// Default `simp_arith` succeeded.
    SimpArith,
    /// Default `mathverse` succeeded.
    Mathverse,
    /// All strategies failed; an unresolved proof metavariable was inserted.
    Sorry,
}

/// Result of attempting to build a decreasing proof.
#[derive(Debug, Clone)]
// Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
// keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[allow(dead_code)]
pub(crate) struct DecreasingProof {
    /// The proof term of type `measure(arg') < measure(arg)`.
    pub(crate) proof: Expr,
    /// Which strategy produced this proof.
    pub(crate) strategy: DecreasingStrategy,
}

/// A proof obligation for a single recursive call site.
#[derive(Debug, Clone)]
pub(crate) struct DecreasingObligation {
    /// The goal type: `rel rec_arg current_arg` (typically `measure(x') < measure(x)`).
    pub(crate) goal_type: Expr,
    /// The recursive argument expression at this call site.
    // Staged Lean4-parity scaffold, exercised by unit tests only; the live
    // pipeline reads only `goal_type` until the phase-2 proof builder lands.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) rec_arg: Expr,
    /// The current argument being decreased.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) current_arg: Expr,
}

impl DecreasingObligation {
    /// Create a new decreasing obligation.
    // Staged Lean4-parity scaffold, exercised by unit tests only; the live
    // pipeline builds its obligation goals inline in `call_sites`.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn new(goal_type: Expr, rec_arg: Expr, current_arg: Expr) -> Self {
        Self {
            goal_type,
            rec_arg,
            current_arg,
        }
    }
}

/// Build the decreasing proof goal type for a Nat-valued measure.
///
/// Given `measure : α → Nat`, `rec_arg : α`, `current_arg : α`, produces:
///   `Nat.lt (measure rec_arg) (measure current_arg)`
/// which is:
///   `LT.lt.{0} Nat instLTNat (measure rec_arg) (measure current_arg)`
/// Strip any `MData` wrappers so a spine match sees the term itself.
fn strip_mdata(mut e: &Expr) -> &Expr {
    while let ExprKind::MData(_, inner) = e.kind() {
        e = inner;
    }
    e
}

/// Split `Nat.lt lhs rhs` — the shape every decreasing obligation is built in
/// (`call_sites::rewrite_app_spine`). `None` for any other head, so a tier
/// keyed on this never fires against a goal it did not recognise.
pub(super) fn split_nat_lt(goal: &Expr) -> Option<(Expr, Expr)> {
    let goal = strip_mdata(goal);
    let ExprKind::App(lhs_fn, rhs) = goal.kind() else {
        return None;
    };
    let ExprKind::App(head, lhs) = strip_mdata(lhs_fn).kind() else {
        return None;
    };
    match strip_mdata(head).kind() {
        ExprKind::Const(name, _) if *name == Name::from_string("Nat.lt") => {
            Some((Expr::clone(lhs), Expr::clone(rhs)))
        }
        _ => None,
    }
}

/// The left-hand side of a `Nat.lt` goal. Separate from [`split_nat_lt`] only
/// so a caller that already has the right-hand side can ask for the left one
/// without re-destructuring.
fn lhs_of(goal: &Expr) -> Option<Expr> {
    split_nat_lt(goal).map(|(lhs, _)| lhs)
}

/// The SUBTRAHEND of a difference, in either spelling the elaborator produces:
/// the raw `Nat.sub a b`, or the `-` notation
/// `@HSub.hSub Nat Nat Nat instHSubNat a b`.
///
/// Only the subtrahend is read. The minuend is deliberately taken from the
/// obligation's right-hand side by the caller, so the two can never be assumed
/// equal — and if they are not, the strict recheck refuses the candidate.
fn sub_subtrahend(e: &Expr) -> Option<Expr> {
    let e = strip_mdata(e);
    let head = e.get_app_fn();
    let args = e.get_app_args();
    let ExprKind::Const(name, _) = strip_mdata(head).kind() else {
        return None;
    };
    if *name == Name::from_string("Nat.sub") && args.len() == 2 {
        return Some(Expr::clone(args[1]));
    }
    if *name == Name::from_string("HSub.hSub") && args.len() == 6 {
        return Some(Expr::clone(args[5]));
    }
    None
}

/// The minuend and subtrahend of a difference, in either spelling (see
/// [`sub_subtrahend`]).
fn sub_parts(e: &Expr) -> Option<(Expr, Expr)> {
    let e = strip_mdata(e);
    let head = e.get_app_fn();
    let args = e.get_app_args();
    let ExprKind::Const(name, _) = strip_mdata(head).kind() else {
        return None;
    };
    if *name == Name::from_string("Nat.sub") && args.len() == 2 {
        return Some((Expr::clone(args[0]), Expr::clone(args[1])));
    }
    if *name == Name::from_string("HSub.hSub") && args.len() == 6 {
        return Some((Expr::clone(args[4]), Expr::clone(args[5])));
    }
    None
}

/// `Nat.lt lhs rhs` — the shape every decreasing obligation is built in, and
/// the shape the named-theorem tiers above key on. Shared with
/// [`super::call_sites`] so the two cannot drift into different spellings of
/// the same goal.
pub(super) fn nat_lt_goal(lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Nat.lt"), vec![]),
        [lhs, rhs],
    )
}

/// How deep the sum-congruence tier may recurse. `a + b` needs 1, `a + b + c`
/// needs 2; the budget is the nesting depth of `+` in a measure, and it is
/// bounded so a pathological measure cannot make the cascade run away.
const SUM_CONGRUENCE_DEPTH: u8 = 4;

/// How deep the positivity tier (`0 < x + y` from a positive summand) may
/// recurse. Bounded by the `+` nesting of a residual, which is the same shape
/// as a measure.
const POSITIVITY_DEPTH: u8 = 4;

/// Per-tier recursion budgets for [`ElabCtx::discharge_decreasing_goal_at`].
///
/// One field per recursive tier, so a tier can hand a sub-goal a budget that
/// disables ONLY the tier that would otherwise re-derive the same sub-goal.
/// That is not cosmetic: the strict-residual tier reduces `L < R` to `0 < S`,
/// and `0 < S` has residual `S` again — without `without_residual` the cascade
/// would not terminate.
#[derive(Debug, Clone, Copy)]
pub(super) struct Budget {
    /// Tier 4, sum congruence.
    pub(super) sum: u8,
    /// Tier 6, positivity of a sum.
    pub(super) pos: u8,
    /// Tier 7, the strict linear residual.
    pub(super) residual: u8,
    /// Tier 8, truncated-subtraction case split.
    pub(super) split: u8,
}

impl Default for Budget {
    fn default() -> Self {
        Self {
            sum: SUM_CONGRUENCE_DEPTH,
            pos: POSITIVITY_DEPTH,
            residual: 1,
            split: 1,
        }
    }
}

impl Budget {
    /// One level deeper in the sum-congruence tier; every other budget is
    /// preserved.
    pub(super) fn descend_sum(self) -> Self {
        Self {
            sum: self.sum.saturating_sub(1),
            ..self
        }
    }

    /// One level deeper in the positivity tier.
    pub(super) fn descend_pos(self) -> Self {
        Self {
            pos: self.pos.saturating_sub(1),
            ..self
        }
    }

    /// One level deeper in the case-split tier. The branch goals get a FULL
    /// budget for every other tier — the point of the split is that the branch
    /// is an ordinary obligation again.
    pub(super) fn descend_split(self) -> Self {
        Self {
            split: self.split.saturating_sub(1),
            ..Self::default()
        }
    }

    /// The residual tier's own sub-goal budget: everything except another
    /// residual step, which would be the same goal.
    pub(super) fn without_residual(self) -> Self {
        Self {
            residual: 0,
            ..self
        }
    }
}

/// The NUMERATOR of a remainder expression, in either spelling the elaborator
/// produces: the raw `Nat.mod a b`, or the `%` notation
/// `@HMod.hMod Nat Nat Nat instHModNat a b`.
///
/// Only the numerator is read here. The divisor is deliberately taken from the
/// obligation's right-hand side by the caller, so the two can never be assumed
/// equal — and if they are not, the strict recheck refuses the candidate.
fn mod_numerator(e: &Expr) -> Option<Expr> {
    let e = strip_mdata(e);
    let head = e.get_app_fn();
    let args = e.get_app_args();
    let ExprKind::Const(name, _) = strip_mdata(head).kind() else {
        return None;
    };
    if *name == Name::from_string("Nat.mod") && args.len() == 2 {
        return Some(Expr::clone(args[0]));
    }
    if *name == Name::from_string("HMod.hMod") && args.len() == 6 {
        return Some(Expr::clone(args[4]));
    }
    None
}

// Staged Lean4-parity scaffold, exercised by unit tests only; the live
// pipeline builds its obligation goals inline in `call_sites`.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn build_nat_decreasing_goal(
    measure_fn: &Expr,
    rec_arg: &Expr,
    current_arg: &Expr,
) -> Expr {
    let measure_rec = Expr::app(measure_fn.clone(), rec_arg.clone());
    let measure_cur = Expr::app(measure_fn.clone(), current_arg.clone());

    // Nat.lt a b is definitionally: @LT.lt Nat instLTNat a b
    // But we can use the simpler encoding via the `<` notation
    let nat_lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);
    Expr::app(Expr::app(nat_lt, measure_rec), measure_cur)
}

// `try_tactic_on_goal` is the one member of the old staged block with a LIVE
// production caller (the fail-closed cascade above), so the split leaves it
// here rather than in the caller-less scaffold.
impl ElabCtx<'_> {
    /// Try to prove a goal using the given tactics.
    ///
    /// Creates a temporary proof state and attempts to close the goal.
    /// Returns `Ok(proof_term)` on success, `Err` on failure.
    fn try_tactic_on_goal(
        &mut self,
        goal_type: &Expr,
        tactics: &[SurfaceTactic],
    ) -> Result<Expr, ElabError> {
        use crate::tactic::ProofState;

        let elab_locals: Vec<_> = self
            .locals
            .iter()
            .map(|(name, fvar, ty)| crate::tactic::LocalDecl {
                binder_info: self.locals.binder_info(*fvar),
                fvar: *fvar,
                name: name.clone(),
                ty: ty.clone(),
                value: None,
            })
            .collect();
        let mut ps = ProofState::with_instances_and_elab_context(
            self.env.clone(),
            goal_type.clone(),
            self.instances.clone(),
            elab_locals,
        );

        // U2 stage 1a — same bridge seeding as `elab_by_tactic`: this is the
        // second ElabCtx→ProofState entry point, and it must not re-mint a
        // level name the enclosing declaration already uses. Decreasing
        // goals are Nat-level and rarely touch levels, but the hygiene is
        // the same.
        let mut tactic_rigid = self.metas.rigid_level_params_snapshot();
        for name in &self.universe_params {
            tactic_rigid.insert(name.name().clone());
        }
        ps.seed_universe_world(
            self.universe_params.clone(),
            self.level_mint.clone(),
            tactic_rigid,
        );
        ps.set_instance_visibility(self.instance_visibility());

        for tac in tactics {
            self.eval_tactic(&mut ps, tac)?;
        }

        let proof = ps.closed_proof().ok_or_else(|| ElabError::Unsupported {
            feature: "decreasing proof: tactic did not close goal".to_owned(),
        })?;
        // Realize tactic-side level solutions, as in `elab_by_tactic`.
        Ok(ps.metas.instantiate_levels(&proof))
    }
}

#[path = "decreasing_staged.rs"]
mod staged;

#[cfg(test)]
#[path = "decreasing_tests.rs"]
mod decreasing_tests;
