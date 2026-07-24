// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! IH-rewriting induction step for the structural-induction lane.
//!
//! The generic single-recursor lane ([`crate::engine_induction_assembly`])
//! proves *base/structural* equational lemmas — `n + 0 = n`, `l ++ [] = l` —
//! whose constructor case closes by reflexivity or by congruence that bottoms
//! out directly in the induction hypothesis. It could NOT prove a theorem whose
//! inductive **step must rewrite with the IH**, such as
//!
//! * `add_assoc`  `∀ n m k, (n+m)+k = n+(m+k)`, and
//! * `append_assoc` `∀ l₁ l₂ l₃, (l₁++l₂)++l₃ = l₁++(l₂++l₃)`,
//!
//! because for those the constructor minor premise's *conclusion is itself a
//! `∀`* (the motive `P` is a `∀`-telescope ending in an `Eq`), and the IH is the
//! matching `∀`-telescope — neither a bare equation the existing
//! reflexivity/congruence prover can read, nor something the SMT/superposition
//! engines close over a minimal environment.
//!
//! This module adds the IH-rewrite step. Given a step conclusion `∀ ys, l = r`
//! and an in-scope induction hypothesis `ih : ∀ ys, l' = r'`, it
//!
//!   1. **introduces** the inner `∀ ys` binders as fresh locals
//!      ([`AutomationEngine::prove_goal_rewrite`]) so both the goal and the IH
//!      become bare equations at those locals;
//!   2. **specialises** every `∀`-quantified induction hypothesis at the
//!      introduced locals ([`specialized_ih_facts`]) — `ih y₁ … yₙ`, a genuine
//!      kernel term — yielding a *directed rewrite equation* `l'[ys] = r'[ys]`;
//!   3. **closes** the bare goal ([`AutomationEngine::prove_eq_rewrite`]) by
//!      reflexivity, by the specialised IH used as an equation (the rewrite), or
//!      by congruence that recurses to one of those — after `whnf`-unfolding the
//!      recurrence on the constructor side (`Nat.add a (succ b) ⤳ succ (a+b)`,
//!      `(h::t) ++ ys ⤳ h :: (t++ys)`), which is what exposes the IH-shaped
//!      residual.
//!
//! It also adds **induction-variable selection** for multi-binder goals
//! ([`AutomationEngine::try_induction_reordered`]): `add_assoc` does not close by
//! induction on its *outermost* variable (the base case `(0+m)+k = 0+(m+k)`
//! would need a `0+m = m` lemma) but does close by induction on its *third*
//! variable `k`. When inducting on the outermost binder fails, the lane reorders
//! a later (closed-domain, registered-inductive) binder to the front and retries.
//!
//! Soundness: this is on the *search* side, not the TCB. Every emitted term is a
//! genuine recursor application whose minor premises are filled by `Eq.refl` /
//! `congrArg` / a specialised-IH application — never `sorry`/axiom. Each
//! candidate is kernel-checked (`infer_type` + `is_def_eq`) before it is used,
//! and the whole `@I.rec` term is re-checked against the original goal by
//! [`crate::engine_induction`]'s final gate; a wrong rewrite or a mis-built
//! reorder adapter simply fails that check and is never returned as success.

use std::time::Instant;

use clean_kernel::{BinderData, Environment, Expr, ExprKind, FVarId, LocalContext, Name};

use crate::engine::AutomationEngine;
use crate::engine_induction::{
    build_eq, congr_arg, eq_refl, kernel_accepts, parse_eq, type_checker,
};
use crate::engine_induction_aux::{chaining_facts, eq_trans};
use crate::engine_induction_match::{refold_nat_add, rewrite_lhs_with_fact};

/// Maximum congruence / rewrite recursion depth when discharging an equation.
///
/// Bounds the `f (g … x) = f (g … y)` peeling in
/// [`AutomationEngine::prove_eq_rewrite`] so a pathological goal terminates.
pub(crate) const REWRITE_DEPTH: u32 = 12;

/// A specialised induction hypothesis: a kernel term `witness` (an application
/// `ih y₁ … yₙ`) together with its inferred, `whnf`-reduced equation type.
type RewriteFact = (Expr, Expr);

impl AutomationEngine {
    /// Discharge a constructor minor-premise conclusion that may be a
    /// `∀ ys, l = r` telescope — the IH-rewriting induction step.
    ///
    /// Introduces the inner `∀ ys` binders as fresh locals layered on `ctx`,
    /// recursing until a non-`Pi` leaf, then proves the resulting equation with
    /// [`Self::prove_eq_rewrite`] using the in-scope induction hypotheses
    /// (specialised at the introduced locals, see [`specialized_ih_facts`]) as
    /// directed rewrite equations. Re-binds the introduced locals as lambdas so
    /// the returned term inhabits the original `∀ ys, l = r`.
    ///
    /// A non-equational leaf is deferred to the general [`Self::discharge_subgoal`]
    /// (engines / nested induction), preserving the lane's behaviour for
    /// inductives whose conclusions are not equations.
    pub(crate) fn prove_goal_rewrite(
        &self,
        env: &Environment,
        goal: &Expr,
        ctx: &LocalContext,
        deadline: Instant,
        fuel: u32,
    ) -> Option<Expr> {
        if Instant::now() >= deadline {
            return None;
        }
        let g = type_checker(env, ctx).whnf(goal);

        if let ExprKind::Pi(bd, dom_arc, body_arc) = g.strip_mdata().kind() {
            let bd: BinderData = *bd;
            let dom = (**dom_arc).clone();
            let body = (**body_arc).clone();
            let mut inner = ctx.clone();
            let y = inner.push(Name::from_string("ind.y"), dom.clone(), bd);
            let opened = body.instantiate(&Expr::fvar(y));
            let sub = self.prove_goal_rewrite(env, &opened, &inner, deadline, fuel)?;
            return Some(Expr::lam(bd, dom, sub.abstract_fvar(y)));
        }

        // Leaf. An equation is closed by the rewrite-aware prover (with the
        // specialised IHs as rewrite equations); any other proposition is left to
        // the engine/nested-induction fallback.
        if parse_eq(&g).is_some() {
            let mut facts = specialized_ih_facts(env, ctx);
            // Auxiliary-lemma synthesis: when a side is stuck on a constructor in
            // the inducted operand (`succ k + m`, `0 + m`), synthesise + prove +
            // kernel-check the bridging lemma (`succ_add` / `zero_add`) and add it
            // as a directed rewrite fact. This is what unlocks `add_comm`.
            facts.extend(self.synthesize_bridging_facts(env, ctx, &g, deadline));
            return self.prove_eq_rewrite(env, ctx, &g, &facts, deadline, REWRITE_DEPTH);
        }
        self.discharge_subgoal(env, &g, ctx, deadline, fuel)
    }

    /// Prove an equation `goal` (`@Eq.{u} T L R`) in `ctx` using kernel
    /// primitives plus a set of directed rewrite equations `facts`, returning a
    /// kernel-checked term or `None`.
    ///
    /// Strategy, each candidate re-checked against `goal`:
    ///   1. **reflexivity** — `L ≟ R` ⇒ `@Eq.refl.{u} T L`;
    ///   2. **rewrite with a specialised IH** — a `fact` whose sides are
    ///      def-eq to `(L, R)` is used directly (this is the IH-rewrite: e.g.
    ///      `ih l₂ l₃ : (t++l₂)++l₃ = t++(l₂++l₃)` closing the `append_assoc`
    ///      residual);
    ///   3. **assumption** — a bare equation local `h : Eq _ a b` with `a ≟ L`,
    ///      `b ≟ R`;
    ///   4. **congruence** — `whnf` both sides; on a shared application head `f`,
    ///      recurse on the arguments and wrap with `@congrArg` (this unfolds the
    ///      constructor-side recurrence and exposes the IH-shaped residual).
    pub(crate) fn prove_eq_rewrite(
        &self,
        env: &Environment,
        ctx: &LocalContext,
        goal: &Expr,
        facts: &[RewriteFact],
        deadline: Instant,
        depth: u32,
    ) -> Option<Expr> {
        if Instant::now() >= deadline {
            return None;
        }
        let (goal_levels, ty, lhs, rhs) = parse_eq(goal)?;
        let beta_level = goal_levels.first().cloned()?;
        let tc = type_checker(env, ctx);

        // 1. reflexivity.
        if tc.is_def_eq(&lhs, &rhs) {
            let term = eq_refl(&goal_levels, &ty, &lhs);
            if kernel_accepts(env, ctx, &term, goal) {
                return Some(term);
            }
        }

        // 2. rewrite with a specialised induction hypothesis.
        for (witness, fact_ty) in facts {
            let Some((_lvl, _hty, a, b)) = parse_eq(fact_ty) else {
                continue;
            };
            if tc.is_def_eq(&lhs, &a)
                && tc.is_def_eq(&rhs, &b)
                && kernel_accepts(env, ctx, witness, goal)
            {
                return Some(witness.clone());
            }
        }

        // 3. a bare equation local (a single-variable IH, or any equality fact).
        for decl in ctx.iter() {
            let Some((_lvl, _hty, a, b)) = parse_eq(&decl.type_) else {
                continue;
            };
            if tc.is_def_eq(&lhs, &a) && tc.is_def_eq(&rhs, &b) {
                let term = Expr::fvar(decl.id);
                if kernel_accepts(env, ctx, &term, goal) {
                    return Some(term);
                }
            }
        }

        // 4. directed rewrite-with-fact via transitivity. Rewrite the left side
        //    with a fact `a = b` whose `a` matches `L` (and makes progress), then
        //    prove the residual `b = R`, combining with `Eq.trans`. This is what
        //    bridges the recursion-side mismatch: the synthesised
        //    `succ a + b = succ (a+b)` rewrites the stuck `succ k + m` to
        //    `succ (k+m)`, after which congruence reaches the IH `k+m = m+k`.
        if depth == 0 {
            return None;
        }
        for (witness, fact_ty) in facts {
            let Some((_lvl, _hty, a, b)) = parse_eq(fact_ty) else {
                continue;
            };
            if tc.is_def_eq(&lhs, &a) && !tc.is_def_eq(&lhs, &b) {
                let residual = build_eq(&beta_level, &ty, &b, &rhs);
                let Some(sub) =
                    self.prove_eq_rewrite(env, ctx, &residual, facts, deadline, depth - 1)
                else {
                    continue;
                };
                let term = eq_trans(&beta_level, &ty, &lhs, &b, &rhs, witness, &sub);
                if kernel_accepts(env, ctx, &term, goal) {
                    return Some(term);
                }
            }
        }

        // 5. congruence on a shared application head.
        if let Some(term) = self.congruence_step(
            env,
            ctx,
            goal,
            &tc,
            &ty,
            &lhs,
            &rhs,
            &beta_level,
            facts,
            deadline,
            depth,
        ) {
            return Some(term);
        }

        // 6. sub-term rewrite. The two sides share no reducible head (both stuck
        //    on different operands — `succ x * j + x` vs `(x*j + x) + j`), so
        //    congruence cannot reach the sub-position where a fact applies. Rewrite
        //    the LEFT side at a sub-term with a directed fact — the specialised IHs
        //    in `facts` *and* the `∀`-quantified bridge lemmas accumulated by
        //    chaining ([`chaining_facts`], e.g. `add_right_comm`) — then discharge
        //    the residual and stitch with `Eq.trans`. Every built term is
        //    kernel-checked before it is trusted.
        let mut all_facts: Vec<RewriteFact> = facts.to_vec();
        all_facts.extend(chaining_facts());
        // Re-fold `Nat.add`'s recursor form (exposed by the `succ`-peel) back to a
        // surface `Nat.add`, so the `∀`-fact patterns (`add_right_comm`) match. The
        // fold is definitionally equal, so proving `lhs_s = rhs` still discharges
        // the goal `lhs = rhs` under the final `kernel_accepts`.
        let lhs_s = refold_nat_add(&lhs);
        for fact in &all_facts {
            if Instant::now() >= deadline {
                return None;
            }
            let Some((lhs2, h1)) = rewrite_lhs_with_fact(env, ctx, &lhs_s, fact) else {
                continue;
            };
            if tc.is_def_eq(&lhs_s, &lhs2) {
                continue;
            }
            let residual = build_eq(&beta_level, &ty, &lhs2, &rhs);
            let Some(sub) = self.prove_eq_rewrite(env, ctx, &residual, facts, deadline, depth - 1)
            else {
                continue;
            };
            let term = eq_trans(&beta_level, &ty, &lhs_s, &lhs2, &rhs, &h1, &sub);
            if kernel_accepts(env, ctx, &term, goal) {
                return Some(term);
            }
        }
        None
    }

    /// Structural congruence on a shared `whnf` application head: reduce
    /// `f a_l = f a_r` to `a_l = a_r`, discharge it, and wrap with `@congrArg`.
    /// `None` when the sides do not share a head (the sub-term rewrite handles
    /// that case).
    #[allow(clippy::too_many_arguments)]
    fn congruence_step(
        &self,
        env: &Environment,
        ctx: &LocalContext,
        goal: &Expr,
        tc: &clean_kernel::TypeChecker<'_>,
        ty: &Expr,
        lhs: &Expr,
        rhs: &Expr,
        beta_level: &clean_kernel::Level,
        facts: &[RewriteFact],
        deadline: Instant,
        depth: u32,
    ) -> Option<Expr> {
        let lhs_w = tc.whnf(lhs);
        let rhs_w = tc.whnf(rhs);
        let (ExprKind::App(f_l, a_l), ExprKind::App(f_r, a_r)) = (lhs_w.kind(), rhs_w.kind())
        else {
            return None;
        };
        if !tc.is_def_eq(f_l, f_r) {
            return None;
        }
        let arg_ty = tc.infer_type(a_l).ok()?;
        let arg_sort = tc.whnf(&tc.infer_type(&arg_ty).ok()?);
        let ExprKind::Sort(arg_level) = arg_sort.strip_mdata().kind() else {
            return None;
        };
        let arg_level = arg_level.normalize();
        let arg_goal = build_eq(&arg_level, &arg_ty, a_l, a_r);
        let sub = self.prove_eq_rewrite(env, ctx, &arg_goal, facts, deadline, depth - 1)?;
        let term = congr_arg(&arg_level, beta_level, &arg_ty, ty, a_l, a_r, f_l, &sub);
        kernel_accepts(env, ctx, &term, goal).then_some(term)
    }

    /// Induction-variable selection: prove `goal = ∀ x₀ … x_{n-1}, B` by
    /// inducting on a *non-outermost* leading binder.
    ///
    /// Peels the maximal leading telescope of `Pi` binders whose domain is
    /// **closed** (no loose bvars — so reordering is type-preserving), and for
    /// each later binder whose domain is a registered index-free inductive,
    /// reorders that binder to the front and retries [`Self::induct_on_outermost`]
    /// on the permuted goal, wrapping the result in a binder-reordering adapter.
    /// `add_assoc` closes here by induction on its third variable.
    pub(crate) fn try_induction_reordered(
        &self,
        env: &Environment,
        goal: &Expr,
        base_ctx: &LocalContext,
        deadline: Instant,
        fuel: u32,
    ) -> Option<Expr> {
        let mut ctx = base_ctx.clone();
        let mut vars: Vec<(FVarId, BinderData, Expr)> = Vec::new();
        let mut body = goal.clone();
        loop {
            let stripped = body.strip_mdata();
            let ExprKind::Pi(bd, dom_arc, body_arc) = stripped.kind() else {
                break;
            };
            let dom = (**dom_arc).clone();
            // A binder whose domain mentions an earlier binder cannot be freely
            // reordered; stop the telescope here.
            if dom.has_loose_bvars_quick() {
                break;
            }
            let bd: BinderData = *bd;
            let fvar = ctx.push(Name::from_string("ind.perm"), dom.clone(), bd);
            body = body_arc.instantiate(&Expr::fvar(fvar));
            vars.push((fvar, bd, dom));
        }
        if vars.len() < 2 {
            return None;
        }

        for target in 1..vars.len() {
            if Instant::now() >= deadline {
                return None;
            }
            if !is_inductive_domain(env, &vars[target].2) {
                continue;
            }
            if let Some(term) =
                self.induct_reordered_on(env, goal, base_ctx, &vars, &body, target, deadline, fuel)
            {
                return Some(term);
            }
        }
        None
    }

    /// Reorder binder `target` of `goal` to the front, induct on it, and wrap the
    /// proof in an adapter that restores the original binder order.
    ///
    /// `vars` are the opened leading binders (fvar, binder data, closed domain)
    /// and `body` is `goal`'s body opened under them. The returned term is
    /// kernel-checked against `goal` before being trusted.
    #[allow(clippy::too_many_arguments)]
    fn induct_reordered_on(
        &self,
        env: &Environment,
        goal: &Expr,
        base_ctx: &LocalContext,
        vars: &[(FVarId, BinderData, Expr)],
        body: &Expr,
        target: usize,
        deadline: Instant,
        fuel: u32,
    ) -> Option<Expr> {
        let n = vars.len();
        // perm = [target, 0, 1, …, target-1, target+1, …, n-1].
        let mut perm: Vec<usize> = Vec::with_capacity(n);
        perm.push(target);
        perm.extend((0..n).filter(|&i| i != target));

        // Permuted goal `∀ (vars[perm[0]]) … , body`: abstract the opened fvars
        // innermost-first (reverse of the binder order). Domains are closed, so
        // abstraction does not disturb them.
        let mut permuted = body.clone();
        for &idx in perm.iter().rev() {
            let (fvar, bd, dom) = &vars[idx];
            permuted = Expr::pi(*bd, dom.clone(), permuted.abstract_fvar(*fvar));
        }

        let proof = self.induct_on_outermost(env, &permuted, base_ctx, deadline, fuel)?;

        // Adapter `fun (x₀ … x_{n-1}) => proof x_{perm[0]} … x_{perm[n-1]}`:
        // open the original telescope under fresh locals, apply `proof` in
        // permuted order, then close as lambdas in original order.
        let mut adapt_ctx = base_ctx.clone();
        let fresh: Vec<(FVarId, BinderData, Expr)> = vars
            .iter()
            .map(|(_f, bd, dom)| {
                let g = adapt_ctx.push(Name::from_string("ind.adapt"), dom.clone(), *bd);
                (g, *bd, dom.clone())
            })
            .collect();
        let mut adapter = perm
            .iter()
            .fold(proof, |acc, &idx| Expr::app(acc, Expr::fvar(fresh[idx].0)));
        for (g, bd, dom) in fresh.iter().rev() {
            adapter = Expr::lam(*bd, dom.clone(), adapter.abstract_fvar(*g));
        }

        if kernel_accepts(env, base_ctx, &adapter, goal) {
            return Some(adapter);
        }
        None
    }
}

/// Collect the in-scope induction hypotheses, each specialised at the freshly
/// introduced inner binders, as directed rewrite equations.
///
/// An induction hypothesis for a `∀`-motive is a local `ih : ∀ ys, l = r` whose
/// arity `a` equals the number of inner binders just introduced — which are the
/// last `a` locals of `ctx` (pushed after the constructor's field/IH binders).
/// Applying `ih` to those locals, in order, yields `ih y₁ … yₐ : l[ys] = r[ys]`,
/// the specialised rewrite equation the step needs. A bare (single-variable) IH
/// has arity `0` and is handled directly by [`AutomationEngine::prove_eq_rewrite`]'s
/// assumption branch, so it is skipped here.
///
/// Every candidate is type-inferred and checked to be an equation before it is
/// returned; a mis-applied hypothesis simply does not produce a fact (and could
/// never be unsound — its witness type is what the kernel infers).
fn specialized_ih_facts(env: &Environment, ctx: &LocalContext) -> Vec<RewriteFact> {
    let decls: Vec<_> = ctx.iter().collect();
    let n = decls.len();
    let tc = type_checker(env, ctx);
    let mut facts = Vec::new();
    for decl in &decls {
        let arity = leading_pi_arity(&decl.type_);
        if arity == 0 || arity > n {
            continue;
        }
        let args: Vec<Expr> = decls[n - arity..]
            .iter()
            .map(|d| Expr::fvar(d.id))
            .collect();
        let witness = Expr::apps(Expr::fvar(decl.id), args);
        let Ok(witness_ty) = tc.infer_type(&witness) else {
            continue;
        };
        let witness_ty = tc.whnf(&witness_ty);
        if parse_eq(&witness_ty).is_some() {
            facts.push((witness, witness_ty));
        }
    }
    facts
}

/// Number of leading `Pi` binders of `ty` whose telescope ends in an `Eq`.
///
/// Returns `0` when `ty` is not a `∀ …, Eq …` (so it is not a `∀`-quantified
/// induction hypothesis). The binder bodies are advanced structurally (a `Pi` is
/// already in whnf), so this is a cheap syntactic count.
fn leading_pi_arity(ty: &Expr) -> usize {
    let mut arity = 0usize;
    let mut current = ty.clone();
    while let ExprKind::Pi(_, _dom, body) = current.strip_mdata().kind() {
        arity += 1;
        // Advance past the binder; the substituted value is irrelevant to the
        // structural shape (we only need the count and the final head).
        current = body.instantiate(&Expr::fvar(FVarId::new(0)));
    }
    if parse_eq(&current).is_some() {
        arity
    } else {
        0
    }
}

/// `true` iff `dom`'s head is a registered, index-free inductive type former
/// (so [`AutomationEngine::induct_on_outermost`] can build its recursor).
fn is_inductive_domain(env: &Environment, dom: &Expr) -> bool {
    let ExprKind::Const(name, _) = dom.strip_mdata().get_app_fn().kind() else {
        return false;
    };
    env.inductive_info(name)
        .is_some_and(|info| info.num_indices == 0)
}
