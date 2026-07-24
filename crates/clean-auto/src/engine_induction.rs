// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structural-induction lane for [`crate::AutomationEngine`].
//!
//! Root capability this addresses: the fixed `smt → superposition → oracle`
//! pipeline (`engine_detailed::run_pipeline`) cannot prove a goal that *requires*
//! induction over an inductive variable — the solver-cache weak-area telemetry
//! measured `induction_required` at `0/3`. The classic example is
//! `∀ (n : Nat), 0 + n = n`: `Nat.add` recurses on its *second* argument, so
//! `0 + n` is stuck for a free `n` and no amount of EUF/congruence/superposition
//! closes it. It needs the `Nat.rec` eliminator.
//!
//! This module adds an additive lane (mirroring `bridge/prove_implication.rs`):
//! when the goal is `∀ (x : I p₁ … p_k), P x` for a registered **non-mutual,
//! index-free** inductive `I` (Nat, List, Bool, Option, Sum, Prod, …) and every
//! other engine has failed, it
//!
//!   1. peels the leading `∀` over `I`, reads off the motive `P`, and resolves
//!      `I`'s metadata from the environment ([`peel_inductive_forall`]);
//!   2. generates one subgoal **per constructor** — read straight off the
//!      recursor's own minor-premise types, so the field/IH shape is whatever
//!      the kernel says it is (Nat: `P 0` and `∀k, P k → P (k+1)`; List: `P []`
//!      and `∀ x xs, P xs → P (x::xs)` with the IH `P xs` in a fresh local
//!      context);
//!   3. discharges each subgoal — first with the *existing* engines (a fresh
//!      SMT/superposition run), then with a small self-contained equality prover
//!      (reflexivity + congruence-from-IH), then a fuel-bounded nested induction;
//!   4. assembles the proof term as a genuine recursor application
//!      `@I.rec.{levels} params (motive := fun x => P x) minor₁ … minor_m`
//!      ([`AutomationEngine::assemble_by_recursor`]), with the universe levels
//!      read off the inductive head constant in the goal and prefixed with the
//!      motive's universe in the kernel's mint order; and
//!   5. **kernel-checks** the assembled term (`infer_type` + `is_def_eq`) against
//!      the original `∀ x, P x` before trusting it.
//!
//! The generic path subsumes the original `Nat`-only lane: `Nat` is the
//! zero-parameter, zero-index, single-motive case (`@Nat.rec.{u} motive base
//! step`).
//!
//! Soundness: this lane is on the *search* side, not the TCB. The assembled term
//! is a real recursor application (never `sorry`/axiom); step (5) rejects any term
//! the kernel does not accept — including a wrong universe instantiation — and
//! each subgoal proof, from an engine or the built-in `Eq.refl`/`congrArg`
//! prover, is itself kernel-checked before it fills a minor premise. The
//! congruence prover yields a term *definitionally equal* to the required premise
//! (e.g. `List.cons α x (xs ++ []) = List.cons α x xs` for the `(x::xs) ++ [] =
//! x::xs` step), which the final assembly's `is_def_eq` absorbs.

use std::time::Instant;

use clean_kernel::{
    BinderInfo, Environment, Expr, ExprKind, Level, LevelVec, LocalContext, Name, TypeChecker,
};

use crate::engine::AutomationEngine;
use crate::engine_api::AutomationOutcome;
use crate::engine_induction_assembly::peel_inductive_forall;
use crate::engine_induction_rewrite::REWRITE_DEPTH;
use crate::proof_result::HypothesisWithProofFVar;
use crate::ProofResult;

/// Maximum nesting depth of the induction lane.
///
/// Bounds recursion so a pathological goal (e.g. `∀ n m k …`) cannot loop. Each
/// nested `∀ (·:Nat)` peel consumes one unit; subgoals discharged purely by the
/// base engines consume none.
pub(crate) const INDUCTION_FUEL: u32 = 4;

/// Maximum structural nesting depth of a goal the search will attempt.
///
/// The induction lane's per-subgoal kernel re-checks (`infer_type` + `is_def_eq`
/// over the assembled `@I.rec` term) and the base engines' goal translation are
/// recursive in the goal's *structure*. On a pathologically deep goal — say a
/// `∀ x₁ … x_n, …` telescope with `n` in the thousands, or a `succ^n …` spine —
/// a *single* such call runs for minutes (observed) and can overflow even a
/// 1 GiB stack. `INDUCTION_FUEL` bounds the *induction nesting* but not the
/// goal's own structural depth, which is what those costs scale with. Real goals
/// are far shallower than this rail, so a goal nested past it is declined up
/// front (`None`) rather than driving a runaway / overflow. This is a robustness
/// bound, not a capability limit, and is soundness-neutral (declining only
/// forgoes a proof attempt).
pub(crate) const MAX_GOAL_DEPTH: u32 = 128;

/// `true` iff `e` nests structurally deeper than `limit`.
///
/// Iterative (explicit worklist) so the check itself is overflow-safe on a
/// pathological term, and it bails the instant the bound is exceeded — so on a
/// too-deep goal it visits only `O(limit)` nodes down one spine, never the whole
/// term.
pub(crate) fn goal_depth_exceeds(e: &Expr, limit: u32) -> bool {
    let mut stack: Vec<(&Expr, u32)> = vec![(e, 0)];
    while let Some((cur, depth)) = stack.pop() {
        if depth > limit {
            return true;
        }
        let next = depth + 1;
        match cur.kind() {
            ExprKind::App(f, a) => {
                stack.push((&**f, next));
                stack.push((&**a, next));
            }
            ExprKind::Lam(_, dom, body) | ExprKind::Pi(_, dom, body) => {
                stack.push((&**dom, next));
                stack.push((&**body, next));
            }
            ExprKind::Let(_, ty, val, body, _) => {
                stack.push((&**ty, next));
                stack.push((&**val, next));
                stack.push((&**body, next));
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => {
                stack.push((&**inner, next));
            }
            _ => {}
        }
    }
    false
}

impl AutomationEngine {
    /// Public strategy entry point: try to prove `goal` by structural induction.
    ///
    /// Returns `Some(ProofResult)` only when the assembled recursor term
    /// kernel-checks against `goal`; `None` when `goal` is not a `∀ (x:I …), P x`
    /// over a registered non-mutual, index-free inductive `I`, or a subgoal could
    /// not be discharged. The returned proof term is closed (no `proof_context`)
    /// when called on a closed goal.
    pub fn prove_by_induction(
        &self,
        env: &Environment,
        goal: &Expr,
        timeout: std::time::Duration,
    ) -> Option<ProofResult> {
        let start = Instant::now();
        let deadline = start + timeout;
        let base_ctx = LocalContext::new();
        let term = self.try_induction_lane(env, goal, &base_ctx, deadline, INDUCTION_FUEL)?;
        Some(ProofResult::new(
            term,
            "proved by structural induction (recursor)",
            start.elapsed().as_millis() as u64,
            None,
        ))
    }

    /// Pipeline hook: try induction with a fresh fuel budget against `base_ctx`.
    ///
    /// Called from [`crate::engine_detailed`]'s `run_pipeline` after SMT and
    /// superposition fail. Returns the assembled, kernel-checked proof term (valid
    /// in `base_ctx`) or `None`.
    pub(crate) fn try_induction_lane(
        &self,
        env: &Environment,
        goal: &Expr,
        base_ctx: &LocalContext,
        deadline: Instant,
        fuel: u32,
    ) -> Option<Expr> {
        if fuel == 0 || Instant::now() >= deadline {
            return None;
        }
        // Robustness rail (BUG 2 / runaway): decline a pathologically deep goal
        // before peeling it. The assembly's kernel re-checks recurse in the goal's
        // structure, so a too-deep goal would otherwise drive a multi-minute run or
        // a stack overflow inside the kernel (which the per-step deadline poll
        // cannot interrupt mid-`infer_type`). Returns `None` gracefully.
        if goal_depth_exceeds(goal, MAX_GOAL_DEPTH) {
            return None;
        }

        // First try inducting on the goal's outermost `∀`-bound inductive
        // variable. This proves the base/structural lemmas (`0+n=n`, `l++[]=l`)
        // and any theorem whose step closes on the outermost variable
        // (`append_assoc`).
        if let Some(term) = self.induct_on_outermost(env, goal, base_ctx, deadline, fuel) {
            return Some(term);
        }

        // Otherwise try inducting on a *later* leading variable (reordered to the
        // front). `add_assoc` does not close on its outermost variable `n` (the
        // base case `(0+m)+k=0+(m+k)` would need a `0+m=m` lemma) but does close
        // by induction on its third variable `k`.
        self.try_induction_reordered(env, goal, base_ctx, deadline, fuel)
    }

    /// Prove `goal = ∀ (x : I …), P x` by inducting on its outermost binder.
    ///
    /// Peels the `∀`, builds the motive, assembles `@I.rec.{levels} params motive
    /// minor₁ … minor_m`, and kernel-checks the whole term against `goal`. Returns
    /// `None` for a non-inductive / mutual / indexed domain, or when a minor
    /// premise cannot be discharged.
    pub(crate) fn induct_on_outermost(
        &self,
        env: &Environment,
        goal: &Expr,
        base_ctx: &LocalContext,
        deadline: Instant,
        fuel: u32,
    ) -> Option<Expr> {
        // Peel `∀ (x : I …), P x` and resolve `I`'s recursor metadata. Declines
        // (`None`) for non-inductive / mutual / indexed domains.
        let target = peel_inductive_forall(env, goal)?;

        // Universe of the motive's codomain: `P x : Sort u`. The kernel rejects a
        // recursor whose levels mismatch the motive, so infer it rather than guess.
        let motive_level = motive_universe(env, base_ctx, &target.dom, &target.body)?;

        // motive := fun (x : I …) => P x  (same de Bruijn shape as the goal's Pi).
        let motive = Expr::lam(BinderInfo::Default, target.dom.clone(), target.body.clone());

        // Assemble `@I.rec.{levels} params motive minor₁ … minor_m`, discharging
        // each constructor's minor premise (the recursive fields' IHs are in scope
        // as locals). Type: `(t : I …) → motive t`, which is `∀ x, P x` up to beta.
        let assembled = self.assemble_by_recursor(
            env,
            &target,
            &motive,
            &motive_level,
            base_ctx,
            deadline,
            fuel - 1,
        )?;

        // ── soundness gate: kernel-check against the original goal ───────────────
        let tc = if base_ctx.is_empty() {
            TypeChecker::new(env)
        } else {
            TypeChecker::with_context(env, base_ctx.clone())
        };
        let inferred = tc.infer_type(&assembled).ok()?;
        if !tc.is_def_eq(&inferred, goal) {
            return None;
        }
        Some(assembled)
    }

    /// Discharge one induction subgoal in `ctx`, returning a proof term.
    ///
    /// Tries, in order: the existing SMT/superposition engines, the self-contained
    /// rewrite-aware equality prover ([`Self::prove_eq_rewrite`]), then (under
    /// remaining fuel) a nested induction. Every candidate is kernel-checked before
    /// it is returned, and again by the caller's `Nat.rec` assembly.
    pub(crate) fn discharge_subgoal(
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

        // 1. Existing engines first (honour "discharge via the existing prover").
        //    Every candidate is kernel-checked inside `run_base_engines`.
        if let Some(term) = self.run_base_engines(env, goal, ctx, deadline) {
            return Some(term);
        }

        // 2. Self-contained, rewrite-aware equality prover: reflexivity (closes
        //    `P 0` / `n + 0`), the specialised-IH rewrite, and congruence-from-IH
        //    (closes the `0 + n` successor step). The EUF engine cannot bridge the
        //    definitional unfold `0 + (k+1) ≡ (0+k)+1`, and its arithmetic fallback
        //    emits lemmas a minimal environment lacks; this path builds
        //    `Eq.refl`/`congrArg`/IH-application terms directly and re-checks them
        //    against `goal`.
        if let Some(term) = self.prove_eq_rewrite(env, ctx, goal, &[], deadline, REWRITE_DEPTH) {
            return Some(term);
        }

        // 3. Nested induction (bounded by fuel) for multi-variable goals.
        if fuel > 0 {
            return self.try_induction_lane(env, goal, ctx, deadline, fuel);
        }
        None
    }

    /// Run only the SMT and superposition engines (no induction recursion, no
    /// oracle) on `goal` in `ctx`, returning a *kernel-checked* proof term.
    ///
    /// Kept separate from `run_pipeline` so the induction lane can discharge a
    /// subgoal with the existing engines without re-entering induction (which
    /// would reset the fuel budget).
    ///
    /// Two robustness rules make this work against a minimal environment:
    ///   * only **Prop-typed** locals are fed to the engines as hypotheses — a
    ///     binder like `k : Nat` is not a fact and, if added, becomes a lossy EUF
    ///     atom that collapses the solver into `Unknown`;
    ///   * every candidate proof term is **kernel-checked** against `goal` in
    ///     `ctx` before being returned, so a term referring to a lemma the engine
    ///     assumed but the environment lacks (e.g. `Nat.le_antisymm`) is rejected
    ///     here, letting the caller fall through to the whnf/refl path.
    fn run_base_engines(
        &self,
        env: &Environment,
        goal: &Expr,
        ctx: &LocalContext,
        deadline: Instant,
    ) -> Option<Expr> {
        if Instant::now() >= deadline {
            return None;
        }
        let proof_ctx = if ctx.is_empty() {
            None
        } else {
            Some(ctx.clone())
        };
        let hypotheses = prop_hypotheses(env, ctx);

        let now = Instant::now();
        let smt = self.try_smt_detailed(
            env,
            goal,
            &hypotheses,
            None,
            proof_ctx.as_ref(),
            now,
            None,
            now,
        );
        if let AutomationOutcome::Verified(result) = smt {
            let term = result.proof_term().clone();
            if kernel_accepts(env, ctx, &term, goal) {
                return Some(term);
            }
        }

        if Instant::now() >= deadline {
            return None;
        }
        let superposition_hyps: Vec<(Expr, clean_kernel::FVarId)> =
            hypotheses.iter().map(|(h, f, _)| (h.clone(), *f)).collect();
        if let Some(result) = self.try_superposition_prove_with_fvars_until(
            env,
            goal,
            &superposition_hyps,
            Some(deadline),
        ) {
            let term = result.proof_term().clone();
            if kernel_accepts(env, ctx, &term, goal) {
                return Some(term);
            }
        }

        None
    }
}

/// Collect the Prop-typed locals of `ctx` as SMT/superposition hypotheses.
///
/// A local is a usable EUF/first-order fact only when its *type* is a
/// proposition (`… : Prop`). Term-level binders (`k : Nat`) are skipped so they
/// do not become lossy unconstrained atoms.
fn prop_hypotheses(env: &Environment, ctx: &LocalContext) -> Vec<HypothesisWithProofFVar> {
    if ctx.is_empty() {
        return Vec::new();
    }
    let tc = TypeChecker::with_context(env, ctx.clone());
    ctx.iter()
        .filter_map(|decl| {
            let type_of_type = tc.infer_type(&decl.type_).ok()?;
            if is_prop_sort(&tc, &type_of_type) {
                Some((decl.type_.clone(), decl.id, None))
            } else {
                None
            }
        })
        .collect()
}

/// `true` iff `ty` whnf-reduces to `Prop` (`Sort 0`).
fn is_prop_sort(tc: &TypeChecker<'_>, ty: &Expr) -> bool {
    matches!(tc.whnf(ty).strip_mdata().kind(), ExprKind::Sort(level) if level.normalize().is_zero())
}

/// Kernel-check `term : goal` in `ctx` (`infer_type` + `is_def_eq`).
pub(crate) fn kernel_accepts(
    env: &Environment,
    ctx: &LocalContext,
    term: &Expr,
    goal: &Expr,
) -> bool {
    let tc = if ctx.is_empty() {
        TypeChecker::new(env)
    } else {
        TypeChecker::with_context(env, ctx.clone())
    };
    match tc.infer_type(term) {
        Ok(inferred) => tc.is_def_eq(&inferred, goal),
        Err(_) => false,
    }
}

/// Infer the universe `u` such that `P n : Sort u` for the motive `fun n => P n`.
///
/// Opens `P` under a fresh `Nat` local and infers the type of `P probe`,
/// whnf-reducing to a `Sort`. Returns `None` if the body is not type-correct or
/// not a sort (so the lane bails rather than build a mis-leveled `Nat.rec`).
fn motive_universe(
    env: &Environment,
    base_ctx: &LocalContext,
    dom: &Expr,
    body: &Expr,
) -> Option<Level> {
    let mut ctx = base_ctx.clone();
    let probe = ctx.push(
        Name::from_string("ind.probe"),
        dom.clone(),
        BinderInfo::Default,
    );
    let body_at_probe = body.instantiate(&Expr::fvar(probe));
    let tc = TypeChecker::with_context(env, ctx);
    let ty = tc.infer_type(&body_at_probe).ok()?;
    let ty_whnf = tc.whnf(&ty);
    match ty_whnf.strip_mdata().kind() {
        ExprKind::Sort(level) => Some(level.normalize()),
        _ => None,
    }
}

/// A `TypeChecker` over `env`, with `ctx` installed when non-empty.
pub(crate) fn type_checker<'e>(env: &'e Environment, ctx: &LocalContext) -> TypeChecker<'e> {
    if ctx.is_empty() {
        TypeChecker::new(env)
    } else {
        TypeChecker::with_context(env, ctx.clone())
    }
}

/// Destructure `Eq.{u} T L R`, returning `(levels, T, L, R)`.
///
/// `levels` is the constant's universe vector (`[u]`); it is reused verbatim
/// when re-emitting `Eq.refl.{u}` so the level matches the goal exactly.
pub(crate) fn parse_eq(e: &Expr) -> Option<(LevelVec, Expr, Expr, Expr)> {
    let e = e.strip_mdata();
    let head = e.get_app_fn();
    let args = e.get_app_args();
    match head.kind() {
        ExprKind::Const(name, levels) if args.len() == 3 && *name == Name::from_string("Eq") => {
            Some((
                levels.clone(),
                args[0].clone(),
                args[1].clone(),
                args[2].clone(),
            ))
        }
        _ => None,
    }
}

/// `@Eq.refl.{u} ty a : Eq ty a a`.
pub(crate) fn eq_refl(levels: &LevelVec, ty: &Expr, a: &Expr) -> Expr {
    let refl = Expr::const_(Name::from_string("Eq.refl"), levels.clone());
    Expr::apps(refl, [ty.clone(), a.clone()])
}

/// `@Eq.{u} ty l r` (the proposition, not a proof).
pub(crate) fn build_eq(level: &Level, ty: &Expr, l: &Expr, r: &Expr) -> Expr {
    let eq = Expr::const_(Name::from_string("Eq"), vec![level.clone()]);
    Expr::apps(eq, [ty.clone(), l.clone(), r.clone()])
}

/// `@congrArg.{u_α, u_β} α β a₁ a₂ f h : Eq β (f a₁) (f a₂)`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn congr_arg(
    alpha_level: &Level,
    beta_level: &Level,
    alpha: &Expr,
    beta: &Expr,
    a1: &Expr,
    a2: &Expr,
    f: &Expr,
    h: &Expr,
) -> Expr {
    let congr = Expr::const_(
        Name::from_string("congrArg"),
        vec![alpha_level.clone(), beta_level.clone()],
    );
    Expr::apps(
        congr,
        [
            alpha.clone(),
            beta.clone(),
            a1.clone(),
            a2.clone(),
            f.clone(),
            h.clone(),
        ],
    )
}
