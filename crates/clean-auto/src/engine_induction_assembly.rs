// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generic single-recursor assembly for the structural-induction lane.
//!
//! [`crate::engine_induction`] owns the lane's orchestration (peel a `∀`,
//! discharge subgoals, kernel-check). This module is the *type-generic* core
//! that replaces the original `Nat`-only hard-coding: given any registered,
//! **non-mutual, index-free** inductive `I` (Nat, List, Bool, Option, Sum,
//! Prod, …), it
//!
//!   1. reads the inductive's metadata from the environment
//!      ([`peel_inductive_forall`]) — its parameters, recursor name, recursor
//!      universe arity, and per-constructor minor-premise binder counts — so
//!      adding another such inductive is *mechanical* (no new code);
//!   2. assembles `@I.rec.{levels} params motive minor₁ … minor_m`
//!      ([`AutomationEngine::assemble_by_recursor`]) by reading each minor
//!      premise's *exact* type straight off the recursor's own inferred type
//!      (so the field/IH structure is whatever the kernel says it is), opening
//!      its binders under fresh locals, and discharging the per-constructor
//!      conclusion with the lane's existing engines (the induction hypotheses
//!      are in scope as locals).
//!
//! The universe levels are read off the inductive head constant in the goal's
//! domain (`I.{ind_levels} args`) and prefixed with the motive's universe, in
//! the exact order the kernel mints recursor level params
//! (`[motive_u, ind_u…]`; see `inductive_recursor.rs`). A wrong instantiation
//! cannot be emitted as success: [`crate::engine_induction`]'s final
//! `infer_type` + `is_def_eq` gate rejects any assembled term the kernel does
//! not accept.

use clean_kernel::{
    BinderData, Environment, Expr, ExprKind, FVarId, Level, LocalContext, Name, TypeChecker,
};

use crate::engine::AutomationEngine;
use crate::engine_induction_aux::in_synthesis;

/// The peeled, environment-resolved target of one induction step.
///
/// Produced by [`peel_inductive_forall`] from a goal `∀ (x : I p₁ … p_k), P x`
/// where `I` is a registered non-mutual, index-free inductive. Carries exactly
/// what [`AutomationEngine::assemble_by_recursor`] needs to build the recursor
/// application — no hard-coded constructor knowledge.
pub(crate) struct InductionTarget {
    /// The inductive domain `I p₁ … p_k` (the peeled binder's type).
    pub(crate) dom: Expr,
    /// The `∀` body `P` with de Bruijn `BVar(0)` = the peeled binder.
    pub(crate) body: Expr,
    /// The recursor constant name (`I.rec`).
    pub(crate) rec_name: Name,
    /// Universe arguments of the inductive head constant in `dom`
    /// (`I.{ind_levels} args`).
    pub(crate) ind_levels: Vec<Level>,
    /// The inductive's parameter arguments `p₁ … p_k` (length = `num_params`).
    pub(crate) params: Vec<Expr>,
    /// Minor-premise binder count per constructor, in recursor-rule order:
    /// `num_fields + (#recursive fields)` (fields followed by their induction
    /// hypotheses). Used to peel exactly the right number of leading `Pi`s of
    /// each minor premise without over-peeling a higher-order conclusion.
    pub(crate) minor_binders: Vec<u32>,
    /// Recursive-field count per constructor, in recursor-rule order (parallel to
    /// [`Self::minor_binders`]). `0` marks a *non-recursive-eliminator* minor — a
    /// constructor with no recursive field, so the recursor hands it NO induction
    /// hypothesis (every `Int` constructor; `Nat.zero`; `List.nil`). This gates
    /// the field-induction fallback in [`AutomationEngine::discharge_minor`], which
    /// must fire only for such minors and never for an IH-carrying one.
    pub(crate) minor_recursive: Vec<u32>,
    /// The recursor's declared universe-parameter count.
    pub(crate) rec_num_levels: usize,
}

/// Peel a single leading `∀ (x : I args), B` whose domain head `I` is a
/// registered **non-mutual, index-free** inductive, returning the metadata the
/// recursor assembly needs.
///
/// Returns `None` (the lane declines) when the goal is not a `Pi`, the domain
/// head is not a registered inductive, the inductive has indices or is mutual
/// (more than one motive), the recursor is absent, or the applied-argument
/// count does not match the parameter count. This subsumes the old
/// `Nat`-specific peeler: `Nat` is the zero-parameter, zero-index, single-motive
/// case.
pub(crate) fn peel_inductive_forall(env: &Environment, goal: &Expr) -> Option<InductionTarget> {
    let ExprKind::Pi(_binder, dom_arc, body_arc) = goal.strip_mdata().kind() else {
        return None;
    };
    let dom = (**dom_arc).clone();
    let body = (**body_arc).clone();

    // Resolve the inductive head `I.{ind_levels}` and its applied arguments. The
    // borrows of `dom` are confined to this block so `dom` can be moved into the
    // returned target afterwards.
    let (ind_name, ind_levels, applied_args) = {
        let dom_stripped = dom.strip_mdata();
        let head = dom_stripped.get_app_fn();
        let ExprKind::Const(ind_name, ind_level_args) = head.kind() else {
            return None;
        };
        let args = dom_stripped.get_app_args();
        let applied_args: Vec<Expr> = args.iter().map(|&a| a.clone()).collect();
        (
            ind_name.clone(),
            ind_level_args.iter().cloned().collect::<Vec<Level>>(),
            applied_args,
        )
    };

    let info = env.inductive_info(&ind_name)?;
    // Index-free only: an indexed family (`Eq`, `Vector`, …) needs the motive to
    // generalise over its indices, which this lane does not build.
    if info.num_indices != 0 {
        return None;
    }
    let rec_name = info.recursor_name.clone()?;
    let rec_val = env.get_recursor(&rec_name)?;
    // Single-recursor (non-mutual): exactly one motive, no indices.
    if rec_val.num_motives != 1 || rec_val.num_indices != 0 {
        return None;
    }
    // One minor premise per constructor; the rules carry the field/IH structure.
    if rec_val.rules.len() != rec_val.num_minors as usize {
        return None;
    }

    if applied_args.len() != info.num_params as usize {
        return None;
    }
    let params: Vec<Expr> = applied_args;

    let minor_recursive: Vec<u32> = rec_val
        .rules
        .iter()
        .map(|rule| rule.recursive_fields.iter().filter(|&&b| b).count() as u32)
        .collect();
    let minor_binders: Vec<u32> = rec_val
        .rules
        .iter()
        .zip(minor_recursive.iter())
        .map(|(rule, &recursive)| rule.num_fields + recursive)
        .collect();

    let rec_num_levels = env.get_const(&rec_name)?.level_params.len();

    Some(InductionTarget {
        dom,
        body,
        rec_name,
        ind_levels,
        params,
        minor_binders,
        minor_recursive,
        rec_num_levels,
    })
}

/// The recursor's concrete universe arguments, in kernel-mint order.
///
/// The kernel mints a recursor's level params as `[motive_u, ind_u…]` for a
/// large-eliminating inductive, or `[ind_u…]` for a `Prop`-only inductive (no
/// motive universe). We mirror that exactly from the recursor's declared level
/// arity:
///   * `rec_num_levels == ind_levels + 1` → prepend `motive_level`;
///   * `rec_num_levels == ind_levels`     → `Prop`-only; require the motive be
///     `Prop` (`motive_level` normalises to `0`), else decline.
///
/// Returns `None` for any other arity (the lane declines rather than emit a
/// mis-leveled recursor — and even if it didn't, the caller's kernel re-check
/// would reject it).
fn recursor_levels(target: &InductionTarget, motive_level: &Level) -> Option<Vec<Level>> {
    let n_ind = target.ind_levels.len();
    if target.rec_num_levels == n_ind + 1 {
        let mut levels = Vec::with_capacity(target.rec_num_levels);
        levels.push(motive_level.clone());
        levels.extend(target.ind_levels.iter().cloned());
        Some(levels)
    } else if target.rec_num_levels == n_ind {
        if !motive_level.normalize().is_zero() {
            return None;
        }
        Some(target.ind_levels.clone())
    } else {
        None
    }
}

impl AutomationEngine {
    /// Assemble `@I.rec.{levels} params motive minor₁ … minor_m`, discharging
    /// each minor premise's conclusion with the lane's engines.
    ///
    /// `motive` is `fun (x : dom) => body`; `motive_level` is the universe of
    /// `body` (`P x : Sort motive_level`). The minor premise types are read
    /// straight off the *inferred* type of `@I.rec params motive`, so this code
    /// is agnostic to the constructor shapes — `target.minor_binders` only tells
    /// it how many leading binders each minor premise has (fields + IHs) so it
    /// peels to the conclusion without over-peeling a higher-order `P`.
    ///
    /// Returns the assembled term (still to be kernel-checked by the caller) or
    /// `None` if any minor premise cannot be discharged or the levels do not fit.
    pub(crate) fn assemble_by_recursor(
        &self,
        env: &Environment,
        target: &InductionTarget,
        motive: &Expr,
        motive_level: &Level,
        base_ctx: &LocalContext,
        deadline: std::time::Instant,
        fuel: u32,
    ) -> Option<Expr> {
        let rec_levels = recursor_levels(target, motive_level)?;
        let rec_head = Expr::const_(target.rec_name.clone(), rec_levels);

        // `@I.rec.{levels} p₁ … p_k motive` — the major premise and minor
        // premises are still to come.
        let mut applied = rec_head;
        for param in &target.params {
            applied = Expr::app(applied, param.clone());
        }
        applied = Expr::app(applied, motive.clone());

        let tc = type_checker(env, base_ctx);
        // Type of `@I.rec params motive`: `minor₁ → … → minor_m → (t:dom) → motive t`.
        let mut current_ty = tc.infer_type(&applied).ok()?;

        for (&n_binders, &n_recursive) in target
            .minor_binders
            .iter()
            .zip(target.minor_recursive.iter())
        {
            let pi = tc.whnf(&current_ty);
            let ExprKind::Pi(_, minor_dom_arc, minor_body_arc) = pi.strip_mdata().kind() else {
                return None;
            };
            let minor_dom = (**minor_dom_arc).clone();
            let minor_body = (**minor_body_arc).clone();

            let minor_proof = self.discharge_minor(
                env,
                &minor_dom,
                n_binders,
                n_recursive,
                base_ctx,
                deadline,
                fuel,
            )?;

            // Minor premises are non-dependent on one another, so instantiating
            // the (unused) binder advances the type to the next minor premise.
            current_ty = minor_body.instantiate(&minor_proof);
            applied = Expr::app(applied, minor_proof);
        }

        Some(applied)
    }

    /// Discharge one minor premise `minor_ty = (fields…)(IHs…) → motive (ctor …)`.
    ///
    /// Opens the leading `n_binders` `Pi`s under fresh locals layered on
    /// `base_ctx` (the recursive fields' induction hypotheses are among them),
    /// discharges the `motive (ctor …)` conclusion via
    /// [`Self::prove_goal_rewrite`] (the IH-rewriting step), then re-binds the
    /// locals as lambdas (innermost-first, mirroring the original `Nat` step).
    /// Returns a term of type `minor_ty`, or `None`.
    ///
    /// `n_recursive` is this constructor's recursive-field count. When
    /// `prove_goal_rewrite` cannot close the conclusion, a **non-recursive
    /// eliminator** minor (`n_recursive == 0`, so no IH — e.g. `Int.ofNat` /
    /// `Int.negSucc`, each carrying a bare `Nat` field) gets a fallback: the
    /// conclusion is generalised back over the opened field binders and the field
    /// is inducted on afresh (`Int.beq (ofNat n)(ofNat n) = true` reduces to
    /// `Nat.beq n n = true`, provable only by `Nat`-induction on `n`). The gate
    /// [`should_induct_on_field`] keeps this off the hot path — recursive minors
    /// (which close by IH above) and the aux-lemma synthesizer's speculative
    /// conjectures are excluded.
    ///
    /// Each opened binder domain *and* the conclusion are `whnf`-reduced. This is
    /// load-bearing for the recursive fields' induction hypotheses: a minor
    /// premise carries an IH binder of type `motive field` — a stuck redex
    /// `(fun x => P x) field` — which the self-contained equality prover's
    /// structural `parse_eq` cannot see through. Reducing it to the concrete
    /// `P field` (e.g. `Eq … (xs ++ []) xs`) is exactly what lets the
    /// congruence-from-IH step recognise the hypothesis. The reduced domain is
    /// definitionally equal to the original, so the rebuilt lambda still inhabits
    /// `minor_ty` (the caller's kernel re-check confirms it).
    fn discharge_minor(
        &self,
        env: &Environment,
        minor_ty: &Expr,
        n_binders: u32,
        n_recursive: u32,
        base_ctx: &LocalContext,
        deadline: std::time::Instant,
        fuel: u32,
    ) -> Option<Expr> {
        let mut ctx = base_ctx.clone();
        let mut binders: Vec<(FVarId, BinderData, Expr)> = Vec::new();
        let mut current = minor_ty.clone();
        for _ in 0..n_binders {
            let ExprKind::Pi(bd, dom_arc, body_arc) = current.strip_mdata().kind() else {
                return None;
            };
            let bd = *bd;
            let dom = (**dom_arc).clone();
            // whnf reduces a `motive field` IH binder to the concrete `P field`
            // (over the locals already in scope), so the equality prover sees a
            // structural `Eq …`. Field binders (`Nat`, `List α`, …) are neutral.
            let dom = type_checker(env, &ctx).whnf(&dom);
            let fvar = ctx.push(Name::from_string("ind.f"), dom.clone(), bd);
            current = body_arc.instantiate(&Expr::fvar(fvar));
            binders.push((fvar, bd, dom));
        }

        // `current` is `motive (ctor …)`, a stuck redex; whnf beta-reduces it to
        // the concrete subgoal `P (ctor …)`. When `P` is a `∀ ys, l = r` motive,
        // the IH-rewriting step ([`AutomationEngine::prove_goal_rewrite`])
        // introduces the inner `ys`, specialises the in-scope induction
        // hypotheses at them, and closes the residual equation by rewriting with
        // those specialised IHs — the step `add_assoc` / `append_assoc` need.
        let conclusion = type_checker(env, &ctx).whnf(&current);
        let mut term = match self.prove_goal_rewrite(env, &conclusion, &ctx, deadline, fuel) {
            Some(t) => t,
            // Non-recursive-eliminator fallback. A minor of a *non-recursive*
            // constructor (`Int.ofNat`, `Int.negSucc` — each carries a `Nat`
            // field but no recursive field, so `Int.rec` hands out NO induction
            // hypothesis) can leave a conclusion that is itself provable only by
            // its own induction on that field: `Int.beq (ofNat n)(ofNat n) = true`
            // reduces to `Nat.beq n n = true`, which needs `Nat`-induction on `n`.
            // The IH-rewrite prover (`prove_goal_rewrite`) has no IH to rewrite
            // with and returns `None`; here we generalise the conclusion back over
            // the opened field binders and induct on the field afresh.
            //
            // This is gated OFF the hot path (see `should_induct_on_field`): it
            // fires ONLY when this minor has NO recursive field (no IH — so a
            // recursive-eliminator minor like `Nat.succ`, which already closes by
            // IH above, is untouched) AND at least one opened field is a
            // registered index-free inductive (so there is something to induct
            // on). Crucially this excludes the aux-lemma synthesizer's false
            // bridging conjectures (`Nat.beq (succ x) y = succ (Nat.beq x y)`),
            // whose stuck minors are either field-less zero-minors or
            // IH-carrying succ-minors — firing on those re-triggered synthesis and
            // exploded N1's budget.
            None if fuel > 0 && should_induct_on_field(env, n_recursive, &binders) => {
                let mut generalized = conclusion.clone();
                for (fvar, bd, dom) in binders.iter().rev() {
                    generalized = Expr::pi(*bd, dom.clone(), generalized.abstract_fvar(*fvar));
                }
                let proof = self.try_induction_lane(env, &generalized, base_ctx, deadline, fuel)?;
                // Re-apply the proof `∀ fields, conclusion` to the opened fields,
                // in binder order, recovering a term of type `conclusion`.
                let mut applied = proof;
                for (fvar, _bd, _dom) in &binders {
                    applied = Expr::app(applied, Expr::fvar(*fvar));
                }
                applied
            }
            None => return None,
        };

        // Re-bind the opened locals innermost-first so `abstract_fvar`'s index
        // shifting lines up (mirrors the original `Nat` step abstraction).
        for (fvar, bd, dom) in binders.into_iter().rev() {
            let abstracted = term.abstract_fvar(fvar);
            term = Expr::lam(bd, dom, abstracted);
        }
        Some(term)
    }
}

/// A `TypeChecker` over `env`, with `ctx` installed when non-empty.
fn type_checker<'e>(env: &'e Environment, ctx: &LocalContext) -> TypeChecker<'e> {
    if ctx.is_empty() {
        TypeChecker::new(env)
    } else {
        TypeChecker::with_context(env, ctx.clone())
    }
}

/// `true` iff this constructor's minor should get the field-induction fallback
/// (see [`AutomationEngine::discharge_minor`]).
///
/// Fires only when ALL of:
///   * we are NOT inside aux-lemma synthesis ([`in_synthesis`]) — the synthesizer
///     proves speculative bridging conjectures via this same lane, and firing on
///     their stuck minors re-enters the synthesizer and explodes the search (the
///     non-local blow-up that regressed the `Nat`/`Int` rows through both the
///     direct-conjecture and the reordered-`Int`-induction routes);
///   * this is a **non-recursive-eliminator minor** — `n_recursive == 0`, so the
///     recursor introduced no induction hypothesis (a recursive minor like
///     `Nat.succ` already closes by its IH in `prove_goal_rewrite` and must stay
///     on that path); and
///   * at least one opened field's domain is a registered index-free inductive
///     (so there is a variable to induct on — declines field-less minors like
///     `Nat.zero`).
fn should_induct_on_field(
    env: &Environment,
    n_recursive: u32,
    binders: &[(FVarId, BinderData, Expr)],
) -> bool {
    n_recursive == 0
        && !in_synthesis()
        && binders
            .iter()
            .any(|(_, _, dom)| is_index_free_inductive(env, dom))
}

/// `true` iff `dom`'s head constant is a registered index-free inductive type.
fn is_index_free_inductive(env: &Environment, dom: &Expr) -> bool {
    let ExprKind::Const(name, _) = dom.strip_mdata().get_app_fn().kind() else {
        return false;
    };
    env.inductive_info(name)
        .is_some_and(|info| info.num_indices == 0)
}
