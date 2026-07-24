// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Miller-pattern higher-order unification.
//!
//! Implements the decidable, most-general fragment of higher-order
//! unification (Miller, *A Logic Programming Language with Lambda-Abstraction,
//! Function Variables, and Simple Unification*, 1991).
//!
//! A constraint `?m x₁ … xₙ =?= t` is a **pattern** when `x₁ … xₙ` are
//! *distinct* bound/local variables (here: distinct local `FVar`s that are not
//! themselves metavariables). For a pattern there is a unique most-general
//! solution
//!
//! ```text
//! ?m := λ x₁ … xₙ. t
//! ```
//!
//! provided three side conditions hold:
//!
//! 1. **Occurs check** — `?m` does not occur in `t` (after instantiation),
//!    otherwise the assignment would be circular.
//! 2. **Scope check** — every free `FVar` of `t` is either one of the pattern
//!    arguments `x₁ … xₙ` or already in `?m`'s recorded local scope. A variable
//!    outside both would *escape* its binder, so we must not abstract it away.
//! 3. **Distinctness** — the arguments are pairwise distinct genuine locals.
//!
//! When any condition fails we **defer**: we return `None` so the unifier's
//! normal structural dispatch runs exactly as before, rather than guess a
//! non-unique solution. Deferring can never make a sound program unsound; it
//! only forgoes solving a constraint the Miller fragment cannot uniquely
//! resolve, and the Miller fragment is therefore purely *additive*.
//!
//! # Soundness
//!
//! A metavariable assignment is provisional: the fully-elaborated term is still
//! kernel-checked, so an incorrect assignment is caught as a type error and
//! cannot cause unsoundness. To avoid *incompleteness* regressions we only
//! assign genuine Miller patterns; everything else defers exactly as before.

use clean_kernel::{BinderData, Expr, ExprKind, ExprVisitor, FVarId};
use std::collections::HashSet;

use super::super::meta_id::MetaId;
use super::super::meta_state::MetaState;
use super::{Unifier, UnifyResult};

/// A pattern argument: a genuine local `FVar` together with its inferred binder
/// type. Used to build fresh metavariables and their lambda abstractions for the
/// flex-flex intersection rule.
struct PatternArg {
    fvar: FVarId,
    ty: Expr,
}

/// A flex application `?m a₁ … aₙ`: an application whose head, after
/// instantiation, is an unassigned metavariable.
struct FlexApp {
    meta: MetaId,
    /// Arguments in source order (`a₁ … aₙ`).
    args: Vec<Expr>,
}

impl<'a> Unifier<'a> {
    /// Decompose `expr` into a flex application if its head is an unassigned
    /// metavariable applied to one or more arguments.
    ///
    /// Returns `None` for a bare metavariable (handled by `unify_meta`), for a
    /// metavariable that is already assigned, or for any non-flex head.
    fn as_flex_app(&self, expr: &Expr) -> Option<FlexApp> {
        if !expr.is_app() {
            return None;
        }
        let head = expr.get_app_fn();
        let meta = self.as_meta(head)?;
        // An assigned meta is not flex — instantiation/WHNF will resolve it,
        // so let the normal dispatch reduce it instead of treating it as flex.
        if self.metas.is_assigned(meta) {
            return None;
        }
        // Source-order argument list.
        let mut args: Vec<Expr> = expr.get_app_args_iter().cloned().collect();
        args.reverse();
        Some(FlexApp { meta, args })
    }

    /// Whether `expr` is a flex application `?m a₁ … aₙ` (head is an unassigned
    /// metavariable applied to ≥1 argument). Convenience predicate over
    /// [`Self::as_flex_app`] for callers that only need the boolean.
    pub(super) fn is_flex_app(&self, expr: &Expr) -> bool {
        self.as_flex_app(expr).is_some()
    }

    /// Attempt Miller-pattern unification for a constraint where at least one
    /// side is a flex application `?m a₁ … aₙ`.
    ///
    /// Returns:
    /// - `Some(Success)` — a unique pattern solution was assigned.
    /// - `Some(Failure)` — occurs check failed (genuinely unsolvable).
    /// - `None` — not a (solvable) Miller pattern, or neither side is a flex
    ///   application. The caller falls back to its normal structural dispatch,
    ///   so the Miller fragment is purely additive and cannot regress
    ///   constraints the structural path already handled.
    pub(super) fn try_pattern_unify(&mut self, left: &Expr, right: &Expr) -> Option<UnifyResult> {
        let left_flex = self.as_flex_app(left);
        let right_flex = self.as_flex_app(right);

        match (left_flex, right_flex) {
            // Flex-rigid (or flex-flex where only one side parses as a flex
            // application): try to solve the flex side as a pattern against the
            // other side.
            (Some(flex), None) => self.solve_pattern_or_defer(flex, right),
            (None, Some(flex)) => self.solve_pattern_or_defer(flex, left),
            // Flex-flex: both heads are metavariables.
            (Some(left_flex), Some(right_flex)) => {
                self.solve_flex_flex(left_flex, left, right_flex, right)
            }
            (None, None) => None,
        }
    }

    /// Solve `?m a₁ … aₙ =?= rhs` if it is a Miller pattern; otherwise defer.
    ///
    /// Returns:
    /// - `Some(Success)` — a unique pattern solution was assigned.
    /// - `Some(Failure)` — the occurs check failed (genuinely circular).
    /// - `None` — not a Miller pattern; the caller falls back to its normal
    ///   structural dispatch (which may decompose the application spine). This
    ///   intentionally preserves pre-existing first-order behavior so that the
    ///   Miller fragment is *additive* and never causes incompleteness
    ///   regressions on constraints the structural path already handled.
    fn solve_pattern_or_defer(&mut self, flex: FlexApp, rhs: &Expr) -> Option<UnifyResult> {
        match self.try_solve_pattern(&flex, rhs) {
            PatternOutcome::Solved => Some(UnifyResult::Success),
            PatternOutcome::OccursCheck => Some(UnifyResult::Failure(format!(
                "occurs check failed for {:?}",
                flex.meta
            ))),
            // Not a pattern (repeated args, non-local args, out-of-scope free
            // var in rhs, …). Defer to the structural dispatch.
            PatternOutcome::NotPattern => None,
        }
    }

    /// Flex-flex: `?m xs =?= ?n ys`.
    ///
    /// - Same metavariable head: decompose argument-wise (rigid congruence),
    ///   preserving the prior structural behavior for `?m a =?= ?m b`.
    /// - Distinct heads: try to solve one side as a pattern (assigning the
    ///   other application as its body). If that direct solve does not apply but
    ///   *both* sides are Miller patterns, apply the **intersection rule**: a
    ///   fresh metavariable `?h` ranges over the variables common to both
    ///   argument lists, and we assign `?m := λ xs. ?h (common)` and
    ///   `?n := λ ys. ?h (common)`. Otherwise defer to the structural dispatch
    ///   (`None`).
    ///
    /// PIN (flex-flex intersection): the intersection rule fires only when both
    /// sides are genuine Miller patterns (distinct local arguments). When either
    /// side is *not* a pattern (repeated/non-local arguments) we still defer —
    /// there is no unique most-general solution to commit to, so guessing would
    /// risk an incompleteness regression. Both-non-pattern flex-flex therefore
    /// remains deferred exactly as before.
    fn solve_flex_flex(
        &mut self,
        left_flex: FlexApp,
        left: &Expr,
        right_flex: FlexApp,
        right: &Expr,
    ) -> Option<UnifyResult> {
        // Same metavariable head: decompose argument-wise (rigid congruence).
        // This preserves the pre-existing structural behavior for `?m a =?= ?m b`
        // (unify `a =?= b`), rather than attempting an occurs-failing pattern
        // assignment. Arity mismatch on the same head is unsolvable.
        if left_flex.meta == right_flex.meta {
            if left_flex.args.len() != right_flex.args.len() {
                return Some(UnifyResult::Failure(format!(
                    "flex-flex arity mismatch for {:?}",
                    left_flex.meta
                )));
            }
            for (a, b) in left_flex.args.iter().zip(right_flex.args.iter()) {
                match self.unify_core(a, b) {
                    UnifyResult::Success => {}
                    other => return Some(other),
                }
            }
            return Some(UnifyResult::Success);
        }

        // Try the left side as a pattern with the right application as body.
        // `?m xs := λ xs. (?n ys)` is sound when xs is a pattern, ?m ∉ rhs and
        // the scope check passes (?n is a meta, exempt; ys must be in scope).
        if let PatternOutcome::Solved = self.try_solve_pattern(&left_flex, right) {
            return Some(UnifyResult::Success);
        }
        // Symmetric: try the right side as a pattern.
        if let PatternOutcome::Solved = self.try_solve_pattern(&right_flex, left) {
            return Some(UnifyResult::Success);
        }

        // Intersection rule (distinct heads, both sides genuine patterns):
        //   ?m x₁ … xⱼ =?= ?n y₁ … yₖ
        // has the unique-up-to-renaming most-general solution
        //   ?m := λ x₁ … xⱼ. ?h c₁ … cₘ
        //   ?n := λ y₁ … yₖ. ?h c₁ … cₘ
        // where c₁ … cₘ are the variables common to both argument lists and ?h
        // is a fresh metavariable scoped over exactly those common variables.
        // After beta-reduction both `?m x⃗` and `?n y⃗` reduce to `?h c⃗`, so the
        // constraint holds for every instantiation of ?h.
        if let Some(result) = self.try_flex_flex_intersection(&left_flex, &right_flex) {
            return Some(result);
        }

        // Neither side is a solvable pattern: defer to structural dispatch.
        None
    }

    /// Apply the Miller flex-flex *intersection* rule for two distinct
    /// metavariable applications that are **both** patterns.
    ///
    /// Returns `Some(Success)` if the rule fired (both metavariables assigned),
    /// or `None` if either side is not a pattern (the caller then defers).
    ///
    /// # Soundness
    ///
    /// The fresh metavariable `?h` is scoped over exactly the common arguments,
    /// so the bodies `?h c₁ … cₘ` reference only those locals (plus `?h`, which
    /// is meta-exempt). Each assignment is therefore a genuine Miller pattern
    /// solve (occurs- and scope-checked) reusing [`Self::try_solve_pattern`].
    /// The assignments are provisional and re-checked by the kernel downstream,
    /// so an imprecise `?h` type can only cause a spurious type error, never
    /// unsoundness. Deferring when either side is not a pattern preserves the
    /// prior conservative behavior (no incompleteness regression).
    fn try_flex_flex_intersection(
        &mut self,
        left_flex: &FlexApp,
        right_flex: &FlexApp,
    ) -> Option<UnifyResult> {
        // Both argument lists must be genuine patterns (distinct local vars).
        let left_args = self.pattern_args(left_flex)?;
        let right_args = self.pattern_args(right_flex)?;

        // Common variables: those appearing in BOTH argument lists. We preserve
        // the left side's order so the two bodies share an identical argument
        // sequence (the choice of order is irrelevant as long as it is the same
        // on both sides; reduction makes both reduce to the same `?h c⃗`).
        let right_set: HashSet<FVarId> = right_args.iter().map(|a| a.fvar).collect();
        let common: Vec<PatternArg> = left_args
            .iter()
            .filter(|a| right_set.contains(&a.fvar))
            .map(|a| PatternArg {
                fvar: a.fvar,
                ty: a.ty.clone(),
            })
            .collect();

        // Helper creation and both outer assignments are one atomic
        // intersection step. If either side stops being a pattern, roll back
        // the fresh metas and the first assignment instead of leaking a
        // half-solved flex-flex constraint into structural fallback.
        self.metas.push_scope();

        // Build a fresh `?h : Π (common tys). ?r` scoped over the common vars,
        // where `?r` is a fresh result-type metavariable. `?r` has the same
        // explicit common-variable scope: marking it as legacy/untracked would
        // inherit every ambient local (including x/z, which are not shared) and
        // make either side's contextual scope check correctly reject `?h`.
        let h_locals: Vec<(String, FVarId, Expr)> = common
            .iter()
            .map(|a| (format!("c{}", a.fvar.as_u64()), a.fvar, a.ty.clone()))
            .collect();
        let result_ty = self
            .metas
            .fresh_with_locals(Expr::type_(), h_locals.clone());
        let mut h_ty = meta_fvar_expr(result_ty);
        for arg in common.iter().rev() {
            h_ty = Expr::pi(BinderData::default(), arg.ty.clone(), h_ty);
        }
        let h = self.metas.fresh_with_locals(h_ty, h_locals);

        // The shared body `?h c₁ … cₘ`, with the common vars as free locals so
        // that `try_solve_pattern` can abstract them on each side.
        let h_body = Expr::apps(meta_fvar_expr(h), common.iter().map(|a| Expr::fvar(a.fvar)));

        // Assign ?m := λ xs. (?h c⃗) and ?n := λ ys. (?h c⃗) via the ordinary
        // pattern machinery. Both bodies reference only the common vars (pattern
        // args of each side) and the meta ?h, so occurs/scope checks pass.
        match self.try_solve_pattern(left_flex, &h_body) {
            PatternOutcome::Solved => {}
            _ => {
                self.metas.pop_scope();
                return None;
            }
        }
        match self.try_solve_pattern(right_flex, &h_body) {
            PatternOutcome::Solved => {
                self.metas.commit();
                Some(UnifyResult::Success)
            }
            _ => {
                self.metas.pop_scope();
                None
            }
        }
    }

    /// Extract the pattern arguments of `flex` (distinct genuine locals with
    /// their inferred binder types), or `None` if `flex` is not a pattern.
    ///
    /// Mirrors the distinctness/locality checks in [`Self::try_solve_pattern`]
    /// so the two share one definition of "pattern".
    fn pattern_args(&self, flex: &FlexApp) -> Option<Vec<PatternArg>> {
        let mut args: Vec<PatternArg> = Vec::with_capacity(flex.args.len());
        let mut seen: HashSet<FVarId> = HashSet::with_capacity(flex.args.len());
        for arg in &flex.args {
            let arg = self.metas.instantiate(arg);
            match arg.kind() {
                ExprKind::FVar(id) => {
                    if MetaState::from_fvar(*id).is_some() {
                        return None;
                    }
                    if !seen.insert(*id) {
                        return None;
                    }
                    args.push(PatternArg {
                        fvar: *id,
                        ty: self.fvar_binder_type(*id),
                    });
                }
                _ => return None,
            }
        }
        Some(args)
    }

    fn contextually_lift_meta(
        &mut self,
        meta_id: MetaId,
        outer_meta: MetaId,
        outer_allowed: &HashSet<FVarId>,
        arg_fvars: &[FVarId],
        arg_set: &HashSet<FVarId>,
        visiting: &mut HashSet<MetaId>,
        done: &mut HashSet<MetaId>,
        lifted_any: &mut bool,
    ) -> Result<(), ()> {
        if meta_id == outer_meta || done.contains(&meta_id) {
            return Ok(());
        }
        let Some(meta) = self.metas.get(meta_id).cloned() else {
            return Ok(());
        };
        if meta.assignment.is_some() {
            done.insert(meta_id);
            return Ok(());
        }
        if !visiting.insert(meta_id) {
            return Err(());
        }

        // Restrict dependencies in both the result type and every captured
        // local type before constructing this meta's helper telescope. This is
        // a depth-first traversal: a type meta such as `?β` becomes `?β' k`
        // before a value meta of type `?β` is itself lifted.
        let meta_ty = self.metas.instantiate(&meta.ty);
        let mut dependencies = collect_unassigned_metas(&meta_ty, self.metas);
        for (_, _, ty) in &meta.locals {
            dependencies.extend(collect_unassigned_metas(
                &self.metas.instantiate(ty),
                self.metas,
            ));
        }
        dependencies.sort_unstable();
        dependencies.dedup();
        for dependency in dependencies {
            if dependency == meta_id || dependency == outer_meta {
                visiting.remove(&meta_id);
                return Err(());
            }
            self.contextually_lift_meta(
                dependency,
                outer_meta,
                outer_allowed,
                arg_fvars,
                arg_set,
                visiting,
                done,
                lifted_any,
            )?;
        }

        let meta = self.metas.get(meta_id).cloned().ok_or(())?;
        if meta
            .locals
            .iter()
            .any(|(_, fvar, _)| !outer_allowed.contains(fvar) && !arg_set.contains(fvar))
        {
            visiting.remove(&meta_id);
            return Err(());
        }

        // Preserve the pattern's source order. This is load-bearing for
        // dependent telescopes and the application `?h x₁ ... xₙ`.
        let extras: Vec<(String, FVarId, Expr)> = arg_fvars
            .iter()
            .filter_map(|wanted| {
                meta.locals
                    .iter()
                    .find(|(_, fvar, _)| fvar == wanted)
                    .cloned()
            })
            .filter(|(_, fvar, _)| !outer_allowed.contains(fvar))
            .collect();

        let helper_locals: Vec<_> = meta
            .locals
            .iter()
            .filter(|(_, fvar, _)| outer_allowed.contains(fvar))
            .map(|(name, fvar, ty)| (name.clone(), *fvar, self.metas.instantiate(ty)))
            .collect();
        for (_, _, ty) in &helper_locals {
            if find_escaping_fvar(ty, outer_allowed).is_some()
                || find_scope_widening_meta(ty, outer_allowed, self.metas).is_some()
            {
                visiting.remove(&meta_id);
                return Err(());
            }
        }

        if extras.is_empty() {
            // Even a scope-compatible meta can have a malformed wider type;
            // validate after recursively restricting all of its dependencies.
            let ty = self.metas.instantiate(&meta.ty);
            if find_escaping_fvar(&ty, outer_allowed).is_some()
                || find_scope_widening_meta(&ty, outer_allowed, self.metas).is_some()
            {
                visiting.remove(&meta_id);
                return Err(());
            }
            visiting.remove(&meta_id);
            done.insert(meta_id);
            return Ok(());
        }

        let mut helper_ty = self.metas.instantiate(&meta.ty);
        // Build the dependent Pi telescope from inside out. Abstracting the
        // accumulated body at each step closes occurrences in later binder
        // types over earlier arguments too.
        for (_, fvar, ty) in extras.iter().rev() {
            helper_ty = helper_ty.abstract_fvar(*fvar);
            helper_ty = Expr::pi(BinderData::default(), self.metas.instantiate(ty), helper_ty);
        }
        if find_escaping_fvar(&helper_ty, outer_allowed).is_some()
            || find_scope_widening_meta(&helper_ty, outer_allowed, self.metas).is_some()
        {
            visiting.remove(&meta_id);
            return Err(());
        }

        let helper = self.metas.fresh_with_locals(helper_ty, helper_locals);
        let lifted = Expr::apps(
            meta_fvar_expr(helper),
            extras.iter().map(|(_, fvar, _)| Expr::fvar(*fvar)),
        );
        if !self.metas.assign(meta_id, lifted) {
            visiting.remove(&meta_id);
            return Err(());
        }
        *lifted_any = true;
        visiting.remove(&meta_id);
        done.insert(meta_id);
        Ok(())
    }

    /// Restrict unsolved metavariables embedded in a prospective pattern
    /// solution to the outer metavariable's scope.
    ///
    /// Suppose we are solving `?f k =?= ?m`, where `?f` was created outside
    /// `k` but `?m` was created inside it. Assigning `?f := fun _ => ?m` is not
    /// stable: if `?m` is later assigned `k`, instantiation reveals a free `k`
    /// under an already-built lambda. We instead introduce a restricted helper
    /// `?h` and assign `?m := ?h k`; outer abstraction then binds the explicit
    /// `k`, and later solving `?m` becomes the Miller constraint `?h k =?= ...`.
    ///
    /// Returns the re-instantiated RHS and whether a rollback scope was opened.
    /// Every caller exit after `opened_scope == true` must commit or pop it.
    fn contextually_lift_rhs_metas(
        &mut self,
        flex: &FlexApp,
        arg_fvars: &[FVarId],
        rhs: &Expr,
    ) -> Result<(Expr, bool), ()> {
        let Some(outer_allowed) = self.allowed_locals_for_meta(flex.meta) else {
            return Ok((rhs.clone(), false));
        };
        let arg_set: HashSet<FVarId> = arg_fvars.iter().copied().collect();
        let mut nested = collect_unassigned_metas(rhs, self.metas);
        nested.retain(|meta_id| *meta_id != flex.meta);
        nested.sort_unstable();
        nested.dedup();
        if nested.is_empty() {
            return Ok((rhs.clone(), false));
        }

        self.metas.push_scope();
        let mut visiting = HashSet::new();
        let mut done = HashSet::new();
        let mut lifted_any = false;
        for meta_id in nested {
            if self
                .contextually_lift_meta(
                    meta_id,
                    flex.meta,
                    &outer_allowed,
                    arg_fvars,
                    &arg_set,
                    &mut visiting,
                    &mut done,
                    &mut lifted_any,
                )
                .is_err()
            {
                self.metas.pop_scope();
                return Err(());
            }
        }
        if !lifted_any {
            self.metas.pop_scope();
            return Ok((rhs.clone(), false));
        }
        Ok((self.metas.instantiate(rhs), true))
    }

    /// Core Miller-pattern attempt: check the side conditions and, if they all
    /// hold, assign `?m := λ x₁ … xₙ. rhs`.
    fn try_solve_pattern(&mut self, flex: &FlexApp, rhs: &Expr) -> PatternOutcome {
        // (3) Distinct genuine locals. Each argument must be an `FVar` that is
        // NOT itself a metavariable, and all argument FVars must be distinct.
        let mut arg_fvars: Vec<FVarId> = Vec::with_capacity(flex.args.len());
        let mut seen: HashSet<FVarId> = HashSet::with_capacity(flex.args.len());
        for arg in &flex.args {
            // Instantiate in case the argument is an assigned meta or contains
            // one; a pattern argument must reduce to a bare local FVar.
            let arg = self.metas.instantiate(arg);
            match arg.kind() {
                ExprKind::FVar(id) => {
                    if MetaState::from_fvar(*id).is_some() {
                        // A metavariable argument is not a local variable.
                        return PatternOutcome::NotPattern;
                    }
                    if !seen.insert(*id) {
                        // Repeated argument ⇒ not a pattern.
                        return PatternOutcome::NotPattern;
                    }
                    arg_fvars.push(*id);
                }
                _ => return PatternOutcome::NotPattern,
            }
        }

        // Instantiate the right-hand side so the occurs/scope checks see the
        // current solution.
        let mut rhs = self.metas.instantiate(rhs);

        // (1) Occurs check: ?m must not appear in rhs.
        if MetaState::occurs_in(&rhs, flex.meta) {
            return PatternOutcome::OccursCheck;
        }

        // (2) Scope check: every free FVar of rhs must be a pattern argument or
        // already in ?m's recorded local scope. Meta-FVars are exempt (they are
        // not locals). A free local outside this set would escape its binder.
        let mut allowed: HashSet<FVarId> = arg_fvars.iter().copied().collect();
        if let Some(meta_allowed) = self.allowed_locals_for_meta(flex.meta) {
            allowed.extend(meta_allowed);
        }
        if find_escaping_fvar(&rhs, &allowed).is_some() {
            return PatternOutcome::NotPattern;
        }

        let opened_lift_scope = match self.contextually_lift_rhs_metas(flex, &arg_fvars, &rhs) {
            Ok((lifted_rhs, opened_scope)) => {
                rhs = lifted_rhs;
                opened_scope
            }
            Err(()) => return PatternOutcome::NotPattern,
        };

        // Lifting introduces only fresh helper metas and applications to the
        // existing pattern arguments, but re-check the ordinary occurs
        // condition before constructing the committed solution.
        if MetaState::occurs_in(&rhs, flex.meta) {
            if opened_lift_scope {
                self.metas.pop_scope();
            }
            return PatternOutcome::OccursCheck;
        }

        // All conditions hold: build `λ x₁ … xₙ. rhs`.
        //
        // `abstract_fvar` replaces its target with `BVar(0)` and shifts every
        // other `BVar` up by one. Abstracting the arguments in *source* order
        // (x₁, then x₂, …) therefore leaves xᵢ at de Bruijn index `n - 1 - i`:
        // x₁ at the deepest index `n-1` and xₙ at `0`. That matches binders
        // wrapped with x₁ outermost (`λ x₁ … λ xₙ. body`). Capture each binder
        // type *before* abstraction, while the FVar's type is still resolvable.
        let binder_tys: Vec<Expr> = arg_fvars
            .iter()
            .map(|fv| self.fvar_binder_type(*fv))
            .collect();
        let mut body = rhs;
        for fv in &arg_fvars {
            body = body.abstract_fvar(*fv);
        }
        // Wrap binders from innermost (last arg) to outermost (first arg), so
        // the outermost lambda binds x₁.
        for ty in binder_tys.into_iter().rev() {
            body = Expr::lam(BinderData::default(), ty, body);
        }

        // After abstracting every pattern argument, the solution may mention
        // only locals captured by the metavariable at creation time. This is a
        // defensive postcondition on Expr::abstract_fvar as well as the Miller
        // construction itself; never commit a temporary binder FVar even if a
        // malformed expression metadata bit caused abstraction to skip it.
        let post_allowed = self.allowed_locals_for_meta(flex.meta).unwrap_or_default();
        if find_escaping_fvar(&body, &post_allowed).is_some() {
            if opened_lift_scope {
                self.metas.pop_scope();
            }
            return PatternOutcome::NotPattern;
        }
        if find_scope_widening_meta(&body, &post_allowed, self.metas).is_some() {
            if opened_lift_scope {
                self.metas.pop_scope();
            }
            return PatternOutcome::NotPattern;
        }

        // Capture the metavariable's declared type *before* assignment so we can
        // propagate any universe-level constraints carried solely by the type
        // (e.g. `?m : Type u → Type v`). Direct Miller-pattern assignment bypasses
        // the level-propagation in `unify_meta`, which otherwise leaks those
        // params into the kernel term (monad universe-normalization bug).
        let meta_ty = self.metas.get(flex.meta).map(|m| m.ty.clone());

        if self.metas.assign(flex.meta, body.clone()) {
            if let Some(meta_ty) = meta_ty {
                self.propagate_meta_type_levels(&meta_ty, &body);
            }
            if opened_lift_scope {
                self.metas.commit();
            }
            PatternOutcome::Solved
        } else {
            if opened_lift_scope {
                self.metas.pop_scope();
            }
            // `assign` only fails if already assigned (handled earlier) or its
            // internal occurs check rejects the value. Treat as occurs failure.
            PatternOutcome::OccursCheck
        }
    }

    /// Best-effort type for a pattern-argument binder.
    ///
    /// The binder type only affects elaboration ergonomics; the kernel
    /// re-checks the final assignment, where the actual local types are known.
    /// We infer the local's type from the type checker when available and fall
    /// back to a placeholder sort otherwise.
    ///
    /// PIN (dependent binder types): the inferred type is used verbatim, so a
    /// genuinely *dependent* local context — where an earlier pattern argument
    /// occurs in the type of a later one — is not abstracted across binders.
    /// Such a lambda would be rejected by the kernel during final checking
    /// (a spurious failure, never an unsound acceptance). This dependent case
    /// is rare in real Lean elaboration and is intentionally left for follow-up.
    fn fvar_binder_type(&self, id: FVarId) -> Expr {
        let tc_cache = self.tc_cache.borrow();
        if let Some(tc) = tc_cache.as_ref() {
            if let Ok(ty) = tc.infer_type(&Expr::fvar(id)) {
                return ty;
            }
        }
        // No environment or unknown local: use a placeholder sort. The kernel
        // will reconstruct the precise type during final checking.
        Expr::type_()
    }
}

/// Outcome of a single Miller-pattern attempt.
enum PatternOutcome {
    /// A unique pattern solution was assigned.
    Solved,
    /// The metavariable occurs in the right-hand side (circular).
    OccursCheck,
    /// Not a Miller pattern; caller must defer.
    NotPattern,
}

/// Build the expression form of a metavariable `?m` (an `FVar` carrying the
/// meta tag), used to construct the body of an intersection-rule assignment.
fn meta_fvar_expr(meta: MetaId) -> Expr {
    Expr::fvar(MetaState::to_fvar(meta))
}

/// Find a free `FVar` in `expr` that is NOT in `allowed` and NOT a meta-fvar.
///
/// Mirrors `meta_ext::find_escaping_fvar`; duplicated locally to keep the
/// unifier independent of the `MetaCtx` layer.
pub(super) fn find_escaping_fvar(expr: &Expr, allowed: &HashSet<FVarId>) -> Option<FVarId> {
    struct Finder<'a> {
        allowed: &'a HashSet<FVarId>,
        found: Option<FVarId>,
    }
    impl ExprVisitor for Finder<'_> {
        type Result = ();
        fn combine(&self, _a: (), _b: ()) {}
        fn visit_fvar(&mut self, id: FVarId) {
            if MetaState::from_fvar(id).is_some() {
                return;
            }
            if self.found.is_none() && !self.allowed.contains(&id) {
                self.found = Some(id);
            }
        }
    }
    let mut finder = Finder {
        allowed,
        found: None,
    };
    finder.visit_expr(expr);
    finder.found
}

/// Find an unassigned metavariable whose captured local scope is wider than
/// `allowed`.
///
/// Meta-FVars cannot be treated as scope-neutral placeholders: a later
/// assignment may reveal any local captured when that metavariable was
/// created.  Embedding such a metavariable in an assignment with a narrower
/// scope would therefore permit a delayed local escape even when the current
/// expression contains no ordinary FVar outside `allowed`.
pub(super) fn find_scope_widening_meta(
    expr: &Expr,
    allowed: &HashSet<FVarId>,
    metas: &MetaState,
) -> Option<MetaId> {
    struct Finder<'a> {
        allowed: &'a HashSet<FVarId>,
        metas: &'a MetaState,
        found: Option<MetaId>,
    }
    impl ExprVisitor for Finder<'_> {
        type Result = ();
        fn combine(&self, _a: (), _b: ()) {}
        fn visit_fvar(&mut self, id: FVarId) {
            let Some(meta_id) = MetaState::from_fvar(id) else {
                return;
            };
            let Some(meta) = self.metas.get(meta_id) else {
                return;
            };
            let wider = meta
                .locals
                .iter()
                .any(|(_, fvar, _)| !self.allowed.contains(fvar));
            if meta.assignment.is_none() && wider {
                self.found.get_or_insert(meta_id);
            }
        }
    }
    let mut finder = Finder {
        allowed,
        metas,
        found: None,
    };
    finder.visit_expr(expr);
    finder.found
}

fn collect_unassigned_metas(expr: &Expr, metas: &MetaState) -> Vec<MetaId> {
    struct Collector<'a> {
        metas: &'a MetaState,
        found: Vec<MetaId>,
    }
    impl ExprVisitor for Collector<'_> {
        type Result = ();
        fn combine(&self, _a: (), _b: ()) {}
        fn visit_fvar(&mut self, id: FVarId) {
            let Some(meta_id) = MetaState::from_fvar(id) else {
                return;
            };
            if self
                .metas
                .get(meta_id)
                .is_some_and(|meta| meta.assignment.is_none())
            {
                self.found.push(meta_id);
            }
        }
    }
    let mut collector = Collector {
        metas,
        found: Vec::new(),
    };
    collector.visit_expr(expr);
    collector.found
}
