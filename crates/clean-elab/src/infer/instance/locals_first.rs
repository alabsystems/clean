// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Local instances before global ones, at every sub-goal, in one pass.
//!
//! Lean's `getInstances` (`Lean/Meta/SynthInstance.lean`) opens the goal's
//! `∀`-telescope at reducible transparency, takes its class, returns the
//! global instances of that class and then appends EVERY local instance of it
//! in local-context order; the search tries the list from the end. So the
//! most recent local instance that unifies answers the goal, whatever its
//! shape — a class application (`[Decidable (1 = 1)]`), a `∀`-telescope
//! (`[∀ n, Decidable (n = 1)]` answers `Decidable (1 = 1)` with `inst 1`), a
//! reducible class alias (`[DecidableEq Nat]` answers `Decidable (1 = 2)`
//! with `inst 1 2`) — and an ALIAS goal (`DecidableEq Nat`) is answered, once
//! opened, by a local of the alias's unfolding (`(i : ∀ a b, Decidable (a =
//! b))` answers it with `i`). A local's own `[inst]` binders are sub-goals,
//! synthesized before the local is taken (`inst : ∀ n, [Foo n] → Decidable (n
//! = 1)` answers `Decidable (1 = 1)` with `inst 1 instFoo1`, and is skipped
//! when `Foo 1` has no instance). Pinned v4.30.0-rc2 measures each
//! (`tests/decide_lean_order_e2e.rs`, `tests/decide_lean_instances_e2e.rs`).
//!
//! [`ElabCtx::try_local_instance`] is that per-local step; the primary local
//! loop of `resolve_instance_candidates` calls it for every local whose type
//! is not a plain application of the goal's class, at its own place in the
//! most-recent-first order, so an older class-headed local no longer shadows
//! a newer one of another shape (DECISIONS R127).
//!
//! A local counts as Lean's `isClass?` reads its type: the `∀`-telescope is
//! opened at REDUCIBLE transparency (`forallTelescopeReducing` under
//! `withReducible`), so `DecidableEq α` and `DecidablePred p` open and a
//! semireducible `def MyCAll := (a : Type) → MyC a` does not — a local of that
//! type is no instance in Lean, and the global keeps winning
//! (`tests/fixtures/source_frontier/p21_control_global_beats_telescoped_local`).

use std::collections::HashSet;

use super::super::ElabCtx;
use super::{has_meta_fvar_outside, INSTANCE_SEARCH_BUDGET, MAX_LOCAL_TELESCOPE};
use crate::instances::extract_class_app_with_levels;
use clean_kernel::{BinderData, BinderInfo, Expr, ExprKind, FVarId, Level, Name};

/// The goal a local is matched against.
struct ClassGoal<'g> {
    class: &'g Name,
    levels: &'g [Level],
    args: &'g [Expr],
    metas: &'g HashSet<FVarId>,
}

/// What matching one local against one goal established.
enum LocalMatch {
    /// The local answers the goal with this term.
    Found(Expr),
    /// The local's telescope never reached the goal's class.
    OtherClass,
    /// It reached the goal's class and failed there (unification, a
    /// sub-goal, an undetermined binder): no other spelling of the same goal
    /// is tried for it, so a local is searched once per goal.
    Failed,
}

/// Where a local's own `[inst]` sub-goals are searched: the enclosing
/// search's depth, active path and open-input mode.
pub(super) struct SubSearch<'p> {
    pub(super) depth: usize,
    pub(super) goal_path: &'p mut Vec<String>,
    pub(super) strict: bool,
}

impl ElabCtx<'_> {
    /// Every local instance tried against `goal_ty`, most recent first
    /// ([`Self::try_local_instance`]); the first that answers it.
    pub(super) fn resolve_locals_first(
        &mut self,
        goal_ty: &Expr,
        sub: &mut SubSearch<'_>,
    ) -> Option<Expr> {
        if self.local_instances.is_empty() || self.instance_search_stuck {
            return None;
        }
        (0..self.local_instances.len())
            .rev()
            .find_map(|i| self.try_local_instance(i, goal_ty, sub))
    }

    /// The local instance at index `i` answering `goal_ty`, or `None`.
    ///
    /// Lean's search runs at a deeper metavariable depth
    /// (`withNewMCtxDepth`), so it cannot assign the caller's metavariables: a
    /// local that matches only by CHOOSING one of them is stuck there, not
    /// taken. Such a match is not made here; the goal falls through to the
    /// candidates and, failing them, to the telescoped match the search has
    /// always made last (`resolve_instance_with_depth`).
    pub(super) fn try_local_instance(
        &mut self,
        i: usize,
        goal_ty: &Expr,
        sub: &mut SubSearch<'_>,
    ) -> Option<Expr> {
        if self.instance_search_stuck {
            return None;
        }
        let goal_ty = self.metas.instantiate(goal_ty);
        let (class, levels, args) = extract_class_app_with_levels(&goal_ty)?;
        let metas = self.collect_meta_fvars(&goal_ty);
        let goal = ClassGoal {
            class: &class,
            levels: &levels,
            args: &args,
            metas: &metas,
        };
        let (fvar, local_ty) = self.local_instances.get(i)?.clone();
        self.metas.push_scope();
        match self.match_local_reducibly(fvar, &local_ty, &goal, sub) {
            LocalMatch::Found(found) => {
                self.metas.commit();
                Some(found)
            }
            LocalMatch::Failed => {
                self.metas.pop_scope();
                None
            }
            LocalMatch::OtherClass => {
                self.metas.pop_scope();
                self.match_local_against_opened_goal(fvar, &local_ty, &goal_ty, &metas, sub)
            }
        }
    }

    /// An ALIAS goal (`DecidableEq Nat`, `DecidablePred p`) opened at
    /// reducible transparency over fresh locals (`a b : Nat ⊢ Decidable (a =
    /// b)`), the local matched against its conclusion, and the match
    /// abstracted back over those locals (`fun a b => i a b`, which is `i`).
    fn match_local_against_opened_goal(
        &mut self,
        fvar: FVarId,
        local_ty: &Expr,
        goal_ty: &Expr,
        goal_metas: &HashSet<FVarId>,
        sub: &mut SubSearch<'_>,
    ) -> Option<Expr> {
        let opened = self.whnf_reducible(goal_ty);
        if !matches!(opened.kind(), ExprKind::Pi(..)) {
            return None;
        }
        let mut binders: Vec<(BinderData, Expr, FVarId)> = Vec::new();
        let mut cursor = opened;
        while let ExprKind::Pi(binder, domain, body) = cursor.kind() {
            if binders.len() >= MAX_LOCAL_TELESCOPE || binder.info == BinderInfo::InstImplicit {
                break;
            }
            let (binder, domain) = (*binder, self.metas.instantiate(domain));
            let local = self.fresh_fvar();
            self.push_local_with_fvar(
                clean_parser::SurfaceName::from_name(
                    Name::anon().str("_aliasgoal").num(local.as_u64()),
                ),
                local,
                domain.clone(),
            );
            let next = body.instantiate(&Expr::fvar(local));
            binders.push((binder, domain, local));
            cursor = self.whnf_reducible(&next);
        }
        let mut result = None;
        if !binders.is_empty() && !matches!(cursor.kind(), ExprKind::Pi(..)) {
            if let Some((class, levels, args)) = extract_class_app_with_levels(&cursor) {
                let goal = ClassGoal {
                    class: &class,
                    levels: &levels,
                    args: &args,
                    metas: goal_metas,
                };
                self.metas.push_scope();
                match self.match_local_reducibly(fvar, local_ty, &goal, sub) {
                    LocalMatch::Found(found) => {
                        self.metas.commit();
                        result = Some(abstract_opened(found, &binders));
                    }
                    LocalMatch::OtherClass | LocalMatch::Failed => {
                        self.metas.pop_scope();
                    }
                }
            }
        }
        for _ in 0..binders.len() {
            self.pop_local();
        }
        result
    }

    /// Open `local_ty`'s `∀`-telescope at reducible transparency, binders as
    /// fresh metavariables, until a class application of the goal's class
    /// appears; match it, synthesize the local's own `[inst]` binders, and
    /// return the local applied to the binders.
    ///
    /// REQUIRES: a metavariable scope is open; the caller pops it unless the
    /// result is `Found`.
    fn match_local_reducibly(
        &mut self,
        fvar: FVarId,
        local_ty: &Expr,
        goal: &ClassGoal<'_>,
        sub: &mut SubSearch<'_>,
    ) -> LocalMatch {
        let mut cursor = self.metas.instantiate(local_ty);
        let mut binders: Vec<Expr> = Vec::new();
        // `[inst]` binders with their (still open) types, in telescope order.
        let mut instance_binders: Vec<(Expr, Expr)> = Vec::new();
        loop {
            let reduced = self.whnf_reducible(&cursor);
            for candidate in [&cursor, &reduced] {
                let Some((class, levels, args)) = extract_class_app_with_levels(candidate) else {
                    continue;
                };
                if &class != goal.class || args.len() != goal.args.len() {
                    continue;
                }
                return match self.finish_local_match(
                    fvar,
                    binders,
                    &instance_binders,
                    (levels.as_slice(), args.as_slice()),
                    goal,
                    sub,
                ) {
                    Some(found) => LocalMatch::Found(found),
                    None => LocalMatch::Failed,
                };
            }
            let ExprKind::Pi(binder, domain, body) = reduced.kind() else {
                return LocalMatch::OtherClass;
            };
            if binders.len() >= MAX_LOCAL_TELESCOPE {
                return LocalMatch::OtherClass;
            }
            let domain = self.metas.instantiate(domain);
            let meta = self.fresh_meta(domain.clone());
            if binder.info == BinderInfo::InstImplicit {
                instance_binders.push((meta.clone(), domain));
            }
            cursor = body.instantiate(&meta);
            binders.push(meta);
        }
    }

    /// Unify the local's class arguments (and levels) with the goal's at
    /// instance transparency, then synthesize its `[inst]` binders as
    /// sub-goals (Lean's `synthOrder`: in telescope order, each once the match
    /// has determined its type); keep the match only when every binder is
    /// determined and no goal metavariable was chosen.
    fn finish_local_match(
        &mut self,
        fvar: FVarId,
        binders: Vec<Expr>,
        instance_binders: &[(Expr, Expr)],
        (levels, args): (&[Level], &[Expr]),
        goal: &ClassGoal<'_>,
        sub: &mut SubSearch<'_>,
    ) -> Option<Expr> {
        // `try_match_local_instance` pushes a scope of its own.
        if !self.try_match_local_instance(levels, args, goal.levels, goal.args) {
            self.metas.pop_scope();
            return None;
        }
        self.metas.commit();
        for (meta, ty) in instance_binders {
            let ty = self.metas.instantiate(ty);
            // A sub-search costs one candidate attempt of the per-query
            // budget, and a ground sub-goal that failed once in this query
            // fails again at once: without both, two locals of one conclusion
            // (or one local with a `[DecidableEq α]` binder, reached through
            // the goal, its bridge and its opened alias) search the same
            // sub-goals 2^n or 3^n times, exhaust the budget, and the global
            // instance Lean would pick is never tried.
            if self.instance_search_steps >= INSTANCE_SEARCH_BUDGET {
                return None;
            }
            self.instance_search_steps += 1;
            let failure_key = (!self.has_metavars(&ty)).then(|| self.normalize_for_cache(&ty));
            if failure_key
                .as_ref()
                .is_some_and(|key| self.failed_local_subgoals.contains(key))
            {
                return None;
            }
            let Some(found) =
                self.resolve_instance_with_depth(&ty, sub.depth + 1, sub.goal_path, sub.strict)
            else {
                if let Some(key) = failure_key {
                    self.failed_local_subgoals.insert(key);
                }
                return None;
            };
            if !self.try_unify(meta, &found) {
                return None;
            }
        }
        let undetermined = binders.iter().any(|binder| {
            let solved = self.metas.instantiate(binder);
            has_meta_fvar_outside(&solved, goal.metas)
        });
        let chose_a_goal_metavariable = goal.metas.iter().any(|meta| {
            let open = Expr::fvar(*meta);
            self.metas.instantiate(&open) != open
        });
        if undetermined || chose_a_goal_metavariable {
            return None;
        }
        let applied = Expr::apps(Expr::fvar(fvar), binders);
        Some(
            self.metas
                .instantiate_levels(&self.metas.instantiate(&applied)),
        )
    }
}

/// `found` abstracted over the opened goal's locals, eta-reduced when it is
/// just a function applied to them in order (`i a b` gives `i`, as Lean
/// prints it).
fn abstract_opened(found: Expr, binders: &[(BinderData, Expr, FVarId)]) -> Expr {
    // The borrows of `found` (its head and argument list) end inside this
    // block, before `found` is moved into the fold below.
    let eta = {
        let head = found.get_app_fn();
        let args = found.get_app_args();
        let applied_to_them = args.len() == binders.len()
            && args.iter().zip(binders).all(
                |(arg, (_, _, local))| matches!(arg.kind(), ExprKind::FVar(id) if id == local),
            )
            && binders
                .iter()
                .all(|(_, _, local)| !head.abstract_fvar(*local).has_loose_bvars());
        applied_to_them.then(|| head.clone())
    };
    if let Some(head) = eta {
        return head;
    }
    binders
        .iter()
        .rev()
        .fold(found, |term, (binder, domain, local)| {
            Expr::lam(*binder, domain.clone(), term.abstract_fvar(*local))
        })
}
