// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Typeclass synthesis for a TACTIC goal.
//!
//! A tactic that holds only a `ProofState` — simp's matcher filling an
//! instance-implicit lemma binder the left-hand side did not determine — asks
//! the same question Lean's `trySynthInstance` answers inside the goal's local
//! context (`Lean/Meta/Tactic/Simp/Rewrite.lean`, `synthesizeArgs`). This is
//! that query, answered by the elaborator's own resolver
//! ([`ElabCtx::resolve_instance`]): scoped instances gated on the goal's open
//! namespaces, class-typed locals as local instances (Lean's
//! `withNewLocalInstances`, keyed on `isClass?` of the local's TYPE), and the
//! 4096-candidate search budget.

use std::collections::{HashMap, HashSet};

use clean_kernel::env::Reducibility;
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, ExprKind, FVarId};
use clean_parser::SurfaceName;

use super::ElabCtx;
use crate::instances::InstanceTable;
use crate::namespace::NamespaceState;
use crate::unify::MetaState;

/// The elaborator's instance visibility at a tactic entry point: the `local
/// instance`s whose section has ended (hidden) and each `scoped instance`'s
/// declaring namespace (visible only where it is open). Carried into the
/// `ProofState` so a tactic's instance query answers as the elaborator's
/// would — without it a file's own `scoped instance` would answer everywhere,
/// the silent-acceptance face of class (8).
#[derive(Debug, Clone, Default)]
pub(crate) struct InstanceVisibility {
    pub(crate) hidden: HashSet<Name>,
    pub(crate) scoped: HashMap<Name, Name>,
    /// The module's instance state, when the enclosing context has it
    /// (`ElabCtx::set_instance_view`).
    pub(crate) view: Option<crate::instance_store::InstanceView>,
    /// Whether a `classical` block is open here. `Lean.Elab.Tactic.classical`
    /// (`Lean/Elab/Tactic/Classical.lean:22-29`) pushes an instance-extension
    /// scope and adds `Classical.propDecidable` at priority 10 for the
    /// duration, so EVERY consumer sees it — including simp, whose
    /// `synthesizeArgs` just calls `trySynthInstance` in the ambient `MetaM`.
    /// Clean's depth counter lives on the `ElabCtx`
    /// ([`ElabCtx::classical_tactic_scope`]) and the tactic layer builds a
    /// FRESH one per query, so without this flag the counter is 0 inside
    /// every tactic-side synthesis and `Classical.propDecidable` is hidden
    /// there — `Function.extend_def`, whose `[Decidable (∃ a, f a = b)]` the
    /// left-hand side does not determine, was never applied and simp reported
    /// "no progress" under a `classical` that works for `exact`/`have`.
    pub(crate) classical_scope: bool,
}

impl ElabCtx<'_> {
    /// This context's instance visibility, for a tactic block it opens.
    pub(crate) fn instance_visibility(&self) -> InstanceVisibility {
        InstanceVisibility {
            hidden: self.hidden_instances.clone(),
            scoped: self.scoped_instances.clone(),
            view: self.instance_view.clone(),
            classical_scope: self.classical_tactic_scope > 0,
        }
    }
}

/// Everything a tactic goal contributes to an instance query.
pub(crate) struct TacticInstanceScope<'s> {
    /// The enclosing elaborator's instance table (`ProofState::instances`);
    /// `None` builds one from the environment.
    pub(crate) instances: Option<&'s InstanceTable>,
    /// Open namespaces, which gate `scoped instance`s.
    pub(crate) namespace_state: Option<&'s NamespaceState>,
    /// The enclosing elaborator's instance visibility; `None` applies the
    /// environment's imported scoping only.
    pub(crate) visibility: Option<&'s InstanceVisibility>,
    /// The declaration's universe parameters: never assignable by the search.
    pub(crate) rigid_levels: HashSet<Name>,
    /// The goal's locals (elaborator locals and goal context), each
    /// `(name, fvar, type)`.
    pub(crate) locals: Vec<(SurfaceName, FVarId, Expr)>,
    /// First free-variable id the search may mint.
    pub(crate) next_fvar: u64,
    /// The proof state's universe-level mint (`ProofState::level_mint`), so a
    /// level metavariable the search mints can never share a spelling with
    /// one the declaration already holds (the name-keyed `MetaState` would
    /// otherwise read a fresh `?u_0` as the goal's own, possibly rigid,
    /// `?u_0`).
    pub(crate) level_mint: crate::level_mint::LevelMint,
}

impl TacticInstanceScope<'_> {
    /// The first free-variable id the search may mint: past `next_fvar` and
    /// past every ORDINARY local.
    ///
    /// Two kinds of local are not ordinary and must not move it. A
    /// metavariable-encoded id carries bit 63. A simp binder temporary — a
    /// local simp pushed while rewriting under a binder — comes from a
    /// DESCENDING allocator that starts just below that bit, precisely so it
    /// can never meet an allocator counting up from small ids; seeding this
    /// one past the first temporary of a process would start it AT bit 63,
    /// and the telescope locals the resolver opens
    /// (`resolve_pi_goal_by_abstraction`) would decode as metavariables.
    ///
    /// ENSURES: the result is `next_fvar` or the successor of an ordinary
    ///   local, so it is below every simp binder temporary and the tag.
    fn first_free_fvar(&self) -> u64 {
        self.locals
            .iter()
            .map(|(_, fvar, _)| *fvar)
            .filter(|fvar| {
                MetaState::from_fvar(*fvar).is_none()
                    && !crate::tactic::simp::is_binder_temporary(*fvar)
            })
            .map(|fvar| fvar.as_u64().saturating_add(1))
            .fold(self.next_fvar, u64::max)
    }
}

impl<'a> ElabCtx<'a> {
    /// Synthesize an instance of `class_ty` in a tactic goal's scope, or
    /// `None`.
    ///
    /// # Soundness
    ///
    /// Nothing is trusted: the result is refused when the search left any of
    /// its own metavariables or universe metavariables in it, and the caller
    /// still checks its type against the slot it fills; every term simp
    /// emits is re-checked by the kernel.
    ///
    /// ENSURES: on `Some(t)`, `t` mentions no unassigned metavariable and no
    ///   reserved-space universe level that `class_ty` does not mention.
    pub(crate) fn synthesize_in_tactic_scope(
        env: &'a Environment,
        scope: &TacticInstanceScope<'_>,
        class_ty: &Expr,
    ) -> Option<Expr> {
        let mut ctx = match scope.instances {
            Some(table) => ElabCtx::with_instances(env, table.clone()),
            None => ElabCtx::new(env),
        };
        ctx.level_mint = scope.level_mint.clone();
        if let Some(ns) = scope.namespace_state {
            ctx.set_namespace_state(ns.clone());
        }
        if let Some(visibility) = scope.visibility {
            // The enclosing elaborator's map already holds the imported
            // `scoped` entries beside the file's own.
            ctx.hidden_instances = visibility.hidden.clone();
            ctx.scoped_instances = visibility.scoped.clone();
            if let Some(view) = &visibility.view {
                ctx.set_instance_view(view.clone());
            }
            // A `classical` block open at the tactic entry makes the
            // `Classical`-scoped instances visible to this query too, exactly
            // as Lean's instance-extension scope does. One level is enough:
            // `instance_visible` tests `> 0`, and the depth itself is the
            // enclosing sequence's bookkeeping, not a search parameter.
            ctx.classical_tactic_scope = u32::from(visibility.classical_scope);
        }
        // The goal's universe parameters are PARAMETERS: a candidate whose
        // level pre-check tried `u := 1` would otherwise pin the goal's own
        // `u` for every later candidate of the same query.
        let mut rigid = scope.rigid_levels.clone();
        let mut params = Vec::new();
        crate::level_params::collect_level_params_from_expr(class_ty, &mut params);
        for (_, _, ty) in &scope.locals {
            crate::level_params::collect_level_params_from_expr(ty, &mut params);
        }
        rigid.extend(
            params
                .into_iter()
                .filter(|p| !crate::level_mint::is_reserved_level_name(&p.to_string())),
        );
        ctx.metas.set_rigid_level_params(rigid);
        ctx.next_fvar = ctx.next_fvar.max(scope.first_free_fvar());
        for (name, fvar, ty) in &scope.locals {
            ctx.locals.push((name.clone(), *fvar, ty.clone()));
            // Lean's `withNewLocalInstances` is keyed on `isClass?` of the
            // local's TYPE. The local is registered under its type with
            // reducible aliases unfolded (`[DecAll p]` as `∀ n, Decidable
            // (p n)`): the resolver matches a local by class head, and the
            // alias's head is not the class.
            if let Some(class_ty) = class_goal(env, Some(&ctx.instances), ty) {
                ctx.push_local_instance(*fvar, class_ty);
            }
        }
        let found = ctx.resolve_instance(class_ty)?;
        let found = ctx.metas.instantiate_levels(&ctx.metas.instantiate(&found));
        if mentions_meta_fvar(&found) {
            return None;
        }
        // A universe metavariable the search minted and nothing fixed (the
        // class type does not mention it) must not escape into the proof:
        // it would reach the declaration boundary undetermined.
        let mut goal_levels = Vec::new();
        crate::level_params::collect_level_params_from_expr(class_ty, &mut goal_levels);
        let mut found_levels = Vec::new();
        crate::level_params::collect_level_params_from_expr(&found, &mut found_levels);
        if found_levels.iter().any(|p| {
            crate::level_mint::is_reserved_level_name(&p.to_string()) && !goal_levels.contains(p)
        }) {
            return None;
        }
        Some(found)
    }
}

/// How many reducible aliases [`class_goal`] unfolds before giving up: an
/// alias of an alias is already rare, and the cap only exists so a cyclic
/// environment cannot spin.
const MAX_ALIAS_UNFOLDS: u8 = 8;

/// The instance goal a binder or local of type `ty` poses, or `None` when
/// `ty` is not a class — Lean's `isClass?` (`Lean/Meta/Basic.lean`,
/// `isClassQuick?` / `isClassExpensive?`).
///
/// The class is the constant heading the CONCLUSION of `ty`'s `∀` telescope.
/// A conclusion headed by a REDUCIBLE definition instead (`DecidablePred p`,
/// a user `abbrev`) is unfolded — head delta plus head beta, the only steps
/// an alias needs — and read again, a bounded number of times. The result is
/// `ty` with those aliases unfolded, which is the spelling the resolver
/// answers: its telescope rule opens the `∀`s and searches the class
/// underneath, and it matches a local instance by class head.
///
/// Nothing else is reduced. A semireducible definition that happens to
/// unfold to a class is not a class, in Lean or here.
pub(crate) fn class_goal(
    env: &Environment,
    table: Option<&InstanceTable>,
    ty: &Expr,
) -> Option<Expr> {
    class_goal_with_fuel(env, table, ty, MAX_ALIAS_UNFOLDS)
}

fn class_goal_with_fuel(
    env: &Environment,
    table: Option<&InstanceTable>,
    ty: &Expr,
    fuel: u8,
) -> Option<Expr> {
    crate::stack_safe(|| {
        if let ExprKind::Pi(binder, domain, body) = ty.kind() {
            let body = class_goal_with_fuel(env, table, body, fuel)?;
            return Some(Expr::pi(*binder, domain.as_ref().clone(), body));
        }
        let ExprKind::Const(head, levels) = ty.get_app_fn().kind() else {
            return None;
        };
        if env.is_class(head) || table.is_some_and(|table| table.is_class(head)) {
            return Some(ty.clone());
        }
        let fuel = fuel.checked_sub(1)?;
        let info = env.get_const(head)?;
        if !matches!(info.reducibility, Reducibility::Reducible)
            || info.level_params.len() != levels.len()
        {
            return None;
        }
        let value = info
            .value
            .as_ref()?
            .instantiate_level_params_direct(&info.level_params, levels);
        let args = ty.get_app_args().into_iter().cloned();
        let unfolded = crate::tactic::op_projection::head_beta(&Expr::apps(value, args));
        class_goal_with_fuel(env, table, &unfolded, fuel)
    })
}

/// Whether `e` mentions a metavariable-encoded free variable.
fn mentions_meta_fvar(e: &Expr) -> bool {
    crate::stack_safe(|| match e.kind() {
        ExprKind::FVar(id) => MetaState::from_fvar(*id).is_some(),
        ExprKind::App(f, a) => mentions_meta_fvar(f) || mentions_meta_fvar(a),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            mentions_meta_fvar(ty) || mentions_meta_fvar(body)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            mentions_meta_fvar(ty) || mentions_meta_fvar(val) || mentions_meta_fvar(body)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
            mentions_meta_fvar(inner)
        }
        _ => false,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tactic::simp::open_binder;
    use crate::tactic::Goal;

    fn scope_with(
        locals: Vec<(SurfaceName, FVarId, Expr)>,
        next_fvar: u64,
    ) -> TacticInstanceScope<'static> {
        TacticInstanceScope {
            instances: None,
            namespace_state: None,
            visibility: None,
            rigid_levels: HashSet::new(),
            locals,
            next_fvar,
            level_mint: crate::level_mint::LevelMint::default(),
        }
    }

    /// A local simp opened while rewriting under a binder lives just below
    /// the metavariable tag. Seeding the search's up-counting allocator past
    /// it would mint locals that decode as metavariables (the first
    /// temporary of a process is `(1 << 63) - 1`, whose successor IS the
    /// tag), so only ordinary locals and `next_fvar` may move it.
    #[test]
    fn test_first_free_fvar_with_a_simp_binder_temporary_in_scope_stays_below_it() {
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let goal = Goal {
            meta_id: crate::unify::MetaId(0),
            target: nat.clone(),
            local_ctx: Vec::new(),
            tag: None,
            case_binders: Vec::new(),
        };
        let temporary = open_binder(&goal, &nat, &Expr::bvar(0)).fvar;
        assert!(crate::tactic::simp::is_binder_temporary(temporary));
        let name = |s: &str| SurfaceName::generated_path(s);
        let scope = scope_with(
            vec![
                (name("h"), FVarId::new(7), nat.clone()),
                (name("_simp_binder"), temporary, nat.clone()),
            ],
            3,
        );
        let first = scope.first_free_fvar();
        assert_eq!(first, 8, "one past the largest ORDINARY local");
        assert!(MetaState::from_fvar(FVarId::new(first)).is_none());
        assert_eq!(scope_with(Vec::new(), 11).first_free_fvar(), 11);
    }
}
