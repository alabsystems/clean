// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Memoised kernel `LocalContext` for `ProofState`.
//!
//! MEASURED, NOT SPECULATIVE. The performance audit's `sample` of the 189.5 s
//! `simp_rw` in `Function.Injective.linearOrder` (`Mathlib/Order/Basic.lean`,
//! `reports/lean4-replacement-audit-2026-09-24/performance.json`) put **23%**
//! of the process in `ProofState::build_local_ctx`, reached from
//! `ProofState::whnf` under `reduce_op_projection_head` — once per simp lemma
//! ATTEMPT. Every call re-instantiated every local and every metavariable type
//! through the `MetaState`, minted a `?mN` name per metavariable, and re-ran
//! the sibling-goal fixpoint (`thread_sibling_ctx_fvars`, a full
//! `collect_fvars` walk of every declaration type, 10% on its own), although
//! nothing a simp attempt does between two `whnf` calls changes any of it.
//! `ElabCtx` fixed the same shape for its own context in
//! `infer/local_ctx_cache.rs`; this is the tactic-side twin.
//!
//! # The key is exact
//!
//! [`ProofState::build_local_ctx`] is a pure function of four inputs, and the
//! memo compares all four before serving a hit:
//!
//! * the metavariable state, by `MetaState::generation` — re-minted from a
//!   process-wide source on every instantiation-relevant mutation
//!   (`crate::state_generation`), so equal generations are equal content;
//! * `elab_locals`, the goal's `local_ctx`, and every goal's `local_ctx` (the
//!   sibling fixpoint reads them all) — compared declaration by declaration
//!   on exactly the fields the context is built from (id, name, type,
//!   reduction-visible value and binder annotation). These vectors are plain
//!   `pub(crate)` fields mutated all over the tactic layer, so they are compared by CONTENT rather than trusted to a
//!   generation nobody would remember to bump; `Expr` equality short-circuits
//!   on shared `Arc` children, so an unchanged context compares in time
//!   linear in its length with no traversal of the types.
//!
//! The memo is thread-local and holds one entry. Because the key is content,
//! a hit is correct whichever `ProofState` (clone, focused sub-state) asks.
//!
//! A stale hit would silently change what the kernel sees, so debug builds
//! audit every hit against a from-scratch rebuild and panic on the first
//! difference; the `clean-elab` suite runs with debug assertions.

use std::cell::RefCell;
use std::sync::Arc;

use clean_kernel::LocalContext;

use super::{Goal, LocalDecl, ProofState};

/// One memoised context and the inputs it was built from.
struct Memo {
    metas_generation: u64,
    elab_locals: Vec<LocalDecl>,
    goal_ctx: Vec<LocalDecl>,
    goal_ctxs: Vec<Vec<LocalDecl>>,
    ctx: Arc<LocalContext>,
}

thread_local! {
    static MEMO: RefCell<Option<Memo>> = const { RefCell::new(None) };
}

/// Two declaration lists agree on every field `build_local_ctx` reads.
fn same_decls(a: &[LocalDecl], b: &[LocalDecl]) -> bool {
    a.len() == b.len()
        && a.iter().zip(b).all(|(x, y)| {
            x.fvar == y.fvar
                && x.name.name() == y.name.name()
                && x.ty == y.ty
                && x.reduction_value() == y.reduction_value()
                && x.binder_info == y.binder_info
        })
}

impl Memo {
    fn serves(&self, state: &ProofState, goal: &Goal) -> bool {
        self.metas_generation == state.metas.generation()
            && self.goal_ctxs.len() == state.goals.len()
            && same_decls(&self.goal_ctx, &goal.local_ctx)
            && same_decls(&self.elab_locals, &state.elab_locals)
            && self
                .goal_ctxs
                .iter()
                .zip(&state.goals)
                .all(|(cached, g)| same_decls(cached, &g.local_ctx))
    }
}

impl ProofState {
    /// The kernel `LocalContext` for `goal`, shared: served from the memo when
    /// none of its inputs changed since the last build, rebuilt otherwise.
    ///
    /// ENSURES: the result equals `self.rebuild_local_ctx(goal)` declaration
    ///   for declaration (audited on every hit in debug builds).
    pub(crate) fn shared_local_ctx(&self, goal: &Goal) -> Arc<LocalContext> {
        let hit = MEMO.with(|memo| {
            memo.borrow()
                .as_ref()
                .filter(|m| m.serves(self, goal))
                .map(|m| Arc::clone(&m.ctx))
        });
        if let Some(ctx) = hit {
            #[cfg(debug_assertions)]
            self.audit_local_ctx_memo(goal, &ctx);
            return ctx;
        }
        let ctx = Arc::new(self.rebuild_local_ctx(goal));
        MEMO.with(|memo| {
            *memo.borrow_mut() = Some(Memo {
                metas_generation: self.metas.generation(),
                elab_locals: self.elab_locals.clone(),
                goal_ctx: goal.local_ctx.clone(),
                goal_ctxs: self.goals.iter().map(|g| g.local_ctx.clone()).collect(),
                ctx: Arc::clone(&ctx),
            });
        });
        ctx
    }

    /// Debug-build audit: a served hit must equal a from-scratch rebuild, by
    /// free-variable id (metavariables come out of a hash map, so order is
    /// not part of the contract). Panics naming the first difference: a
    /// mutation the key does not see.
    #[cfg(debug_assertions)]
    fn audit_local_ctx_memo(&self, goal: &Goal, cached: &LocalContext) {
        let rebuilt = self.rebuild_local_ctx(goal);
        let stale = |what: String| -> ! {
            panic!(
                "ProofState local-context memo is STALE: {what}; an input of \
                 build_local_ctx changed without changing the memo key (see \
                 crates/clean-elab/src/tactic/core/local_ctx_memo.rs)"
            )
        };
        if cached.len() != rebuilt.len() {
            stale(format!(
                "cached has {} declarations, rebuilt has {}",
                cached.len(),
                rebuilt.len()
            ));
        }
        for decl in cached.iter() {
            let Some(fresh) = rebuilt.get(decl.id) else {
                stale(format!(
                    "cached fvar {:?} is absent from the rebuild",
                    decl.id
                ));
            };
            if decl.name != fresh.name
                || decl.type_ != fresh.type_
                || decl.value != fresh.value
                || decl.bi != fresh.bi
            {
                stale(format!("fvar {:?} ({}) differs", decl.id, decl.name));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::unify::MetaState;
    use clean_kernel::{Environment, Expr, FVarId};

    fn local(fvar: u64, name: &str, ty: Expr) -> LocalDecl {
        LocalDecl {
            binder_info: Default::default(),
            fvar: FVarId::new(fvar),
            name: clean_parser::SurfaceName::generated_path(name),
            ty,
            value: None,
        }
    }

    #[test]
    fn binder_annotation_change_invalidates_context_cache() {
        let mut state = ProofState::with_context(
            Environment::new(),
            Expr::prop(),
            vec![local(0, "x", Expr::prop())],
        );
        let before = state.shared_local_ctx(state.current_goal().unwrap());
        state.goals[0].local_ctx[0].binder_info = clean_kernel::BinderInfo::Implicit.into();
        let after = state.shared_local_ctx(state.current_goal().unwrap());
        assert!(!Arc::ptr_eq(&before, &after));
        assert_eq!(
            after.get(FVarId::new(0)).unwrap().bi.info,
            clean_kernel::BinderInfo::Implicit
        );
    }

    #[test]
    fn test_shared_local_ctx_unchanged_state_serves_the_same_arc() {
        let env = Environment::new();
        let state = ProofState::new(env, Expr::prop());
        let goal = state.current_goal().cloned().expect("a goal");
        let a = state.shared_local_ctx(&goal);
        let b = state.shared_local_ctx(&goal);
        assert!(Arc::ptr_eq(&a, &b), "an unchanged state must hit");
    }

    #[test]
    fn test_shared_local_ctx_follows_a_hypothesis_added_to_the_goal() {
        let env = Environment::new();
        let mut state = ProofState::new(env, Expr::prop());
        let goal = state.current_goal().cloned().expect("a goal");
        let before = state.shared_local_ctx(&goal);
        assert!(before.get(FVarId::new(900)).is_none());

        state.goals[0].local_ctx.push(local(900, "h", Expr::prop()));
        let goal = state.current_goal().cloned().expect("a goal");
        let after = state.shared_local_ctx(&goal);
        assert!(!Arc::ptr_eq(&before, &after), "a new local must miss");
        assert!(after.get(FVarId::new(900)).is_some());
    }

    #[test]
    fn test_shared_local_ctx_follows_a_hypothesis_type_rewritten_in_place() {
        let env = Environment::new();
        let mut state = ProofState::new(env, Expr::prop());
        state.goals[0].local_ctx.push(local(901, "h", Expr::prop()));
        let goal = state.current_goal().cloned().expect("a goal");
        let before = state.shared_local_ctx(&goal);
        assert_eq!(
            before.get(FVarId::new(901)).map(|d| d.type_.clone()),
            Some(Expr::prop())
        );

        // Same length, same fvar, same name: only the TYPE moved, which is
        // the `simp at h` / `rw at h` shape a length-keyed memo would miss.
        state.goals[0].local_ctx[0].ty = Expr::type_();
        let goal = state.current_goal().cloned().expect("a goal");
        let after = state.shared_local_ctx(&goal);
        assert_eq!(
            after.get(FVarId::new(901)).map(|d| d.type_.clone()),
            Some(Expr::type_())
        );
    }

    #[test]
    fn test_shared_local_ctx_follows_metavariable_assignment_and_undo() {
        let env = Environment::new();
        let mut state = ProofState::new(env, Expr::prop());
        let m = state.metas.fresh(Expr::type_());
        let m_fvar = MetaState::to_fvar(m);
        state.goals[0]
            .local_ctx
            .push(local(902, "x", Expr::fvar(m_fvar)));
        let goal = state.current_goal().cloned().expect("a goal");
        let open = state.shared_local_ctx(&goal);
        assert_eq!(
            open.get(FVarId::new(902)).map(|d| d.type_.clone()),
            Some(Expr::fvar(m_fvar))
        );

        state.metas.push_scope();
        assert!(state.metas.assign(m, Expr::prop()));
        let assigned = state.shared_local_ctx(&goal);
        assert_eq!(
            assigned.get(FVarId::new(902)).map(|d| d.type_.clone()),
            Some(Expr::prop()),
            "an assignment must be seen"
        );

        assert!(state.metas.pop_scope());
        let undone = state.shared_local_ctx(&goal);
        assert_eq!(
            undone.get(FVarId::new(902)).map(|d| d.type_.clone()),
            Some(Expr::fvar(m_fvar)),
            "undoing the assignment must be seen"
        );
    }

    #[test]
    fn marked_have_and_equal_let_do_not_share_reduction_contexts() {
        let mut env = Environment::new();
        env.init_nat().expect("Nat init");
        let nat = Expr::const_(clean_kernel::Name::from_string("Nat"), vec![]);
        let value = Expr::nat_lit(7);
        let marked = super::super::have_value(value.clone());
        // Structural equality retains the marker; kernel reduction ignores
        // it. Local reduction visibility must still distinguish the origins.
        assert_ne!(value, marked);
        assert_eq!(clean_kernel::TypeChecker::new(&env).whnf(&marked), value);
        let mut state = ProofState::new(env, nat.clone());
        let mut decl = local(903, "h", nat);
        decl.value = Some(value.clone());
        state.goals[0].local_ctx.push(decl);
        let goal = state.current_goal().cloned().expect("goal");
        let transparent = state.shared_local_ctx(&goal);
        assert_eq!(state.whnf(&goal, &Expr::fvar(FVarId::new(903))), value);

        // Same meta generation, name, id, type and underlying proof payload.
        // A clone is the focused/sibling-state shape the thread-local memo sees.
        let mut opaque = state.clone();
        opaque.goals[0].local_ctx[0].value = Some(marked.clone());
        assert_eq!(state.metas.generation(), opaque.metas.generation());
        let opaque_goal = opaque.current_goal().cloned().expect("goal");
        let rigid = opaque.shared_local_ctx(&opaque_goal);
        assert!(!Arc::ptr_eq(&transparent, &rigid));
        assert!(rigid.get(FVarId::new(903)).expect("local").value.is_none());
        assert_eq!(
            opaque.whnf(&opaque_goal, &Expr::fvar(FVarId::new(903))),
            Expr::fvar(FVarId::new(903))
        );
        assert!(opaque.goals[0].local_ctx[0].is_have());
        assert_eq!(opaque.goals[0].local_ctx[0].value.as_ref(), Some(&marked));
        // Restoring the genuine let must restore reduction as well.
        assert_eq!(state.whnf(&goal, &Expr::fvar(FVarId::new(903))), value);
    }

    #[test]
    fn enclosing_marked_have_proofs_stay_opaque() {
        let mut env = Environment::new();
        env.init_nat().expect("Nat init");
        let nat = Expr::const_(clean_kernel::Name::from_string("Nat"), vec![]);
        let mut state = ProofState::new(env, nat.clone());
        let mut decl = local(904, "h", nat);
        decl.value = Some(super::super::have_value(Expr::nat_lit(7)));
        state.elab_locals.push(decl);
        let goal = state.current_goal().cloned().expect("goal");
        assert_eq!(
            state.whnf(&goal, &Expr::fvar(FVarId::new(904))),
            Expr::fvar(FVarId::new(904))
        );
        assert!(state.elab_locals[0].value.is_some());
    }

    #[test]
    fn opaque_clones_keep_distinct_full_binder_data_in_the_memo() {
        let mut state = ProofState::with_context(
            Environment::new(),
            Expr::prop(),
            vec![local(905, "h", Expr::prop())],
        );
        let raw = super::super::have_value(Expr::prop());
        state.goals[0].local_ctx[0].value = Some(raw.clone());
        let first = state.shared_local_ctx(state.current_goal().expect("goal"));
        let mut clone = state.clone();
        let data = clean_kernel::BinderData::new(
            clean_kernel::BinderInfo::StrictImplicit,
            clean_kernel::Multiplicity::One,
        );
        clone.goals[0].local_ctx[0].binder_info = data;
        let second = clone.shared_local_ctx(clone.current_goal().expect("cloned goal"));
        assert!(!Arc::ptr_eq(&first, &second));
        assert_eq!(second.get(FVarId::new(905)).expect("opaque local").bi, data);
        assert!(second
            .get(FVarId::new(905))
            .expect("opaque local")
            .value
            .is_none());
        assert_eq!(clone.goals[0].local_ctx[0].value.as_ref(), Some(&raw));
        assert_eq!(state.goals[0].local_ctx[0].binder_info, Default::default());
    }
}
