// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Memoised kernel `LocalContext` for `ElabCtx`.
//!
//! MEASURED, NOT SPECULATIVE. On `Mathlib/Logic/Basic.lean` two independent
//! 1 ms sampling profiles put 100% of elaboration time in instance
//! resolution, of which **75.6% / 76.7% was `ElabCtx::build_local_ctx`**
//! rebuilding the whole kernel context — every local AND every metavariable
//! re-instantiated through `MetaState::instantiate` and
//! `instantiate_levels` — for EVERY `whnf`, plus ~22% dropping the
//! `TypeChecker` that owned the freshly built context; the kernel's own
//! `whnf_impl` was 0.1%
//! (`docs/issues/2026-08-21-mathlib-source-frontier-logic-basic.md`).
//!
//! The context is a pure function of two states: the local bindings
//! (`LocalBindings`) and the metavariable state (`MetaState`). Both carry a
//! generation re-minted on every mutation (see `crate::state_generation` for
//! why the numbers are process-unique), so the cache key `(metas generation,
//! locals generation)` is exact: a hit means the rebuilt context would be
//! identical. The cached context is handed out as an `Arc`, and the kernel
//! `TypeChecker` holds its context behind an `Arc` with copy-on-write, so a
//! `whnf` that never pushes a binder neither clones nor rebuilds anything.
//!
//! A stale hit would be a SOUNDNESS bug in the elaborator's view of its
//! context, so debug builds audit every hit against a from-scratch rebuild
//! and panic on the first difference, naming the declaration — the
//! `clean-elab` suite runs with debug assertions, so a mutation site that
//! forgets its generation bump fails the suite rather than silently changing
//! `whnf` answers.

use super::ElabCtx;
use crate::unify::MetaState;
use clean_kernel::{BinderInfo, LocalContext, Name};
use std::sync::Arc;

/// One memoised context and the generations it was built from.
pub(crate) struct LocalCtxCache {
    metas_generation: u64,
    locals_generation: u64,
    ctx: Arc<LocalContext>,
}

impl ElabCtx<'_> {
    /// The kernel `LocalContext` for the current local bindings and
    /// metavariable state, shared: O(1) when nothing changed since the last
    /// call, a full rebuild otherwise.
    pub(crate) fn shared_local_ctx(&self) -> Arc<LocalContext> {
        let metas_generation = self.metas.generation();
        let locals_generation = self.locals.generation();
        let hit = self.local_ctx_cache.borrow().as_ref().and_then(|cache| {
            (cache.metas_generation == metas_generation
                && cache.locals_generation == locals_generation)
                .then(|| Arc::clone(&cache.ctx))
        });
        if let Some(ctx) = hit {
            #[cfg(debug_assertions)]
            self.audit_local_ctx_cache(&ctx, metas_generation, locals_generation);
            return ctx;
        }
        let ctx = Arc::new(self.rebuild_local_ctx());
        *self.local_ctx_cache.borrow_mut() = Some(LocalCtxCache {
            metas_generation,
            locals_generation,
            ctx: Arc::clone(&ctx),
        });
        ctx
    }

    /// Build the context from scratch: every local (let-bound ones as local
    /// definitions) and every metavariable, types instantiated through the
    /// current assignments and universe-level solutions.
    fn rebuild_local_ctx(&self) -> LocalContext {
        let mut ctx = LocalContext::new();
        for (name, fvar, ty) in &self.locals {
            let ty_inst = self.metas.instantiate(ty);
            let ty_inst = self.metas.instantiate_levels(&ty_inst);
            // Only genuine lets expose defining equations. Marked have
            // proofs remain stored for scope/proof reads but stay rigid in
            // the kernel reduction view. See `LocalBindings`.
            if let Some(value) = self.locals.reduction_value(*fvar) {
                let val_inst = self.metas.instantiate(value);
                let val_inst = self.metas.instantiate_levels(&val_inst);
                ctx.push_let_with_id(*fvar, name.name().clone(), ty_inst, val_inst);
            } else {
                ctx.push_with_id(
                    *fvar,
                    name.name().clone(),
                    ty_inst,
                    self.locals.binder_info(*fvar),
                );
            }
        }

        for (meta_id, meta) in self.metas.iter() {
            let name = Name::from_string(&format!("?m{}", meta_id.0));
            let ty_inst = self.metas.instantiate(&meta.ty);
            let ty_inst = self.metas.instantiate_levels(&ty_inst);
            ctx.push_with_id(
                MetaState::to_fvar(meta_id),
                name,
                ty_inst,
                BinderInfo::Implicit,
            );
        }

        ctx
    }

    /// Debug-build audit: a served hit must equal a from-scratch rebuild.
    ///
    /// Compares by free-variable id (the context is a stack but the kernel
    /// resolves fvars by id, and metavariables come out of a hash map whose
    /// order is not part of the contract). Panics naming the first
    /// difference: that is a missed generation bump at some mutation site.
    #[cfg(debug_assertions)]
    fn audit_local_ctx_cache(
        &self,
        cached: &LocalContext,
        metas_generation: u64,
        locals_generation: u64,
    ) {
        let rebuilt = self.rebuild_local_ctx();
        let stale = |what: String| -> ! {
            panic!(
                "local-context cache is STALE at generations (metas {metas_generation}, locals \
                 {locals_generation}): {what}; a mutation site is missing its generation bump \
                 (see crates/clean-elab/src/infer/local_ctx_cache.rs)"
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
                    "cached fvar {:?} ({}) is absent from the rebuilt context",
                    decl.id, decl.name
                ));
            };
            if decl.name != fresh.name {
                stale(format!(
                    "fvar {:?} is named {} in the cache, {} rebuilt",
                    decl.id, decl.name, fresh.name
                ));
            }
            if decl.type_ != fresh.type_ {
                stale(format!(
                    "fvar {:?} ({}) has cached type {:?} but rebuilt type {:?}",
                    decl.id, decl.name, decl.type_, fresh.type_
                ));
            }
            if decl.value != fresh.value {
                stale(format!(
                    "fvar {:?} ({}) has cached value {:?} but rebuilt value {:?}",
                    decl.id, decl.name, decl.value, fresh.value
                ));
            }
            if decl.bi != fresh.bi {
                stale(format!(
                    "fvar {:?} ({}) changed binder data",
                    decl.id, decl.name
                ));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::infer::ElabCtx;
    use clean_kernel::{Environment, Expr, FVarId};
    use std::sync::Arc;

    #[test]
    fn test_shared_local_ctx_is_served_from_cache_until_a_local_moves() {
        let env = Environment::new();
        let mut ctx = ElabCtx::new(&env);
        let a = ctx.shared_local_ctx();
        let b = ctx.shared_local_ctx();
        assert!(
            Arc::ptr_eq(&a, &b),
            "unchanged state must serve the same Arc"
        );

        let fvar = ctx.push_local(clean_parser::SurfaceName::generated_path("x"), Expr::prop());
        let c = ctx.shared_local_ctx();
        assert!(!Arc::ptr_eq(&a, &c), "a push must invalidate");
        assert!(
            c.get(fvar).is_some(),
            "the pushed local is in the rebuilt context"
        );

        ctx.pop_local();
        let d = ctx.shared_local_ctx();
        assert!(!Arc::ptr_eq(&c, &d), "a pop must invalidate");
        assert!(d.get(fvar).is_none());
    }

    #[test]
    fn test_shared_local_ctx_tracks_metavariable_assignment_and_rollback() {
        let env = Environment::new();
        let mut ctx = ElabCtx::new(&env);
        // A local whose type mentions a metavariable: the cached context
        // must follow the meta's assignment and its undo.
        let m = ctx.metas.fresh(Expr::type_());
        let m_fvar = crate::unify::MetaState::to_fvar(m);
        let x = ctx.push_local(
            clean_parser::SurfaceName::generated_path("x"),
            Expr::fvar(m_fvar),
        );
        let before = ctx.shared_local_ctx();
        assert_eq!(
            before.get(x).map(|d| d.type_.clone()),
            Some(Expr::fvar(m_fvar))
        );

        ctx.metas.push_scope();
        assert!(ctx.metas.assign(m, Expr::prop()));
        let assigned = ctx.shared_local_ctx();
        assert!(
            !Arc::ptr_eq(&before, &assigned),
            "an assignment must invalidate"
        );
        assert_eq!(assigned.get(x).map(|d| d.type_.clone()), Some(Expr::prop()));

        assert!(ctx.metas.pop_scope());
        let rolled_back = ctx.shared_local_ctx();
        assert!(
            !Arc::ptr_eq(&assigned, &rolled_back),
            "undoing the assignment must invalidate"
        );
        assert_eq!(
            rolled_back.get(x).map(|d| d.type_.clone()),
            Some(Expr::fvar(m_fvar))
        );

        // A fresh metavariable appears in the context.
        let m2 = ctx.metas.fresh(Expr::prop());
        let with_m2 = ctx.shared_local_ctx();
        assert!(with_m2.get(crate::unify::MetaState::to_fvar(m2)).is_some());
        let _ = FVarId::new(0);
    }

    #[test]
    fn test_shared_local_ctx_survives_restoring_a_cloned_meta_state() {
        // The clone-then-restore pattern the process-wide generation exists
        // for: after restoring the clone, the content is the clone's content
        // and the cache must either hit with that content or rebuild.
        let env = Environment::new();
        let mut ctx = ElabCtx::new(&env);
        let m = ctx.metas.fresh(Expr::type_());
        let x = ctx.push_local(
            clean_parser::SurfaceName::generated_path("x"),
            Expr::fvar(crate::unify::MetaState::to_fvar(m)),
        );
        let snapshot = ctx.metas.clone();
        let _ = ctx.shared_local_ctx();

        assert!(ctx.metas.assign(m, Expr::prop()));
        let assigned = ctx.shared_local_ctx();
        assert_eq!(assigned.get(x).map(|d| d.type_.clone()), Some(Expr::prop()));

        ctx.metas = snapshot;
        let restored = ctx.shared_local_ctx();
        assert_eq!(
            restored.get(x).map(|d| d.type_.clone()),
            Some(Expr::fvar(crate::unify::MetaState::to_fvar(m))),
            "the restored clone's content must be served, never the assigned timeline's"
        );
    }
}
