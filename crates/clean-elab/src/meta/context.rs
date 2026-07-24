// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! MetaCtx — core MetaM context for runtime metaprogramming operations.

use crate::instances::InstanceTable;
use crate::unify::{MetaState, Unifier, UnifyResult};
use clean_kernel::{Environment, Expr};

/// MetaM context for runtime metaprogramming operations
///
/// This provides a subset of Lean 4's MetaM functionality needed for
/// runtime q-pattern matching.
///
/// # Backtracking Support (Part of #383)
///
/// MetaCtx uses MetaState's undo trail for efficient backtracking during
/// speculative operations like tactic proof search. This replaces the
/// previous clone-based approach with O(1) scope management.
pub struct MetaCtx<'a> {
    /// The kernel environment for lookups
    pub(super) env: &'a Environment,
    /// Metavariable state for unification
    pub(super) metas: MetaState,
    /// Current transparency mode
    pub(super) transparency: clean_kernel::TransparencyMode,
    /// Optional instance table for synthInstanceQ
    pub(super) instances: Option<&'a InstanceTable>,
}

impl<'a> MetaCtx<'a> {
    /// Create a new MetaM context
    pub fn new(env: &'a Environment) -> Self {
        Self {
            env,
            metas: MetaState::new(),
            transparency: clean_kernel::TransparencyMode::Default,
            instances: None,
        }
    }

    /// Create a MetaM context with existing metavariable state
    pub fn with_metas(env: &'a Environment, metas: MetaState) -> Self {
        Self {
            env,
            metas,
            transparency: clean_kernel::TransparencyMode::Default,
            instances: None,
        }
    }

    /// Create a MetaM context with an instance table for type class resolution
    ///
    /// This enables `synth_instance_q` to perform actual instance lookups.
    pub fn with_instances(env: &'a Environment, instances: &'a InstanceTable) -> Self {
        Self {
            env,
            metas: MetaState::new(),
            transparency: clean_kernel::TransparencyMode::Default,
            instances: Some(instances),
        }
    }

    /// Create a MetaM context with both existing metavariable state and instance table
    pub fn with_metas_and_instances(
        env: &'a Environment,
        metas: MetaState,
        instances: &'a InstanceTable,
    ) -> Self {
        Self {
            env,
            metas,
            transparency: clean_kernel::TransparencyMode::Default,
            instances: Some(instances),
        }
    }

    /// Get the current metavariable state
    pub fn metas(&self) -> &MetaState {
        &self.metas
    }

    /// Get mutable access to metavariable state for unit tests.
    #[cfg(test)]
    pub(crate) fn metas_mut(&mut self) -> &mut MetaState {
        &mut self.metas
    }

    /// Take ownership of the metavariable state
    pub fn into_metas(self) -> MetaState {
        self.metas
    }

    /// Check if two expressions are definitionally equal
    ///
    /// This is the core operation for runtime q-pattern matching.
    /// Returns true if the expressions unify, false otherwise.
    ///
    /// Unlike elaboration-time matching, this preserves metavariable state
    /// only on success. On failure, all changes are rolled back.
    ///
    /// # Implementation Note (Part of #383)
    ///
    /// Uses the undo trail for efficient rollback instead of cloning the
    /// entire MetaState. On success, changes are committed. On failure,
    /// changes are undone via `pop_scope()`.
    pub fn is_def_eq(&mut self, e1: &Expr, e2: &Expr) -> bool {
        use clean_kernel::LocalContext;

        self.metas.push_scope();

        let ctx = LocalContext::new();
        let unify_result = {
            let mut unifier = Unifier::with_env(&mut self.metas, self.env, ctx);
            unifier.unify(e1, e2)
        };
        match unify_result {
            UnifyResult::Success => {
                self.metas.commit();
                true
            }
            UnifyResult::Failure(_) | UnifyResult::Stuck => {
                self.metas.pop_scope();
                false
            }
        }
    }

    /// Check if two expressions are definitionally equal, with rollback
    ///
    /// Like `is_def_eq`, but always rolls back metavariable state regardless
    /// of success or failure. Useful for checking without side effects.
    pub fn is_def_eq_pure(&mut self, e1: &Expr, e2: &Expr) -> bool {
        use clean_kernel::LocalContext;

        self.metas.push_scope();

        let ctx = LocalContext::new();
        let result = {
            let mut unifier = Unifier::with_env(&mut self.metas, self.env, ctx);
            matches!(unifier.unify(e1, e2), UnifyResult::Success)
        };

        self.metas.pop_scope();
        result
    }

    /// Run an operation with reducible transparency
    pub fn with_reducible<F, T>(&mut self, f: F) -> T
    where
        F: FnOnce(&mut Self) -> T,
    {
        let old_transparency = self.transparency;
        self.transparency = clean_kernel::TransparencyMode::Reducible;
        let result = f(self);
        self.transparency = old_transparency;
        result
    }

    /// Run an operation with a fresh metavariable context depth
    ///
    /// This isolates metavariable assignments made during the operation.
    pub fn with_new_mctx_depth<F, T>(&mut self, f: F) -> T
    where
        F: FnOnce(&mut Self) -> T,
    {
        self.metas.push_scope();
        let result = f(self);
        self.metas.pop_scope();
        result
    }

    /// Run an operation with a fresh metavariable context, keeping changes on success
    pub fn with_new_mctx_depth_keep_on_success<F, T>(&mut self, f: F) -> Option<T>
    where
        F: FnOnce(&mut Self) -> Option<T>,
    {
        self.metas.push_scope();

        match f(self) {
            Some(result) => {
                self.metas.commit();
                Some(result)
            }
            None => {
                self.metas.pop_scope();
                None
            }
        }
    }

    /// Instantiate all assigned metavariables in an expression
    pub fn instantiate_mvars(&self, e: &Expr) -> Expr {
        self.metas.instantiate(e)
    }

    /// Create a fresh metavariable with the given type
    pub fn fresh_meta(&mut self, ty: Expr) -> Expr {
        // MetaCtx has no local-context field: its runtime q-pattern metas are
        // deliberately closed.  Spell the empty scope explicitly so this
        // cannot recurse through this wrapper or inherit a later unifier
        // context.
        let id = self.metas.fresh_with_locals(ty, Vec::new());
        Expr::fvar(MetaState::to_fvar(id))
    }

    /// Get the environment reference
    pub fn env(&self) -> &Environment {
        self.env
    }

    /// Get current transparency mode
    pub fn transparency(&self) -> clean_kernel::TransparencyMode {
        self.transparency
    }
}
