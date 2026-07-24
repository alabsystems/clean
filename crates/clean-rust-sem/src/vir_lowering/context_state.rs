// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! State bookkeeping helpers for VIR lowering context.

use super::context::{FunctionLoweringContext, Scope};
use super::loop_support::{CleanupLocal, MaybeInitializedLocal};
use super::VirLoweringError;
use crate::expr::Expr;
use crate::ownership::Place;
use crate::types::{Mutability, RustType};
use crate::vir::{
    BasicBlock, BasicBlockId, Constant, LocalDecl, LocalId, Operand, Rvalue, ScalarValue,
    Stmt as VirStmt, Term,
};

impl<'a> FunctionLoweringContext<'a> {
    pub(super) fn current_block_mut(&mut self) -> &mut BasicBlock {
        self.body
            .block_mut(self.current_block)
            .expect("invariant: current_block always references a valid block")
    }

    pub(super) fn current_block_id(&self) -> BasicBlockId {
        self.current_block
    }

    pub(super) fn new_block(&mut self, terminator: Term) -> BasicBlockId {
        let block = if self.building_cleanup_blocks {
            BasicBlock::cleanup(terminator)
        } else {
            BasicBlock::new(terminator)
        };
        self.body.add_block(block)
    }

    pub(super) fn switch_to_block(&mut self, block: BasicBlockId) {
        self.current_block = block;
        self.terminated = false;
    }

    pub(super) fn emit(&mut self, stmt: VirStmt) {
        if !self.terminated {
            self.current_block_mut().add_statement(stmt);
        }
    }

    pub(super) fn scope_depth(&self) -> usize {
        self.scopes.len()
    }

    pub(super) fn push_scope(&mut self) {
        self.scopes.push(Scope::default());
    }

    /// End the current iteration's value for a reusable loop temp, then
    /// immediately make the storage live again for the next iteration.
    pub(super) fn recycle_loop_temp(&mut self, local: LocalId) {
        if self.terminated {
            return;
        }
        self.emit_local_cleanup(local);
        self.emit(VirStmt::StorageLive(local));
    }

    pub(super) fn recycle_loop_temps(&mut self, locals: &[LocalId]) {
        for &local in locals {
            self.recycle_loop_temp(local);
        }
    }

    pub(super) fn recycle_tracked_loop_temp(&mut self, local: LocalId, init_flag: LocalId) {
        if self.terminated {
            return;
        }
        self.recycle_loop_temp(local);
        self.set_bool_local(init_flag, false);
    }

    pub(super) fn alloc_loop_init_flag(&mut self) -> LocalId {
        let local = self.alloc_local(None, RustType::Bool, Mutability::Mutable);
        self.set_bool_local(local, false);
        local
    }

    pub(super) fn lower_expr_into_tracked_loop_temp(
        &mut self,
        destination: LocalId,
        init_flag: LocalId,
        expr: &Expr,
        new_scope: bool,
    ) -> Result<(), VirLoweringError> {
        self.set_bool_local(init_flag, false);
        self.lower_expr_into(Place::Local(destination), expr, new_scope)?;
        if !self.terminated {
            self.set_bool_local(init_flag, true);
        }
        Ok(())
    }

    fn register_cleanup_local(&mut self, local: LocalId) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.cleanup.push(CleanupLocal::Plain(local));
        }
    }

    pub(super) fn track_maybe_initialized_local_cleanup(
        &mut self,
        local: LocalId,
        init_flag: LocalId,
    ) {
        self.retire_cleanup_local(local);
        self.retire_cleanup_local(init_flag);
        if let Some(scope) = self.scopes.last_mut() {
            scope
                .cleanup
                .push(CleanupLocal::MaybeInitialized(MaybeInitializedLocal {
                    local,
                    init_flag,
                }));
        }
    }

    pub(super) fn set_bool_local(&mut self, local: LocalId, value: bool) {
        self.emit(VirStmt::Assign {
            place: Place::Local(local),
            rvalue: Rvalue::Use(Operand::Constant(Constant::Scalar(ScalarValue::Bool(
                value,
            )))),
        });
    }

    pub(super) fn retire_cleanup_local(&mut self, local: LocalId) {
        for scope in self.scopes.iter_mut().rev() {
            if let Some(idx) = scope
                .cleanup
                .iter()
                .rposition(|tracked| tracked.tracks(local))
            {
                scope.cleanup.remove(idx);
                break;
            }
        }
    }

    pub(super) fn current_scope_mut(&mut self) -> Result<&mut Scope, VirLoweringError> {
        self.scopes
            .last_mut()
            .ok_or_else(|| VirLoweringError::Unsupported {
                context: "scope",
                detail: "lowering context lost its lexical root".to_string(),
            })
    }

    pub(super) fn current_scope_locals(&self) -> Vec<LocalId> {
        self.scopes
            .last()
            .map(|scope| scope.locals.clone())
            .unwrap_or_default()
    }

    pub(super) fn lookup_local(&self, name: &str) -> Result<LocalId, VirLoweringError> {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.bindings.get(name).copied())
            .ok_or_else(|| VirLoweringError::UnknownLocal {
                name: name.to_string(),
            })
    }

    pub(super) fn local_ty(&self, local: LocalId) -> Result<RustType, VirLoweringError> {
        self.body
            .local(local)
            .map(|decl| decl.ty.clone())
            .ok_or_else(|| VirLoweringError::MissingType {
                context: format!("local {local} in `{}`", self.function_name),
            })
    }

    pub(super) fn remember_future_output(&mut self, local: LocalId, output_ty: RustType) {
        self.future_output_tys.insert(local, output_ty);
    }

    pub(super) fn remember_callable_future_output(&mut self, local: LocalId, output_ty: RustType) {
        self.callable_future_output_tys.insert(local, output_ty);
    }

    pub(super) fn propagate_async_output_metadata(
        &mut self,
        source: &Place,
        destination_local: LocalId,
    ) {
        let Place::Local(source_local) = source else {
            return;
        };
        if let Some(output_ty) = self.future_output_tys.get(source_local).cloned() {
            self.remember_future_output(destination_local, output_ty);
        }
        if let Some(output_ty) = self.callable_future_output_tys.get(source_local).cloned() {
            self.remember_callable_future_output(destination_local, output_ty);
        }
    }

    pub(super) fn declare_binding(
        &mut self,
        name: &str,
        ty: RustType,
        mutability: Mutability,
    ) -> Result<LocalId, VirLoweringError> {
        let local = self.alloc_local(Some(name), ty, mutability);
        let scope = self.current_scope_mut()?;
        scope.bindings.insert(name.to_string(), local);
        scope.locals.push(local);
        scope.cleanup.push(CleanupLocal::Plain(local));
        Ok(local)
    }

    pub(super) fn alloc_local(
        &mut self,
        name: Option<&str>,
        ty: RustType,
        mutability: Mutability,
    ) -> LocalId {
        let decl = match name {
            Some(name) => LocalDecl::new(ty, mutability).with_name(name),
            None => LocalDecl::new(ty, mutability),
        };
        let local = self.body.add_local(decl);
        self.emit(VirStmt::StorageLive(local));
        if name.is_none() {
            self.register_cleanup_local(local);
        }
        local
    }

    pub(super) fn fork_for_type_inference(&self) -> Self {
        let mut fork = Self::new(self.function_name, &[], RustType::Unit, self.symbols);
        fork.body = self.body.clone();
        fork.scopes = self.scopes.clone();
        fork.closure_def_ids = self.closure_def_ids.clone();
        fork.generator_def_ids = self.generator_def_ids.clone();
        fork.future_output_tys = self.future_output_tys.clone();
        fork.callable_future_output_tys = self.callable_future_output_tys.clone();
        fork.loop_stack = self.loop_stack.clone();
        fork.terminated = self.terminated;
        fork.current_block = self.current_block;
        fork
    }
}
