// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Control flow lowering: if-expressions, break, and continue.

mod loops;

use super::context::FunctionLoweringContext;
use super::VirLoweringError;
use crate::expr::Expr;
use crate::ownership::Place;
use crate::types::{Mutability, RustType};
use crate::vir::{Operand, SwitchTargets, Term};

impl<'a> FunctionLoweringContext<'a> {
    pub(crate) fn lower_if_expr(
        &mut self,
        destination: Place,
        condition: &Expr,
        then_branch: &Expr,
        else_branch: Option<&Expr>,
    ) -> Result<(), VirLoweringError> {
        // Evaluate the condition into a temporary bool local.
        let cond_local = self.alloc_local(None, RustType::Bool, Mutability::Mutable);
        self.lower_expr_into(Place::Local(cond_local), condition, false)?;
        if self.terminated {
            return Ok(());
        }

        // Create the then, else, and merge blocks.
        let then_block = self.new_block(Term::Unreachable);
        let else_block = self.new_block(Term::Unreachable);
        let merge_block = self.new_block(Term::Unreachable);

        // Set the current block's terminator to a SwitchInt on the condition.
        // true (1) → then_block, otherwise → else_block
        let mut targets = SwitchTargets::new(else_block);
        targets.add(1, then_block);
        self.current_block_mut().terminator = Term::SwitchInt {
            discriminant: Operand::Copy(Place::Local(cond_local)),
            targets,
        };

        // Lower the then branch.
        self.switch_to_block(then_block);
        self.lower_expr_into(destination.clone(), then_branch, true)?;
        let then_terminated = self.terminated;
        if !then_terminated {
            self.current_block_mut().terminator = Term::Goto {
                target: merge_block,
                args: vec![],
            };
        }

        // Lower the else branch.
        self.switch_to_block(else_block);
        if let Some(else_expr) = else_branch {
            self.lower_expr_into(destination, else_expr, true)?;
        } else {
            self.assign_unit(destination)?;
        }
        let else_terminated = self.terminated;
        if !else_terminated {
            self.current_block_mut().terminator = Term::Goto {
                target: merge_block,
                args: vec![],
            };
        }

        // If both branches terminated (e.g., both return), the merge block
        // is unreachable and we stay terminated.
        if then_terminated && else_terminated {
            self.terminated = true;
        } else {
            self.switch_to_block(merge_block);
        }

        Ok(())
    }

    pub(crate) fn lower_break_expr(
        &mut self,
        label: Option<&str>,
        value: Option<&Expr>,
    ) -> Result<(), VirLoweringError> {
        let target = self.loop_target(label, "break")?;
        if let Some(value) = value {
            self.lower_expr_into(
                target.break_destination.clone(),
                value,
                matches!(value, Expr::Block { .. }),
            )?;
        } else {
            self.assign_unit(target.break_destination.clone())?;
        }
        if self.terminated {
            return Ok(());
        }
        self.emit_scope_cleanup(target.scope_depth);
        self.current_block_mut().terminator = Term::Goto {
            target: target.break_block,
            args: vec![],
        };
        self.terminated = true;
        Ok(())
    }

    pub(crate) fn lower_continue_expr(
        &mut self,
        label: Option<&str>,
    ) -> Result<(), VirLoweringError> {
        let target = self.loop_target(label, "continue")?;
        self.emit_scope_cleanup(target.scope_depth);
        self.recycle_loop_temps(&target.continue_cleanup);
        self.recycle_maybe_initialized_loop_temps(&target.continue_maybe_cleanup);
        self.current_block_mut().terminator = Term::Goto {
            target: target.continue_block,
            args: vec![],
        };
        self.terminated = true;
        Ok(())
    }
}
