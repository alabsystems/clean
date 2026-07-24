// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Block, statement, and return lowering helpers.

use super::context::FunctionLoweringContext;
use super::VirLoweringError;
use crate::expr::{Expr, Stmt as SemStmt};
use crate::ownership::Place;
use crate::types::{Mutability, RustType};
use crate::vir::{Constant, Operand, Rvalue, Stmt as VirStmt, Term};

impl<'a> FunctionLoweringContext<'a> {
    pub(super) fn lower_stmt(&mut self, stmt: &SemStmt) -> Result<(), VirLoweringError> {
        match stmt {
            SemStmt::Let {
                pattern,
                ty,
                init,
                else_block,
            } => self.lower_let_stmt(pattern, ty.as_ref(), init.as_deref(), else_block.as_deref()),
            SemStmt::Expr(expr) => self.lower_expr_stmt(expr),
            SemStmt::Item(item) => self.register_and_lower_scoped_item(item),
        }
    }

    pub(super) fn lower_expr_stmt(&mut self, expr: &Expr) -> Result<(), VirLoweringError> {
        match expr {
            Expr::Return(_) => return self.lower_return(expr),
            Expr::Break { label, value } => {
                return self.lower_break_expr(label.as_deref(), value.as_deref());
            }
            Expr::Continue { label } => return self.lower_continue_expr(label.as_deref()),
            _ => {}
        }

        let temp_ty = self.infer_expr_type(expr)?;
        let temp = self.alloc_local(None, temp_ty, Mutability::Mutable);
        self.lower_expr_into(Place::Local(temp), expr, matches!(expr, Expr::Block { .. }))?;
        if !self.terminated {
            self.emit_drop_and_storage_dead(temp);
        }
        Ok(())
    }

    pub(super) fn lower_block_expr(
        &mut self,
        destination: Place,
        stmts: &[SemStmt],
        tail: Option<&Expr>,
        new_scope: bool,
    ) -> Result<(), VirLoweringError> {
        if new_scope {
            self.push_scope();
        }

        for stmt in stmts {
            self.lower_stmt(stmt)?;
            if self.terminated {
                break;
            }
        }

        if !self.terminated {
            if let Some(expr) = tail {
                self.lower_expr_into(
                    destination.clone(),
                    expr,
                    matches!(expr, Expr::Block { .. }),
                )?;
            } else {
                self.assign_unit(destination)?;
            }
        }

        if new_scope {
            self.pop_scope();
        }

        Ok(())
    }

    pub(super) fn lower_return(&mut self, expr: &Expr) -> Result<(), VirLoweringError> {
        let return_place = Place::Local(0);
        match expr {
            Expr::Return(Some(value)) => {
                self.lower_expr_into(
                    return_place,
                    value,
                    matches!(value.as_ref(), Expr::Block { .. }),
                )?;
            }
            Expr::Return(None) => self.assign_unit(return_place)?,
            _ => {
                return Err(VirLoweringError::Unsupported {
                    context: "return",
                    detail: format!("expected return expression, got `{expr:?}`"),
                });
            }
        }
        if self.terminated {
            return Ok(());
        }
        self.emit_scope_cleanup(0);
        self.current_block_mut().terminator = Term::Return;
        self.terminated = true;
        Ok(())
    }

    pub(super) fn assign_unit(&mut self, destination: Place) -> Result<(), VirLoweringError> {
        let dest_ty = self.place_type(&destination)?;
        if dest_ty != RustType::Unit {
            return Err(VirLoweringError::MissingType {
                context: format!(
                    "unit result assigned into non-unit destination `{destination:?}` in `{}`",
                    self.function_name
                ),
            });
        }
        self.emit(VirStmt::Assign {
            place: destination,
            rvalue: Rvalue::Use(Operand::Constant(Constant::ZeroSized)),
        });
        Ok(())
    }
}
