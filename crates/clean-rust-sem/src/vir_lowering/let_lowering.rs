// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `let`-statement lowering helpers.

use super::context::FunctionLoweringContext;
use super::type_helpers::pattern_is_irrefutable;
use super::VirLoweringError;
use crate::expr::{Expr, Pattern};
use crate::ownership::Place;
use crate::types::{Mutability, RustType};
use crate::vir::Term;

impl<'a> FunctionLoweringContext<'a> {
    pub(super) fn lower_let_stmt(
        &mut self,
        pattern: &Pattern,
        ty: Option<&RustType>,
        init: Option<&Expr>,
        else_block: Option<&Expr>,
    ) -> Result<(), VirLoweringError> {
        let Some(init) = init else {
            let binding_ty = ty.cloned().ok_or_else(|| VirLoweringError::MissingType {
                context: format!(
                    "binding pattern in `{}` without annotation or initializer",
                    self.function_name
                ),
            })?;
            return match pattern {
                Pattern::Binding {
                    name,
                    mutable,
                    subpattern: None,
                } => {
                    self.declare_binding(
                        name,
                        binding_ty,
                        if *mutable {
                            Mutability::Mutable
                        } else {
                            Mutability::Shared
                        },
                    )?;
                    Ok(())
                }
                Pattern::Wildcard => Ok(()),
                other => Err(VirLoweringError::Unsupported {
                    context: "pattern",
                    detail: format!("unsupported lowering pattern `{other:?}` without initializer"),
                }),
            };
        };

        let init_ty = match ty {
            Some(ty) => ty.clone(),
            None => self.infer_expr_type(init)?,
        };

        // Fast path: simple binding — lower init directly into the declared
        // local, avoiding an intermediate temp that breaks NLL borrow tracking
        // and makes the named local unreachable as a direct rvalue destination.
        if let Pattern::Binding {
            name,
            mutable,
            subpattern: None,
        } = pattern
        {
            if else_block.is_none() {
                let mutability = if *mutable {
                    Mutability::Mutable
                } else {
                    Mutability::Shared
                };
                let future_output_ty = self.future_output_type_of_expr(init);
                let callable_future_output_ty = self.callable_future_output_type_of_expr(init);
                let local = self.declare_binding(name, init_ty, mutability)?;
                self.lower_expr_into(
                    Place::Local(local),
                    init,
                    matches!(init, Expr::Block { .. }),
                )?;
                if let Some(output_ty) = future_output_ty {
                    self.remember_future_output(local, output_ty);
                }
                if let Some(output_ty) = callable_future_output_ty {
                    self.remember_callable_future_output(local, output_ty);
                }
                return Ok(());
            }
        }

        // For compound patterns, reuse the source local directly when the init
        // is a plain variable reference so field projections root on the
        // original binding instead of an anonymous temp.
        let (init_place, temp_local) = if let Expr::Var { name, .. } = init {
            let source = self.lookup_local(name)?;
            (Place::Local(source), None)
        } else {
            let init_local = self.alloc_local(None, init_ty, Mutability::Mutable);
            self.lower_expr_into(
                Place::Local(init_local),
                init,
                matches!(init, Expr::Block { .. }),
            )?;
            if self.terminated {
                return Ok(());
            }
            (Place::Local(init_local), Some(init_local))
        };

        match else_block {
            Some(else_expr) if !pattern_is_irrefutable(pattern) => {
                let success_block = self.new_block(Term::Unreachable);
                let failure_block = self.new_block(Term::Unreachable);
                self.lower_pattern_test(init_place.clone(), pattern, success_block, failure_block)?;

                self.switch_to_block(failure_block);
                let else_ty = match self.infer_expr_type(else_expr)? {
                    RustType::Never => RustType::Unit,
                    ty => ty,
                };
                let else_temp = self.alloc_local(None, else_ty, Mutability::Mutable);
                self.lower_expr_into(
                    Place::Local(else_temp),
                    else_expr,
                    matches!(else_expr, Expr::Block { .. }),
                )?;
                if !self.terminated {
                    return Err(VirLoweringError::Unsupported {
                        context: "let-else",
                        detail: "let-else block must diverge (return, break, continue, or panic)"
                            .to_string(),
                    });
                }

                self.switch_to_block(success_block);
                self.bind_pattern(init_place.clone(), pattern)?;
                if let Some(temp) = temp_local {
                    self.emit_drop_and_storage_dead(temp);
                }
                Ok(())
            }
            Some(_) | None if !pattern_is_irrefutable(pattern) => {
                Err(VirLoweringError::Unsupported {
                    context: "let binding",
                    detail: format!("refutable pattern `{pattern:?}` requires let-else lowering"),
                })
            }
            _ => {
                self.bind_pattern(init_place.clone(), pattern)?;
                if let Some(temp) = temp_local {
                    self.emit_drop_and_storage_dead(temp);
                }
                Ok(())
            }
        }
    }
}
