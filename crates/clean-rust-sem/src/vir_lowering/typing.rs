// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Operand and place lowering for VIR.
//!
//! Converts semantic AST expressions to VIR operands and places.
//! Type inference lives in `type_inference.rs`.

use super::context::FunctionLoweringContext;
use super::ops::constant_from_value;
use super::type_helpers::{
    autoderef_projection_base, indexed_element_type, nominal_type_name, projected_field_type,
    type_is_index, type_is_range,
};
use super::VirLoweringError;
use crate::expr::Expr;
use crate::ownership::Place;
use crate::types::{Mutability, RustType};
use crate::vir::{Constant, Operand, Rvalue, Stmt as VirStmt};

impl<'a> FunctionLoweringContext<'a> {
    pub(super) fn function_item_constant(&self, name: &str) -> Option<Constant> {
        if self.lookup_local(name).is_ok() {
            return None;
        }
        self.fn_type(name).map(|_| Constant::FnDef {
            name: name.to_string(),
            substs: vec![],
        })
    }

    pub(super) fn lower_place_like_expr_into(
        &mut self,
        destination: Place,
        expr: &Expr,
    ) -> Result<(), VirLoweringError> {
        let destination_local = match &destination {
            Place::Local(local) => Some(*local),
            _ => None,
        };
        let future_output_ty = self.future_output_type_of_expr(expr);
        let callable_future_output_ty = self.callable_future_output_type_of_expr(expr);
        let operand = self.lower_operand(expr)?;
        self.emit(VirStmt::Assign {
            place: destination,
            rvalue: Rvalue::Use(operand),
        });
        if let (Some(local), Some(output_ty)) = (destination_local, future_output_ty) {
            self.remember_future_output(local, output_ty);
        }
        if let (Some(local), Some(output_ty)) = (destination_local, callable_future_output_ty) {
            self.remember_callable_future_output(local, output_ty);
        }
        Ok(())
    }

    pub(super) fn lower_operand(&mut self, expr: &Expr) -> Result<Operand, VirLoweringError> {
        match expr {
            Expr::Literal(value) => Ok(Operand::Constant(constant_from_value(value)?)),
            Expr::Var { name, .. } => {
                if let Some(function_item) = self.function_item_constant(name) {
                    return Ok(Operand::Constant(function_item));
                }
                let place = self.lower_place(expr)?;
                self.place_operand(place)
            }
            Expr::Field { .. } | Expr::Index { .. } | Expr::Deref(_) | Expr::RawDeref(_) => {
                let place = self.lower_place(expr)?;
                self.place_operand(place)
            }
            // Complex expressions (BinOp, Call, etc.): materialize to a temporary
            // local, then return an operand referencing that temp. This mirrors
            // rustc MIR lowering where every non-trivial subexpression evaluates
            // into a temp before being used as an operand.
            other => {
                let ty = self.infer_expr_type(other)?;
                let temp = self.alloc_local(None, ty, Mutability::Mutable);
                self.lower_expr_into(
                    Place::Local(temp),
                    other,
                    matches!(other, Expr::Block { .. }),
                )?;
                if self.terminated {
                    return Err(VirLoweringError::Unsupported {
                        context: "operand",
                        detail: "expression diverged during operand materialization".to_string(),
                    });
                }
                self.place_operand(Place::Local(temp))
            }
        }
    }

    pub(super) fn lower_place(&mut self, expr: &Expr) -> Result<Place, VirLoweringError> {
        match expr {
            Expr::Var { name, .. } => Ok(Place::Local(self.lookup_local(name)?)),
            Expr::Field { base, field } => {
                let base_place = autoderef_projection_base(self, base)?;
                Ok(Place::Field {
                    base: Box::new(base_place),
                    field: field.clone(),
                })
            }
            Expr::Index { base, index } => {
                let base_place = autoderef_projection_base(self, base)?;

                let index_ty = self.infer_expr_type(index)?;

                // Range index → slicing (`a[1..3]`, `a[..]`, ...). A slice
                // borrows the *whole* container (the `Index::index` desugaring
                // takes `&self`), so the sound over-approximation is to model
                // the slice place as the entire base container. Any borrow of
                // `a[range]` then conflicts with every other access to `a`,
                // never under-reporting. The range bounds are still lowered for
                // their evaluation effects (side effects, sub-borrows).
                if type_is_range(&index_ty) {
                    if let Expr::Range { start, end, .. } = index.as_ref() {
                        for bound in [start.as_deref(), end.as_deref()].into_iter().flatten() {
                            self.materialize_operand(bound)?;
                            if self.terminated {
                                return Err(VirLoweringError::Unsupported {
                                    context: "slice place",
                                    detail:
                                        "range bound diverged before the sliced place could be used"
                                            .to_string(),
                                });
                            }
                        }
                    } else {
                        // A non-literal range value: lower it for its effects.
                        self.materialize_operand(index)?;
                        if self.terminated {
                            return Err(VirLoweringError::Unsupported {
                                context: "slice place",
                                detail:
                                    "range index diverged before the sliced place could be used"
                                        .to_string(),
                            });
                        }
                    }
                    return Ok(base_place);
                }

                if !type_is_index(&index_ty) {
                    return Err(VirLoweringError::Unsupported {
                        context: "index place",
                        detail: format!(
                            "index expression must be integer-like or a range, got `{index_ty:?}`"
                        ),
                    });
                }

                let index_local = self.alloc_local(None, index_ty, Mutability::Mutable);
                self.lower_expr_into(
                    Place::Local(index_local),
                    index,
                    matches!(index.as_ref(), Expr::Block { .. }),
                )?;
                if self.terminated {
                    return Err(VirLoweringError::Unsupported {
                        context: "index place",
                        detail: "index expression diverged before the indexed place could be used"
                            .to_string(),
                    });
                }

                Ok(Place::Index {
                    base: Box::new(base_place),
                    index: Box::new(Place::Local(index_local)),
                })
            }
            Expr::Deref(base) | Expr::RawDeref(base) => {
                Ok(Place::Deref(Box::new(self.lower_place_or_temp(base)?)))
            }
            other => Err(VirLoweringError::Unsupported {
                context: "place",
                detail: format!("unsupported place expression `{other:?}`"),
            }),
        }
    }

    pub(super) fn lower_place_or_temp(&mut self, expr: &Expr) -> Result<Place, VirLoweringError> {
        match self.lower_place(expr) {
            Ok(place) => Ok(place),
            Err(VirLoweringError::Unsupported {
                context: "place", ..
            }) => {
                let ty = self.infer_expr_type(expr)?;
                let temp = self.alloc_local(None, ty, Mutability::Mutable);
                self.lower_expr_into(Place::Local(temp), expr, matches!(expr, Expr::Block { .. }))?;
                if self.terminated {
                    return Err(VirLoweringError::Unsupported {
                        context: "place",
                        detail: "expression diverged before it could be materialized as a place"
                            .to_string(),
                    });
                }
                Ok(Place::Local(temp))
            }
            Err(err) => Err(err),
        }
    }

    pub(super) fn place_operand(&self, place: Place) -> Result<Operand, VirLoweringError> {
        let ty = self.place_type(&place)?;
        Ok(if ty.is_copy() {
            Operand::Copy(place)
        } else {
            Operand::Move(place)
        })
    }

    pub(super) fn place_type(&self, place: &Place) -> Result<RustType, VirLoweringError> {
        match place {
            Place::Local(local) => self.local_ty(*local),
            Place::Field { base, field } => {
                let base_ty = self.place_type(base)?;
                projected_field_type(self, &base_ty, field, &format!("{base:?}"))
            }
            Place::Index { base, .. } => {
                indexed_element_type(self.place_type(base)?).ok_or_else(|| {
                    VirLoweringError::Unsupported {
                        context: "index place",
                        detail: format!("cannot index into `{base:?}` in `{}`", self.function_name),
                    }
                })
            }
            Place::Deref(base) => match self.place_type(base)? {
                RustType::Reference { inner, .. }
                | RustType::RawPtr { inner, .. }
                | RustType::Box { inner }
                | RustType::Pin { inner } => Ok(*inner),
                other => Err(VirLoweringError::Unsupported {
                    context: "deref place",
                    detail: format!("cannot dereference `{other:?}`"),
                }),
            },
            Place::Downcast { base, variant } => {
                let base_ty = self.place_type(base)?;
                let enum_name =
                    nominal_type_name(&base_ty).ok_or_else(|| VirLoweringError::MissingType {
                        context: format!(
                            "downcast base `{base:?}` for variant `{variant}` in `{}`",
                            self.function_name
                        ),
                    })?;
                self.enum_variant_info_for_type(&base_ty, &enum_name, variant)
                    .map(|info| info.payload.payload_type())
                    .map_err(|_| VirLoweringError::MissingType {
                        context: format!(
                            "downcast variant `{enum_name}::{variant}` in `{}`",
                            self.function_name
                        ),
                    })
            }
            other => Err(VirLoweringError::Unsupported {
                context: "place type",
                detail: format!("type lookup for `{other:?}` is not implemented yet"),
            }),
        }
    }
}
