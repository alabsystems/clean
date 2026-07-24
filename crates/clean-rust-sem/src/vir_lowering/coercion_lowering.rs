// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Operand materialization and coercion-aware lowering helpers.

use super::context::FunctionLoweringContext;
use super::ops::lower_cast_kind;
use super::VirLoweringError;
use crate::coercion::{try_coerce, CoercionKind};
use crate::expr::Expr;
use crate::ownership::Place;
use crate::types::{Mutability, RustType};
use crate::vir::{
    BorrowKind, Constant, MutBorrowKind, Operand, RetagKind, Rvalue, Stmt as VirStmt, Term,
};

impl<'a> FunctionLoweringContext<'a> {
    pub(super) fn materialize_operand(&mut self, expr: &Expr) -> Result<Operand, VirLoweringError> {
        match self.lower_operand(expr) {
            Ok(op) => return Ok(op),
            Err(err) if self.terminated => return Err(err),
            Err(_) => {}
        }
        let ty = self.infer_expr_type(expr)?;
        let is_copy = ty.is_copy();
        let temp = self.alloc_local(None, ty, Mutability::Mutable);
        self.lower_expr_into(Place::Local(temp), expr, matches!(expr, Expr::Block { .. }))?;
        Ok(if is_copy {
            Operand::Copy(Place::Local(temp))
        } else {
            Operand::Move(Place::Local(temp))
        })
    }

    pub(super) fn materialize_operand_as(
        &mut self,
        expr: &Expr,
        expected_ty: Option<&RustType>,
    ) -> Result<Operand, VirLoweringError> {
        let Some(expected_ty) = expected_ty else {
            return self.materialize_operand(expr);
        };

        let source_ty = self.infer_expr_type(expr)?;
        if source_ty == *expected_ty || source_ty.is_compatible(expected_ty) {
            return self.materialize_operand(expr);
        }

        // Never-typed expressions diverge — lower the diverging expr, then
        // return a dummy operand. Execution never reaches the use site.
        if matches!(source_ty, RustType::Never) {
            let temp = self.alloc_local(None, expected_ty.clone(), Mutability::Mutable);
            self.lower_expr_into(Place::Local(temp), expr, matches!(expr, Expr::Block { .. }))?;
            if !self.terminated {
                // `!`-typed calls still lower with a continuation block today; mark
                // that continuation unreachable so callers never consume the dummy temp.
                self.current_block_mut().terminator = Term::Unreachable;
                self.terminated = true;
            }
            return self.place_operand(Place::Local(temp));
        }

        if let Some(operand) =
            self.try_materialize_autoderef_reference_operand(expr, expected_ty)?
        {
            return Ok(operand);
        }
        let Some(kind) = try_coerce(&source_ty, expected_ty) else {
            return self.materialize_operand(expr);
        };

        let temp = self.alloc_local(None, expected_ty.clone(), Mutability::Mutable);
        self.lower_expr_with_coercion(Place::Local(temp), expr, &source_ty, expected_ty, &kind)?;
        if self.terminated {
            return self.place_operand(Place::Local(temp));
        }
        self.place_operand(Place::Local(temp))
    }

    pub(super) fn materialize_operands_as<'b, I>(
        &mut self,
        values: I,
    ) -> Result<Vec<Operand>, VirLoweringError>
    where
        I: IntoIterator<Item = (&'b Expr, Option<&'b RustType>)>,
    {
        let mut operands = Vec::new();
        for (expr, expected_ty) in values {
            if self.terminated {
                break;
            }
            operands.push(self.materialize_operand_as(expr, expected_ty)?);
        }
        Ok(operands)
    }

    pub(super) fn try_lower_coerced_expr(
        &mut self,
        destination: &Place,
        expr: &Expr,
    ) -> Result<bool, VirLoweringError> {
        let target_ty = self.place_type(destination)?;
        let source_ty = self.infer_expr_type(expr)?;
        if matches!(source_ty, RustType::Never)
            || source_ty == target_ty
            || source_ty.is_compatible(&target_ty)
        {
            return Ok(false);
        }
        if self.try_lower_autoderef_reference_expr(destination.clone(), expr, &target_ty)? {
            return Ok(true);
        }
        let Some(kind) = try_coerce(&source_ty, &target_ty) else {
            return Ok(false);
        };
        self.lower_expr_with_coercion(destination.clone(), expr, &source_ty, &target_ty, &kind)?;
        Ok(true)
    }

    fn lower_expr_with_coercion(
        &mut self,
        destination: Place,
        expr: &Expr,
        source_ty: &RustType,
        target_ty: &RustType,
        kind: &CoercionKind,
    ) -> Result<(), VirLoweringError> {
        let source_place = self.lower_place_or_temp(expr)?;
        if self.terminated {
            return Ok(());
        }
        self.emit_coercion_from_place(destination, source_place, source_ty, target_ty, kind)
    }

    fn emit_coercion_from_place(
        &mut self,
        destination: Place,
        source_place: Place,
        source_ty: &RustType,
        target_ty: &RustType,
        kind: &CoercionKind,
    ) -> Result<(), VirLoweringError> {
        match kind {
            CoercionKind::MutToSharedRef
            | CoercionKind::DerefCoercion { .. }
            | CoercionKind::UnsizeArrayToSlice => {
                let borrow_kind = match target_ty {
                    RustType::Reference {
                        mutability: Mutability::Shared,
                        ..
                    } => BorrowKind::Shared,
                    RustType::Reference {
                        mutability: Mutability::Mutable,
                        ..
                    } => BorrowKind::Mut {
                        kind: MutBorrowKind::Default,
                    },
                    _ => {
                        return Err(VirLoweringError::Unsupported {
                            context: "coercion",
                            detail: format!(
                                "reference coercion `{kind:?}` requires a reference target, got `{target_ty:?}`"
                            ),
                        });
                    }
                };
                let borrow_place = self.coercion_borrow_place(source_place, source_ty, target_ty);
                self.emit_ref_and_retag(destination, borrow_kind, borrow_place, RetagKind::Default);
                Ok(())
            }
            CoercionKind::RefToRawPtr => {
                let raw_mutability = match target_ty {
                    RustType::RawPtr { mutability, .. } => *mutability,
                    _ => Mutability::Shared,
                };
                let referent_place = self.referent_place(source_place, source_ty);
                self.emit(VirStmt::Assign {
                    place: destination.clone(),
                    rvalue: Rvalue::AddressOf {
                        mutability: raw_mutability,
                        place: referent_place,
                    },
                });
                self.emit(VirStmt::Retag {
                    kind: RetagKind::Raw(raw_mutability),
                    place: destination,
                });
                Ok(())
            }
            CoercionKind::UnsizeToDynTrait => {
                let operand = self.place_operand(source_place)?;
                self.emit(VirStmt::Assign {
                    place: destination.clone(),
                    rvalue: Rvalue::Cast {
                        kind: lower_cast_kind(source_ty, target_ty),
                        operand,
                        ty: target_ty.clone(),
                    },
                });
                if matches!(target_ty, RustType::Reference { .. }) {
                    self.emit(VirStmt::Retag {
                        kind: RetagKind::Default,
                        place: destination,
                    });
                }
                Ok(())
            }
            CoercionKind::MutPtrToConstPtr => {
                let operand = self.place_operand(source_place)?;
                self.emit(VirStmt::Assign {
                    place: destination,
                    rvalue: Rvalue::Cast {
                        kind: lower_cast_kind(source_ty, target_ty),
                        operand,
                        ty: target_ty.clone(),
                    },
                });
                Ok(())
            }
            CoercionKind::ClosureKindUpcast => {
                let operand = self.place_operand(source_place)?;
                self.emit(VirStmt::Assign {
                    place: destination,
                    rvalue: Rvalue::Use(operand),
                });
                Ok(())
            }
            CoercionKind::ClosureToFnPtr => {
                let Some(def_id) = self.closure_def_id_for_place(&source_place) else {
                    return Err(VirLoweringError::Unsupported {
                        context: "closure coercion",
                        detail: format!(
                            "closure source `{source_place:?}` has no registered lowered body for fn-pointer coercion"
                        ),
                    });
                };
                self.emit(VirStmt::Assign {
                    place: destination,
                    rvalue: Rvalue::Use(Operand::Constant(Constant::FnDef {
                        name: def_id,
                        substs: vec![],
                    })),
                });
                Ok(())
            }
            CoercionKind::Transitive(steps)
                if steps.iter().all(|step| {
                    matches!(
                        step,
                        CoercionKind::DerefCoercion { .. } | CoercionKind::UnsizeArrayToSlice
                    )
                }) =>
            {
                let borrow_kind = match target_ty {
                    RustType::Reference {
                        mutability: Mutability::Shared,
                        ..
                    } => BorrowKind::Shared,
                    RustType::Reference {
                        mutability: Mutability::Mutable,
                        ..
                    } => BorrowKind::Mut {
                        kind: MutBorrowKind::Default,
                    },
                    _ => {
                        return Err(VirLoweringError::Unsupported {
                            context: "coercion",
                            detail: format!(
                                "transitive reference coercion requires a reference target, got `{target_ty:?}`"
                            ),
                        });
                    }
                };
                let borrow_place = self.coercion_borrow_place(source_place, source_ty, target_ty);
                self.emit_ref_and_retag(destination, borrow_kind, borrow_place, RetagKind::Default);
                Ok(())
            }
            CoercionKind::NeverToAny => {
                // The source expression produced `!` (diverging). The source_place
                // was already lowered by `lower_place_or_temp`, which would have set
                // `self.terminated` if the expression actually diverged. If we reach
                // here, mark the block unreachable defensively.
                self.current_block_mut().terminator = Term::Unreachable;
                self.terminated = true;
                Ok(())
            }
            CoercionKind::Transitive(steps) => {
                // General transitive chain: lower each step sequentially through
                // intermediate temps. The pure-deref/unsize case is already handled
                // above; this arm catches mixed chains (e.g., deref + ptr weakening).
                let mut current_place = source_place;
                let mut current_ty = source_ty.clone();
                for (i, step) in steps.iter().enumerate() {
                    let step_target = if i + 1 < steps.len() {
                        self.intermediate_coercion_type(&current_ty, step)
                    } else {
                        target_ty.clone()
                    };
                    let step_dest = if i + 1 < steps.len() {
                        let temp = self.alloc_local(None, step_target.clone(), Mutability::Mutable);
                        Place::Local(temp)
                    } else {
                        destination.clone()
                    };
                    self.emit_coercion_from_place(
                        step_dest.clone(),
                        current_place,
                        &current_ty,
                        &step_target,
                        step,
                    )?;
                    if self.terminated {
                        return Ok(());
                    }
                    current_place = step_dest;
                    current_ty = step_target;
                }
                Ok(())
            }
        }
    }

    fn referent_place(&self, source_place: Place, source_ty: &RustType) -> Place {
        match source_ty {
            RustType::Reference { .. } => Place::Deref(Box::new(source_place)),
            _ => source_place,
        }
    }

    fn coercion_borrow_place(
        &self,
        source_place: Place,
        source_ty: &RustType,
        target_ty: &RustType,
    ) -> Place {
        match (source_ty, target_ty) {
            (
                RustType::Reference {
                    inner: source_inner,
                    ..
                },
                RustType::Reference {
                    inner: target_inner,
                    ..
                },
            ) => self.coercion_inner_place(
                Place::Deref(Box::new(source_place)),
                source_inner,
                target_inner,
            ),
            _ => source_place,
        }
    }

    fn coercion_inner_place(
        &self,
        place: Place,
        source_ty: &RustType,
        target_inner: &RustType,
    ) -> Place {
        if source_ty == target_inner || source_ty.is_compatible(target_inner) {
            return place;
        }
        match source_ty {
            RustType::Reference { inner, .. }
            | RustType::Box { inner }
            | RustType::Pin { inner } => {
                self.coercion_inner_place(Place::Deref(Box::new(place)), inner, target_inner)
            }
            _ => place,
        }
    }

    fn intermediate_coercion_type(&self, source: &RustType, step: &CoercionKind) -> RustType {
        match step {
            CoercionKind::MutToSharedRef => match source {
                RustType::Reference {
                    lifetime, inner, ..
                } => RustType::Reference {
                    lifetime: lifetime.clone(),
                    mutability: Mutability::Shared,
                    inner: inner.clone(),
                },
                _ => source.clone(),
            },
            CoercionKind::DerefCoercion { .. } => match source {
                RustType::Reference {
                    lifetime,
                    mutability,
                    inner,
                } => {
                    let deref_target = match inner.as_ref() {
                        RustType::Named { name, .. } if name == "String" => RustType::Str,
                        RustType::Vec { element } => RustType::Slice {
                            elem: element.clone(),
                        },
                        RustType::Box { inner } => inner.as_ref().clone(),
                        _ => inner.as_ref().clone(),
                    };
                    RustType::Reference {
                        lifetime: lifetime.clone(),
                        mutability: *mutability,
                        inner: Box::new(deref_target),
                    }
                }
                _ => source.clone(),
            },
            CoercionKind::UnsizeArrayToSlice => match source {
                RustType::Reference {
                    lifetime,
                    mutability,
                    inner,
                } => {
                    let slice_ty = match inner.as_ref() {
                        RustType::Array { element, .. } => RustType::Slice {
                            elem: element.clone(),
                        },
                        _ => inner.as_ref().clone(),
                    };
                    RustType::Reference {
                        lifetime: lifetime.clone(),
                        mutability: *mutability,
                        inner: Box::new(slice_ty),
                    }
                }
                _ => source.clone(),
            },
            CoercionKind::RefToRawPtr => match source {
                RustType::Reference {
                    mutability, inner, ..
                } => RustType::RawPtr {
                    mutability: *mutability,
                    inner: inner.clone(),
                },
                _ => source.clone(),
            },
            CoercionKind::MutPtrToConstPtr => match source {
                RustType::RawPtr { inner, .. } => RustType::RawPtr {
                    mutability: Mutability::Shared,
                    inner: inner.clone(),
                },
                _ => source.clone(),
            },
            _ => source.clone(),
        }
    }

    fn closure_def_id_for_place(&self, place: &Place) -> Option<String> {
        match place {
            Place::Local(local) => self.closure_def_ids.get(local).cloned(),
            _ => None,
        }
    }
}
