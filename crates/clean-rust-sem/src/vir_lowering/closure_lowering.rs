// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Closure expression lowering to VIR.
//!
//! Lowers `Expr::Closure` into:
//! - A separate `Body` for the closure code (registered in `LoweredProgram`)
//! - An `Rvalue::Aggregate { kind: AggregateKind::Closure { def_id }, operands }`
//!   at the closure expression site, packing captured variables.
//!
//! ## Closure representation
//!
//! In MIR, a closure is an anonymous struct holding captures, with a separate
//! function body. We follow this model:
//!
//! - The closure body function parameters are `[captures..., explicit_params...]`
//! - Borrow closures capture by reference (`&T` or `&mut T`)
//! - Move closures capture by value
//! - The aggregate operands at the construction site match the capture layout

use super::context::FunctionLoweringContext;
use super::VirLoweringError;
use crate::expr::Expr;
use crate::ownership::Place;
use crate::types::{Lifetime, Mutability, RustType};
use crate::vir::{
    AggregateKind, BorrowKind, MutBorrowKind, Operand, RetagKind, Rvalue, Stmt as VirStmt,
};

impl<'a> FunctionLoweringContext<'a> {
    pub(super) fn lower_closure_expr(
        &mut self,
        destination: Place,
        params: &[(String, RustType)],
        body: &Expr,
        captures: &[(String, Mutability)],
        capture_by_value: bool,
    ) -> Result<(), VirLoweringError> {
        let closure_id = self.next_closure_id();
        let def_id = format!("{}::{{closure#{closure_id}}}", self.function_name);
        let destination_local = match &destination {
            Place::Local(local) => Some(*local),
            _ => None,
        };

        // Build capture operands at the construction site.
        // For borrow closures: emit Ref for each capture.
        // For move closures: emit Move for each capture.
        let mut capture_operands = Vec::with_capacity(captures.len());
        let mut capture_types = Vec::with_capacity(captures.len());

        for (name, mutability) in captures {
            // Source-side capture collection intentionally over-approximates and
            // can report names that are actually introduced inside the closure
            // body (for example match-pattern bindings or block-local lets).
            // Skip names that do not
            // resolve in the enclosing scope, matching type inference.
            let Ok(local) = self.lookup_local(name) else {
                continue;
            };
            let Ok(local_ty) = self.local_ty(local) else {
                continue;
            };

            if capture_by_value {
                // Move closure: capture by value
                let operand = if local_ty.is_copy() {
                    Operand::Copy(Place::Local(local))
                } else {
                    Operand::Move(Place::Local(local))
                };
                capture_operands.push(operand);
                capture_types.push((name.clone(), local_ty, *mutability));
            } else {
                // Borrow closure: capture by reference
                let borrow_kind = match mutability {
                    Mutability::Shared => BorrowKind::Shared,
                    Mutability::Mutable => BorrowKind::Mut {
                        kind: MutBorrowKind::ClosureCapture,
                    },
                };
                let ref_ty = RustType::Reference {
                    lifetime: Lifetime::Anonymous(0),
                    mutability: *mutability,
                    inner: Box::new(local_ty.clone()),
                };
                let ref_local = self.alloc_local(None, ref_ty.clone(), Mutability::Shared);
                self.emit_ref_and_retag(
                    Place::Local(ref_local),
                    borrow_kind,
                    Place::Local(local),
                    RetagKind::Default,
                );
                capture_operands.push(Operand::Move(Place::Local(ref_local)));
                capture_types.push((name.clone(), local_ty, *mutability));
            }
        }

        // Build the closure body function's parameter list.
        // Captures use their original value types so that `Expr::Var { name }`
        // in the closure body resolves to the same type the enclosing scope sees.
        // The borrow-vs-move distinction is captured in the aggregate operands
        // at the construction site, not in the body's parameter signature.
        let mut body_params: Vec<(String, RustType)> = capture_types
            .iter()
            .map(|(name, local_ty, _)| (name.clone(), local_ty.clone()))
            .collect();
        body_params.extend_from_slice(params);

        // Infer return type from the closure body.
        // Push a temporary scope with the closure's params so that
        // infer_expr_type can resolve variables like `x` that only
        // exist inside the closure.
        let ret_ty = self.infer_closure_body_type(&body_params, body)?;
        let visible_symbols = self.visible_symbols();

        // Lower the closure body as a separate function.
        // Use lower_function_with_closures to capture any nested closures.
        let (closure_body, nested_closures) = super::context::lower_function_with_closures(
            &def_id,
            &body_params,
            &ret_ty,
            body,
            &visible_symbols,
        )?;
        self.closure_bodies.push((def_id.clone(), closure_body));
        self.closure_bodies.extend(nested_closures);

        // Emit the closure aggregate at the construction site.
        self.emit(VirStmt::Assign {
            place: destination,
            rvalue: Rvalue::Aggregate {
                kind: AggregateKind::Closure {
                    def_id: def_id.clone(),
                },
                operands: capture_operands,
            },
        });
        if let Some(local) = destination_local {
            self.closure_def_ids.insert(local, def_id);
            // For async closures (body = Expr::Async { body: inner, .. }),
            // future_output_type_of_expr calls infer_expr_type(inner) but inner
            // references closure parameters that are not in the outer scope.
            // Use infer_closure_body_type which pushes a temporary scope with the
            // closure's full parameter list so param names resolve correctly.
            let async_output = match body {
                Expr::Async {
                    body: inner_body, ..
                } => self.infer_closure_body_type(&body_params, inner_body).ok(),
                _ => self.future_output_type_of_expr(body),
            };
            if let Some(output_ty) = async_output {
                self.remember_callable_future_output(local, output_ty);
            }
        }

        Ok(())
    }
}
