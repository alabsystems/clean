// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Expression lowering helpers for calls, aggregates, and range construction.

use super::context::FunctionLoweringContext;
use super::type_helpers::{autoderef_place_to_expected_inner, nominal_type_name};
use super::VirLoweringError;
use crate::expr::Expr;
use crate::ownership::Place;
use crate::types::{Mutability, ReceiverMode, RustType};
use crate::vir::{
    AggregateKind, BorrowKind, Constant, MutBorrowKind, Operand, RetagKind, Rvalue,
    Stmt as VirStmt, Term,
};

/// Return the `Fn` / `FnMut` / `FnOnce` trait name when `ty` is a callable
/// trait object — either bare (`dyn Fn`) or behind a `&`/`&mut`/`Box`/`Pin`
/// wrapper (`&dyn Fn`, `Box<dyn FnMut>`, ...). Returns `None` for any other
/// type, including non-callable trait objects such as `dyn Display`.
pub(super) fn dyn_fn_trait_name(ty: &RustType) -> Option<&str> {
    match ty {
        RustType::DynTrait { trait_name, .. }
            if matches!(trait_name.as_str(), "Fn" | "FnMut" | "FnOnce") =>
        {
            Some(trait_name.as_str())
        }
        RustType::Reference { inner, .. } | RustType::Box { inner } | RustType::Pin { inner } => {
            dyn_fn_trait_name(inner)
        }
        _ => None,
    }
}

/// Return the trait name when `ty` is a `dyn Trait` trait object — either bare
/// (`dyn Greeter`) or behind a `&`/`&mut`/`Box`/`Pin` wrapper. Excludes the
/// callable `Fn`/`FnMut`/`FnOnce` traits, which are dispatched through the
/// dedicated `dyn Fn` call path rather than method-call dynamic dispatch.
pub(super) fn dyn_trait_object_name(ty: &RustType) -> Option<&str> {
    match ty {
        RustType::DynTrait { trait_name, .. }
            if !matches!(trait_name.as_str(), "Fn" | "FnMut" | "FnOnce") =>
        {
            Some(trait_name.as_str())
        }
        RustType::Reference { inner, .. } | RustType::Box { inner } | RustType::Pin { inner } => {
            dyn_trait_object_name(inner)
        }
        _ => None,
    }
}

impl<'a> FunctionLoweringContext<'a> {
    pub(super) fn lower_call_expr(
        &mut self,
        destination: Place,
        func_expr: &Expr,
        args: &[Expr],
    ) -> Result<(), VirLoweringError> {
        // Standard-library constructor intrinsics (`Vec::new`, `String::new`, ...)
        // are not user-declared functions, so they have no `FnSig` and would
        // otherwise surface as `UnknownLocal`. Lower them structurally into the
        // destination so ownership/move analysis sees a properly initialized
        // local instead of an opaque call edge.
        if let Expr::Var { name, .. } = func_expr {
            if self.lookup_local(name).is_err() && self.fn_type(name).is_none() {
                if let Some(result) =
                    self.try_lower_builtin_constructor_call(&destination, name, args)
                {
                    return result;
                }
            }
        }

        let destination_local = match &destination {
            Place::Local(local) => Some(*local),
            _ => None,
        };
        let future_output_ty = self.callable_future_output_type_of_expr(func_expr);
        let callable_ty = self.infer_expr_type(func_expr)?;

        // A `dyn Fn` / `dyn FnMut` / `dyn FnOnce` trait object (behind a
        // reference, `Box`, or bare) is callable, but the surface `dyn Fn(A) -> R`
        // parenthesized signature is erased to a bare `DynTrait { trait_name }`,
        // so the parameter types cannot be recovered from the callee type. Lower
        // such calls through the materialized fat-pointer operand and materialize
        // each argument at its own inferred type (no callee-driven coercion).
        if dyn_fn_trait_name(&callable_ty).is_some() {
            let func_operand = self.materialize_operand(func_expr)?;
            let arg_operands = self.materialize_operands_as(args.iter().map(|arg| (arg, None)))?;
            if self.terminated {
                return Ok(());
            }
            let cont_block = self.new_block(Term::Unreachable);
            let unwind = self.call_unwind_action(&destination);
            self.current_block_mut().terminator = Term::Call {
                func: func_operand,
                args: arg_operands,
                destination,
                target: Some(cont_block),
                target_args: vec![],
                unwind,
            };
            self.switch_to_block(cont_block);
            if let (Some(local), Some(output_ty)) = (destination_local, future_output_ty) {
                self.remember_future_output(local, output_ty);
            }
            return Ok(());
        }

        let (param_tys, func_operand) = match callable_ty {
            RustType::Function { params, .. } | RustType::Closure { params, .. } => {
                (params, self.materialize_operand(func_expr)?)
            }
            other => {
                return Err(VirLoweringError::Unsupported {
                    context: "call",
                    detail: format!("callee `{func_expr:?}` is not callable: `{other:?}`"),
                });
            }
        };

        if args.len() != param_tys.len() {
            return Err(VirLoweringError::Unsupported {
                context: "call",
                detail: format!(
                    "callee `{func_expr:?}` expects {} args, got {}",
                    param_tys.len(),
                    args.len()
                ),
            });
        }

        let arg_operands = self.materialize_operands_as(
            args.iter()
                .zip(param_tys.iter())
                .map(|(arg, expected_ty)| (arg, Some(expected_ty))),
        )?;

        if self.terminated {
            return Ok(());
        }

        let cont_block = self.new_block(Term::Unreachable);
        let unwind = self.call_unwind_action(&destination);
        self.current_block_mut().terminator = Term::Call {
            func: func_operand,
            args: arg_operands,
            destination,
            target: Some(cont_block),
            target_args: vec![],
            unwind,
        };
        self.switch_to_block(cont_block);
        if let (Some(local), Some(output_ty)) = (destination_local, future_output_ty) {
            self.remember_future_output(local, output_ty);
        }
        Ok(())
    }

    /// Lower a recognized standard-library constructor intrinsic into the
    /// destination place. Returns `None` when `name` is not a known builtin
    /// constructor (so the caller falls through to ordinary call lowering).
    ///
    /// The semantic model represents `Vec<T>` uniformly as a growable buffer,
    /// so `Vec::new` and `Vec::with_capacity` both initialize the destination
    /// with an empty array aggregate (the capacity argument is a runtime hint
    /// and is lowered only for its evaluation effects). `String::new` produces
    /// an empty string literal, and `String::from`/`Box::new` are transparent
    /// over their single argument.
    fn try_lower_builtin_constructor_call(
        &mut self,
        destination: &Place,
        name: &str,
        args: &[Expr],
    ) -> Option<Result<(), VirLoweringError>> {
        match (name, args.len()) {
            ("Vec::new", 0) => Some(self.lower_empty_vec(destination)),
            ("Vec::with_capacity", 1) => {
                // Materialize the capacity argument for its evaluation effects,
                // then discard it: the verification model carries no capacity.
                if let Err(err) = self.materialize_operand(&args[0]) {
                    return Some(Err(err));
                }
                if self.terminated {
                    return Some(Ok(()));
                }
                Some(self.lower_empty_vec(destination))
            }
            ("String::new", 0) => Some(self.lower_empty_string(destination)),
            ("String::from", 1) | ("Box::new", 1) => {
                // Transparent over the single argument: lower it directly into
                // the destination so ownership of the inner value transfers.
                Some(self.lower_expr_into(
                    destination.clone(),
                    &args[0],
                    matches!(&args[0], Expr::Block { .. }),
                ))
            }
            _ => None,
        }
    }

    /// Emit an empty-array aggregate (`Vec`'s uniform model) into `destination`.
    fn lower_empty_vec(&mut self, destination: &Place) -> Result<(), VirLoweringError> {
        let element_ty = match self.place_type(destination)? {
            RustType::Vec { element } => *element,
            RustType::Array { element, .. } => *element,
            other => {
                return Err(VirLoweringError::Unsupported {
                    context: "Vec constructor",
                    detail: format!(
                        "destination `{destination:?}` for a Vec constructor is not a Vec: `{other:?}`"
                    ),
                });
            }
        };
        self.emit(VirStmt::Assign {
            place: destination.clone(),
            rvalue: Rvalue::Aggregate {
                kind: AggregateKind::Array(element_ty),
                operands: Vec::new(),
            },
        });
        Ok(())
    }

    /// Emit an empty string literal into `destination` (`String::new`).
    fn lower_empty_string(&mut self, destination: &Place) -> Result<(), VirLoweringError> {
        self.emit(VirStmt::Assign {
            place: destination.clone(),
            rvalue: Rvalue::Use(Operand::Constant(Constant::Str(String::new()))),
        });
        Ok(())
    }

    pub(super) fn lower_method_call_expr(
        &mut self,
        destination: Place,
        receiver_expr: &Expr,
        method: &str,
        args: &[Expr],
    ) -> Result<(), VirLoweringError> {
        let destination_local = match &destination {
            Place::Local(local) => Some(*local),
            _ => None,
        };
        let receiver_ty = self.infer_expr_type(receiver_expr)?;

        // Dynamic dispatch: a method call on a `dyn Trait` trait object (bare or
        // behind `&`/`&mut`/`Box`/`Pin`) erases the concrete implementing type,
        // so no inherent/impl signature is reachable via `nominal_type_name`.
        // Resolve the method against the trait *declaration* and emit a virtual
        // call through the trait-object operand instead.
        if let Some(trait_name) = dyn_trait_object_name(&receiver_ty) {
            return self.lower_dyn_method_call_expr(
                destination,
                receiver_expr,
                trait_name,
                method,
                args,
            );
        }

        let type_name =
            nominal_type_name(&receiver_ty).ok_or_else(|| VirLoweringError::MissingType {
                context: format!(
                    "method receiver `{receiver_expr:?}` in `{}`",
                    self.function_name
                ),
            })?;
        let qualified_name = self.resolve_method_name(&type_name, method);
        let future_output_ty = self.fn_future_output_type(&qualified_name).cloned();

        let param_tys = self
            .symbols
            .fn_param_types(&qualified_name)
            .ok_or_else(|| VirLoweringError::MissingType {
                context: format!(
                    "method signature for `{qualified_name}` in `{}`",
                    self.function_name
                ),
            })?;
        let first_param_ty = param_tys.first().cloned();
        let receiver_operand = self.lower_receiver(receiver_expr, &first_param_ty)?;

        if args.len() + 1 != param_tys.len() {
            return Err(VirLoweringError::Unsupported {
                context: "method call",
                detail: format!(
                    "method `{qualified_name}` expects {} explicit args, got {}",
                    param_tys.len().saturating_sub(1),
                    args.len()
                ),
            });
        }

        let arg_operands = self.materialize_operands_as(
            args.iter()
                .zip(param_tys.iter().skip(1))
                .map(|(arg, expected_ty)| (arg, Some(expected_ty))),
        )?;

        if self.terminated {
            return Ok(());
        }

        let mut all_args = vec![receiver_operand];
        all_args.extend(arg_operands);

        let func_operand = Operand::Constant(Constant::FnDef {
            name: qualified_name,
            substs: vec![],
        });

        let cont_block = self.new_block(Term::Unreachable);
        let unwind = self.call_unwind_action(&destination);
        self.current_block_mut().terminator = Term::Call {
            func: func_operand,
            args: all_args,
            destination,
            target: Some(cont_block),
            target_args: vec![],
            unwind,
        };
        self.switch_to_block(cont_block);
        if let (Some(local), Some(output_ty)) = (destination_local, future_output_ty) {
            self.remember_future_output(local, output_ty);
        }
        Ok(())
    }

    /// Lower a method call dispatched dynamically through a `dyn Trait` trait
    /// object (`obj.method(args)` where `obj: &dyn Trait`, `Box<dyn Trait>`, …).
    ///
    /// The concrete implementing type is erased, so the method signature is
    /// recovered from the trait *declaration* and the call is emitted as a
    /// virtual call against a synthetic `<dyn Trait>::method` callee with no
    /// registered body. This is a sound over-approximation: the borrow/move
    /// analysis treats the call as consuming its operands (the trait-object
    /// receiver and each argument) and havocing the destination, so no stale
    /// value or borrow survives the dispatch. It is intentionally incomplete —
    /// the concrete impl body is never inlined — but never unsound.
    fn lower_dyn_method_call_expr(
        &mut self,
        destination: Place,
        receiver_expr: &Expr,
        trait_name: &str,
        method: &str,
        args: &[Expr],
    ) -> Result<(), VirLoweringError> {
        let destination_local = match &destination {
            Place::Local(local) => Some(*local),
            _ => None,
        };

        let sig = self
            .symbols
            .trait_method_sig(trait_name, method)
            .ok_or_else(|| VirLoweringError::MissingType {
                context: format!(
                    "trait method `{trait_name}::{method}` for dynamic dispatch in `{}`",
                    self.function_name
                ),
            })?;
        let receiver_mode = sig.receiver;
        let param_tys = sig.params.clone();
        let future_output_ty = sig.future_output.clone();

        if args.len() != param_tys.len() {
            return Err(VirLoweringError::Unsupported {
                context: "dynamic method call",
                detail: format!(
                    "trait method `{trait_name}::{method}` expects {} explicit args, got {}",
                    param_tys.len(),
                    args.len()
                ),
            });
        }

        if !receiver_mode.has_self_receiver() {
            return Err(VirLoweringError::Unsupported {
                context: "dynamic method call",
                detail: format!(
                    "trait method `{trait_name}::{method}` has no `self` receiver and is not object-safe for `dyn` dispatch"
                ),
            });
        }

        // The trait-object value itself (the fat pointer carrying the vtable) is
        // the receiver operand. Materializing it reads the place and, for a
        // non-`Copy` trait-object value, moves it — an over-approximation that
        // keeps the analysis sound regardless of the declared receiver mode.
        let receiver_operand = self.materialize_operand(receiver_expr)?;
        if self.terminated {
            return Ok(());
        }

        let arg_operands = self.materialize_operands_as(
            args.iter()
                .zip(param_tys.iter())
                .map(|(arg, expected_ty)| (arg, Some(expected_ty))),
        )?;
        if self.terminated {
            return Ok(());
        }

        let mut all_args = vec![receiver_operand];
        all_args.extend(arg_operands);

        // Synthetic virtual-dispatch callee. No body is registered under this
        // name, so it is treated as an opaque external call by the analysis.
        let func_operand = Operand::Constant(Constant::FnDef {
            name: format!("<dyn {trait_name}>::{method}"),
            substs: vec![],
        });

        let cont_block = self.new_block(Term::Unreachable);
        let unwind = self.call_unwind_action(&destination);
        self.current_block_mut().terminator = Term::Call {
            func: func_operand,
            args: all_args,
            destination,
            target: Some(cont_block),
            target_args: vec![],
            unwind,
        };
        self.switch_to_block(cont_block);
        if let (Some(local), Some(output_ty)) = (destination_local, future_output_ty) {
            self.remember_future_output(local, output_ty);
        }
        Ok(())
    }

    fn lower_receiver(
        &mut self,
        receiver_expr: &Expr,
        first_param_ty: &Option<RustType>,
    ) -> Result<Operand, VirLoweringError> {
        match first_param_ty {
            Some(
                param_ty @ RustType::Reference {
                    mutability: Mutability::Shared,
                    inner,
                    ..
                },
            ) => {
                let place = autoderef_place_to_expected_inner(self, receiver_expr, inner)?;
                let temp = self.alloc_local(None, param_ty.clone(), Mutability::Shared);
                self.emit_ref_and_retag(
                    Place::Local(temp),
                    BorrowKind::Shared,
                    place,
                    RetagKind::Default,
                );
                Ok(Operand::Move(Place::Local(temp)))
            }
            Some(
                param_ty @ RustType::Reference {
                    mutability: Mutability::Mutable,
                    inner,
                    ..
                },
            ) => {
                let place = autoderef_place_to_expected_inner(self, receiver_expr, inner)?;
                let temp = self.alloc_local(None, param_ty.clone(), Mutability::Mutable);
                self.emit_ref_and_retag(
                    Place::Local(temp),
                    BorrowKind::Mut {
                        kind: MutBorrowKind::TwoPhaseBorrow,
                    },
                    place,
                    RetagKind::TwoPhase,
                );
                Ok(Operand::Move(Place::Local(temp)))
            }
            _ => self.materialize_operand(receiver_expr),
        }
    }

    pub(super) fn lower_tuple_expr(
        &mut self,
        destination: Place,
        elements: &[Expr],
    ) -> Result<(), VirLoweringError> {
        let field_tys = match self.place_type(&destination)? {
            RustType::Tuple(field_tys) if field_tys.len() == elements.len() => field_tys,
            RustType::Tuple(field_tys) => {
                return Err(VirLoweringError::Unsupported {
                    context: "tuple expression",
                    detail: format!(
                        "tuple arity mismatch: destination expects {}, expression has {}",
                        field_tys.len(),
                        elements.len()
                    ),
                });
            }
            other => {
                return Err(VirLoweringError::MissingType {
                    context: format!(
                        "tuple destination `{destination:?}` expected a tuple, got `{other:?}` in `{}`",
                        self.function_name
                    ),
                });
            }
        };

        let operands = self.materialize_operands_as(
            elements
                .iter()
                .zip(field_tys.iter())
                .map(|(element, expected_ty)| (element, Some(expected_ty))),
        )?;
        if self.terminated {
            return Ok(());
        }

        self.emit(VirStmt::Assign {
            place: destination,
            rvalue: Rvalue::Aggregate {
                kind: AggregateKind::Tuple,
                operands,
            },
        });
        Ok(())
    }

    pub(super) fn lower_array_expr(
        &mut self,
        destination: Place,
        elements: &[Expr],
    ) -> Result<(), VirLoweringError> {
        let element_ty = match self.place_type(&destination)? {
            RustType::Array { element, len }
                if len.as_usize(&std::collections::HashMap::new()) == Some(elements.len()) =>
            {
                *element
            }
            RustType::Array { len, .. } => {
                return Err(VirLoweringError::Unsupported {
                    context: "array expression",
                    detail: format!(
                        "array length mismatch: destination expects {:?}, expression has {}",
                        len,
                        elements.len()
                    ),
                });
            }
            other => {
                return Err(VirLoweringError::MissingType {
                    context: format!(
                        "array destination `{destination:?}` expected an array, got `{other:?}` in `{}`",
                        self.function_name
                    ),
                });
            }
        };

        let operands = self
            .materialize_operands_as(elements.iter().map(|element| (element, Some(&element_ty))))?;
        if self.terminated {
            return Ok(());
        }

        self.emit(VirStmt::Assign {
            place: destination,
            rvalue: Rvalue::Aggregate {
                kind: AggregateKind::Array(element_ty),
                operands,
            },
        });
        Ok(())
    }

    pub(super) fn lower_array_repeat_expr(
        &mut self,
        destination: Place,
        value: &Expr,
        count: usize,
    ) -> Result<(), VirLoweringError> {
        let element_ty = match self.place_type(&destination)? {
            RustType::Array { element, len }
                if len.as_usize(&std::collections::HashMap::new()) == Some(count) =>
            {
                *element
            }
            RustType::Array { len, .. } => {
                return Err(VirLoweringError::Unsupported {
                    context: "array repeat",
                    detail: format!(
                        "array repeat length mismatch: destination expects {:?}, expression has {count}",
                        len
                    ),
                });
            }
            other => {
                return Err(VirLoweringError::MissingType {
                    context: format!(
                        "array repeat destination `{destination:?}` expected an array, got `{other:?}` in `{}`",
                        self.function_name
                    ),
                });
            }
        };

        let mut operands = Vec::with_capacity(count);
        for _ in 0..count {
            if self.terminated {
                break;
            }
            operands.push(self.materialize_operand_as(value, Some(&element_ty))?);
        }
        if self.terminated {
            return Ok(());
        }

        self.emit(VirStmt::Assign {
            place: destination,
            rvalue: Rvalue::Aggregate {
                kind: AggregateKind::Array(element_ty),
                operands,
            },
        });
        Ok(())
    }

    pub(super) fn lower_struct_expr(
        &mut self,
        destination: Place,
        name: &str,
        fields: &[(String, Expr)],
    ) -> Result<(), VirLoweringError> {
        let mut operands = Vec::new();
        for (field_name, field_expr) in fields {
            if self.terminated {
                break;
            }
            let expected_ty = self.field_type(name, field_name).cloned();
            operands.push(self.materialize_operand_as(field_expr, expected_ty.as_ref())?);
        }
        if self.terminated {
            return Ok(());
        }
        self.emit(VirStmt::Assign {
            place: destination,
            rvalue: Rvalue::Aggregate {
                kind: AggregateKind::Adt {
                    name: name.to_string(),
                    variant_index: 0,
                },
                operands,
            },
        });
        Ok(())
    }

    /// Lower `UnionInit { name, field: (field_name, value) }` into an Adt aggregate
    /// with a single operand. Unions are represented the same as single-variant ADTs
    /// in MIR — `AggregateKind::Adt { name, variant_index: 0 }`.
    pub(super) fn lower_union_init_expr(
        &mut self,
        destination: Place,
        name: &str,
        field: &(String, Box<Expr>),
    ) -> Result<(), VirLoweringError> {
        let expected_ty = self.field_type(name, &field.0).cloned();
        let operand = self.materialize_operand_as(&field.1, expected_ty.as_ref())?;
        if self.terminated {
            return Ok(());
        }
        self.emit(VirStmt::Assign {
            place: destination,
            rvalue: Rvalue::Aggregate {
                kind: AggregateKind::Adt {
                    name: name.to_string(),
                    variant_index: 0,
                },
                operands: vec![operand],
            },
        });
        Ok(())
    }

    /// Lower `UnionFieldAccess { union_expr, field }` by projecting through the
    /// union place. In VIR, union field access uses the same `Place::Field`
    /// projection as struct access — the unsafe context is handled at a higher level.
    pub(super) fn lower_union_field_access_expr(
        &mut self,
        destination: Place,
        union_expr: &Expr,
        field: &str,
    ) -> Result<(), VirLoweringError> {
        let base_place = self.lower_place(union_expr)?;
        let field_place = Place::Field {
            base: Box::new(base_place),
            field: field.to_string(),
        };
        let operand = self.place_operand(field_place)?;
        self.emit(VirStmt::Assign {
            place: destination,
            rvalue: Rvalue::Use(operand),
        });
        Ok(())
    }

    pub(super) fn lower_range_expr(
        &mut self,
        destination: Place,
        start: Option<&Expr>,
        end: Option<&Expr>,
        inclusive: bool,
    ) -> Result<(), VirLoweringError> {
        let name = if start.is_some() && end.is_some() {
            if inclusive {
                "RangeInclusive"
            } else {
                "Range"
            }
        } else if start.is_some() {
            "RangeFrom"
        } else if end.is_some() {
            if inclusive {
                "RangeToInclusive"
            } else {
                "RangeTo"
            }
        } else {
            "RangeFull"
        };

        let mut operands = Vec::new();
        if let Some(s) = start {
            operands.push(self.materialize_operand(s)?);
        }
        if let Some(e) = end {
            operands.push(self.materialize_operand(e)?);
        }
        if self.terminated {
            return Ok(());
        }
        self.emit(VirStmt::Assign {
            place: destination,
            rvalue: Rvalue::Aggregate {
                kind: AggregateKind::Adt {
                    name: name.to_string(),
                    variant_index: 0,
                },
                operands,
            },
        });
        Ok(())
    }
}
