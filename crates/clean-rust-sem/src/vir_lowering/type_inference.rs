// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Expression type inference for VIR lowering.
//!
//! Structural type inference: walks the semantic AST to compute `RustType`
//! for VIR local declarations and operand materialization.

use super::calls::dyn_trait_object_name;
use super::context::FunctionLoweringContext;
use super::type_helpers::{
    indexed_element_type, nominal_type_name, projected_field_type, sliced_element_type,
    type_is_index, type_is_range,
};
use super::VirLoweringError;
use crate::expr::{Expr, Stmt as SemStmt};
use crate::types::{ClosureKind, Lifetime, Mutability, RustType};
use crate::values::{BinOp as ExprBinOp, UnOp as ExprUnOp};

impl<'a> FunctionLoweringContext<'a> {
    pub(super) fn infer_expr_type(&self, expr: &Expr) -> Result<RustType, VirLoweringError> {
        match expr {
            Expr::Literal(value) => Ok(value.get_type()),
            Expr::Var { name, .. } => self
                .lookup_local(name)
                .and_then(|local| self.local_ty(local))
                .or_else(|_| {
                    self.fn_type(name)
                        .ok_or_else(|| VirLoweringError::UnknownLocal { name: name.clone() })
                }),
            Expr::Field { base, field } => {
                let base_ty = self.infer_expr_type(base)?;
                projected_field_type(self, &base_ty, field, &format!("{base:?}"))
            }
            Expr::Index { base, index } => {
                let index_ty = self.infer_expr_type(index)?;
                let base_ty = self.infer_expr_type(base)?;
                // Range index → slicing: the result is a slice `[T]`, not a
                // single element `T`.
                if type_is_range(&index_ty) {
                    let elem = sliced_element_type(base_ty).ok_or_else(|| {
                        VirLoweringError::MissingType {
                            context: format!("slice base `{base:?}` in `{}`", self.function_name),
                        }
                    })?;
                    return Ok(RustType::Slice {
                        elem: Box::new(elem),
                    });
                }
                if !type_is_index(&index_ty) {
                    return Err(VirLoweringError::Unsupported {
                        context: "index expression",
                        detail: format!(
                            "index expression must be integer-like or a range, got `{index_ty:?}`"
                        ),
                    });
                }
                indexed_element_type(base_ty).ok_or_else(|| VirLoweringError::MissingType {
                    context: format!("index base `{base:?}` in `{}`", self.function_name),
                })
            }
            Expr::Deref(base) => match self.infer_expr_type(base)? {
                RustType::Reference { inner, .. }
                | RustType::RawPtr { inner, .. }
                | RustType::Box { inner }
                | RustType::Pin { inner } => Ok(*inner),
                other => Err(VirLoweringError::Unsupported {
                    context: "deref expression",
                    detail: format!("cannot dereference `{other:?}`"),
                }),
            },
            Expr::AddrOf { mutability, expr } => Ok(RustType::Reference {
                lifetime: Lifetime::Anonymous(0),
                mutability: *mutability,
                inner: Box::new(self.infer_expr_type(expr)?),
            }),
            Expr::Assign { .. } | Expr::AssignOp { .. } => Ok(RustType::Unit),
            Expr::Block { stmts, expr } => self.infer_block_expr_type(stmts, expr.as_deref()),
            Expr::Tuple(elements) => Ok(RustType::Tuple(
                elements
                    .iter()
                    .map(|element| self.infer_expr_type(element))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            Expr::Array(elements) => {
                let element_ty = match elements.first() {
                    Some(first) => self.infer_expr_type(first)?,
                    None => RustType::Unit,
                };
                for element in elements.iter().skip(1) {
                    let ty = self.infer_expr_type(element)?;
                    if !ty.is_compatible(&element_ty) {
                        return Err(VirLoweringError::Unsupported {
                            context: "array expression",
                            detail: format!(
                                "array elements must share a type, got `{element_ty:?}` and `{ty:?}`"
                            ),
                        });
                    }
                }
                Ok(RustType::Array {
                    element: Box::new(element_ty),
                    len: crate::types::ConstGenericArg::usize(elements.len()),
                })
            }
            Expr::ArrayRepeat { value, count } => Ok(RustType::Array {
                element: Box::new(self.infer_expr_type(value)?),
                len: crate::types::ConstGenericArg::usize(*count),
            }),
            Expr::Cast { target, .. } => Ok(target.clone()),
            Expr::Return(_) | Expr::Break { .. } | Expr::Continue { .. } | Expr::Panic { .. } => {
                Ok(RustType::Never)
            }
            Expr::Unsafe { block } => self.infer_expr_type(block),
            Expr::BinOp { op, left, .. } => match op {
                ExprBinOp::Eq
                | ExprBinOp::Ne
                | ExprBinOp::Lt
                | ExprBinOp::Le
                | ExprBinOp::Gt
                | ExprBinOp::Ge => Ok(RustType::Bool),
                _ => self.infer_expr_type(left),
            },
            Expr::UnOp { op, expr } => match op {
                ExprUnOp::Not => {
                    let inner = self.infer_expr_type(expr)?;
                    if inner == RustType::Bool {
                        Ok(RustType::Bool)
                    } else {
                        Ok(inner)
                    }
                }
                ExprUnOp::Neg => self.infer_expr_type(expr),
            },
            Expr::If {
                then_branch,
                else_branch,
                ..
            } => {
                if else_branch.is_some() {
                    self.infer_expr_type(then_branch)
                } else {
                    Ok(RustType::Unit)
                }
            }
            Expr::Match { scrutinee, arms } => self.infer_match_expr_type(scrutinee, arms),
            Expr::Loop { label, body } => {
                Ok(self.loop_result_type(body, label.as_deref(), RustType::Never))
            }
            Expr::While { label, body, .. } => {
                Ok(self.loop_result_type(body, label.as_deref(), RustType::Unit))
            }
            Expr::Struct { name, .. } => Ok(RustType::Named {
                name: name.clone(),
                type_args: Vec::new(),
                lifetime_args: Vec::new(),
                const_args: Vec::new(),
            }),
            Expr::EnumVariant {
                enum_name, variant, ..
            } => {
                if self.enum_variant(enum_name, variant).is_some() {
                    return Ok(RustType::Named {
                        name: enum_name.clone(),
                        type_args: Vec::new(),
                        lifetime_args: Vec::new(),
                        const_args: Vec::new(),
                    });
                }
                self.infer_builtin_enum_variant_type(enum_name, variant, expr)
            }
            Expr::Call { func, args, .. } => {
                if let Expr::Var { name, .. } = func.as_ref() {
                    if self.lookup_local(name).is_err() && self.fn_type(name).is_none() {
                        if let Some(ty) = self.builtin_constructor_result_type(name, args)? {
                            return Ok(ty);
                        }
                    }
                }
                let callee_ty = self.infer_expr_type(func)?;
                match callee_ty {
                    RustType::Function { ret, .. } | RustType::Closure { ret, .. } => Ok(*ret),
                    // A `dyn Fn(A) -> R` trait object's parenthesized signature is
                    // erased to a bare `DynTrait` at parse time, so the call's
                    // return type cannot be recovered from the callee type. The
                    // concrete result type is supplied by the destination place at
                    // the call site; report it as inferred here.
                    ref other if super::calls::dyn_fn_trait_name(other).is_some() => {
                        Ok(RustType::Infer)
                    }
                    other => Err(VirLoweringError::Unsupported {
                        context: "call expression",
                        detail: format!("callee `{func:?}` is not callable: `{other:?}`"),
                    }),
                }
            }
            Expr::MethodCall {
                receiver, method, ..
            } => {
                let receiver_ty = self.infer_expr_type(receiver)?;
                // Dynamic dispatch through a `dyn Trait` trait object: the
                // concrete impl is erased, so the return type comes from the
                // trait declaration's method signature.
                if let Some(trait_name) = dyn_trait_object_name(&receiver_ty) {
                    if let Some(sig) = self.symbols.trait_method_sig(trait_name, method) {
                        return Ok(sig.ret.clone());
                    }
                }
                if let Some(type_name) = nominal_type_name(&receiver_ty) {
                    let qualified = self.resolve_method_name(&type_name, method);
                    if let Some(ret) = self.fn_ret_type(&qualified) {
                        return Ok(ret.clone());
                    }
                }
                Err(VirLoweringError::MissingType {
                    context: format!("method call `.{method}()` in `{}`", self.function_name),
                })
            }
            Expr::Range {
                start,
                end,
                inclusive,
            } => {
                let elem_ty = if let Some(s) = start {
                    self.infer_expr_type(s)?
                } else if let Some(e) = end {
                    self.infer_expr_type(e)?
                } else {
                    RustType::Unit
                };
                let name = if *inclusive {
                    "RangeInclusive"
                } else if start.is_some() && end.is_some() {
                    "Range"
                } else if start.is_some() {
                    "RangeFrom"
                } else if end.is_some() {
                    "RangeTo"
                } else {
                    "RangeFull"
                };
                Ok(RustType::Named {
                    name: name.to_string(),
                    type_args: vec![elem_ty],
                    lifetime_args: Vec::new(),
                    const_args: Vec::new(),
                })
            }
            Expr::For { .. } => Ok(RustType::Unit),
            Expr::UnionInit { name, .. } => Ok(RustType::Named {
                name: name.clone(),
                type_args: Vec::new(),
                lifetime_args: Vec::new(),
                const_args: Vec::new(),
            }),
            Expr::UnionFieldAccess { union_expr, field } => {
                let base_ty = self.infer_expr_type(union_expr)?;
                let type_name =
                    nominal_type_name(&base_ty).ok_or_else(|| VirLoweringError::MissingType {
                        context: format!(
                            "union field `{field}` on `{union_expr:?}` in `{}`",
                            self.function_name
                        ),
                    })?;
                self.field_type(&type_name, field).cloned().ok_or_else(|| {
                    VirLoweringError::MissingType {
                        context: format!(
                            "union field `{type_name}::{field}` in `{}`",
                            self.function_name
                        ),
                    }
                })
            }
            Expr::RawDeref(base) => match self.infer_expr_type(base)? {
                RustType::RawPtr { inner, .. } => Ok(*inner),
                RustType::Reference { inner, .. } | RustType::Box { inner } => Ok(*inner),
                other => Err(VirLoweringError::Unsupported {
                    context: "raw deref expression",
                    detail: format!("cannot raw-dereference `{other:?}`"),
                }),
            },
            Expr::Closure {
                params,
                body,
                captures,
                ..
            } => {
                let param_tys: Vec<RustType> = params.iter().map(|(_, ty)| ty.clone()).collect();
                let capture_tys: Vec<(String, RustType, Mutability)> = captures
                    .iter()
                    .filter_map(|(name, mutability)| {
                        let local = self.lookup_local(name).ok()?;
                        let ty = self.local_ty(local).ok()?;
                        Some((name.clone(), ty, *mutability))
                    })
                    .collect();
                let mut full_params: Vec<(String, RustType)> = capture_tys
                    .iter()
                    .map(|(name, ty, _)| (name.clone(), ty.clone()))
                    .collect();
                full_params.extend_from_slice(params);
                let ret_ty = self.infer_closure_body_type(&full_params, body)?;
                let kind = ClosureKind::from_captures(captures);
                Ok(RustType::Closure {
                    params: param_tys,
                    ret: Box::new(ret_ty),
                    captures: capture_tys,
                    kind,
                })
            }
            Expr::Async { .. } => Ok(RustType::ImplTrait {
                traits: vec!["Future".to_string()],
            }),
            Expr::Await { base } => {
                if let Some(output_ty) = self.future_output_type_of_expr(base) {
                    return Ok(output_ty);
                }
                let base_ty = self.infer_expr_type(base)?;
                let base_ty = if let RustType::Pin { inner } = base_ty {
                    *inner
                } else {
                    base_ty
                };
                match base_ty {
                    RustType::ImplTrait { .. } | RustType::DynTrait { .. } => Ok(RustType::Infer),
                    other => Ok(other),
                }
            }
            Expr::InlineAsm(_) => Ok(RustType::Unit),
        }
    }

    /// Result type of a recognized standard-library constructor intrinsic,
    /// or `None` when `name` is not a known builtin constructor.
    ///
    /// `Vec::new`/`Vec::with_capacity` produce `Vec<_>` (the element type is
    /// resolved from the call site by `lower_call_expr`), `String::new`/
    /// `String::from` produce a string, and `Box::new(x)` is transparent over
    /// the type of its argument.
    fn builtin_constructor_result_type(
        &self,
        name: &str,
        args: &[Expr],
    ) -> Result<Option<RustType>, VirLoweringError> {
        let ty = match (name, args.len()) {
            ("Vec::new", 0) | ("Vec::with_capacity", 1) => RustType::Vec {
                element: Box::new(RustType::Infer),
            },
            ("String::new", 0) | ("String::from", 1) => RustType::Str,
            ("Box::new", 1) => RustType::Box {
                inner: Box::new(self.infer_expr_type(&args[0])?),
            },
            _ => return Ok(None),
        };
        Ok(Some(ty))
    }

    fn loop_result_type(
        &self,
        body: &Expr,
        loop_label: Option<&str>,
        default: RustType,
    ) -> RustType {
        self.find_targeted_break_type(body, loop_label, false)
            .unwrap_or(default)
    }

    fn find_targeted_break_type(
        &self,
        expr: &Expr,
        loop_label: Option<&str>,
        nested_loop: bool,
    ) -> Option<RustType> {
        match expr {
            Expr::Break { label, value }
                if match label.as_deref() {
                    Some(l) => loop_label == Some(l),
                    None => !nested_loop,
                } =>
            {
                value
                    .as_deref()
                    .and_then(|v| self.infer_expr_type(v).ok())
                    .or(Some(RustType::Unit))
            }
            Expr::Block { stmts, expr } => stmts
                .iter()
                .find_map(|stmt| match stmt {
                    SemStmt::Expr(expr) => {
                        self.find_targeted_break_type(expr, loop_label, nested_loop)
                    }
                    _ => None,
                })
                .or_else(|| {
                    expr.as_deref().and_then(|expr| {
                        self.find_targeted_break_type(expr, loop_label, nested_loop)
                    })
                }),
            Expr::If {
                then_branch,
                else_branch,
                ..
            } => self
                .find_targeted_break_type(then_branch, loop_label, nested_loop)
                .or_else(|| {
                    else_branch.as_deref().and_then(|expr| {
                        self.find_targeted_break_type(expr, loop_label, nested_loop)
                    })
                }),
            Expr::Match { arms, .. } => arms
                .iter()
                .find_map(|arm| self.find_targeted_break_type(&arm.body, loop_label, nested_loop)),
            Expr::Loop { body, .. } | Expr::While { body, .. } | Expr::For { body, .. } => {
                loop_label.and_then(|_| self.find_targeted_break_type(body, loop_label, true))
            }
            _ => None,
        }
    }

    fn infer_builtin_enum_variant_type(
        &self,
        enum_name: &str,
        variant: &str,
        expr: &Expr,
    ) -> Result<RustType, VirLoweringError> {
        match (enum_name, expr) {
            (
                "Option",
                Expr::EnumVariant {
                    payload: crate::expr::EnumVariantPayload::Unit,
                    ..
                },
            ) if variant == "None" => Ok(RustType::Option {
                inner: Box::new(RustType::Infer),
            }),
            (
                "Option",
                Expr::EnumVariant {
                    payload: crate::expr::EnumVariantPayload::Tuple(values),
                    ..
                },
            ) if variant == "Some" && values.len() == 1 => Ok(RustType::Option {
                inner: Box::new(self.infer_expr_type(&values[0])?),
            }),
            (
                "Result",
                Expr::EnumVariant {
                    payload: crate::expr::EnumVariantPayload::Tuple(values),
                    ..
                },
            ) if variant == "Ok" && values.len() == 1 => Ok(RustType::Result {
                ok: Box::new(self.infer_expr_type(&values[0])?),
                err: Box::new(RustType::Infer),
            }),
            (
                "Result",
                Expr::EnumVariant {
                    payload: crate::expr::EnumVariantPayload::Tuple(values),
                    ..
                },
            ) if variant == "Err" && values.len() == 1 => Ok(RustType::Result {
                ok: Box::new(RustType::Infer),
                err: Box::new(self.infer_expr_type(&values[0])?),
            }),
            _ => Err(VirLoweringError::MissingType {
                context: format!(
                    "enum variant `{enum_name}::{variant}` in `{}`",
                    self.function_name
                ),
            }),
        }
    }
}
