// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::super::SourceError;
use super::Parser;
use crate::types::{
    ConstGenericArg, ConstGenericValue, ConstParamDef, IntType, RustType, TypeParamDef, UintType,
};

impl Parser {
    pub(crate) fn parse_type_and_const_params(
        &mut self,
        generics: &syn::Generics,
    ) -> Result<(Vec<TypeParamDef>, Vec<ConstParamDef>), SourceError> {
        let mut type_params = Vec::new();
        let mut const_params = Vec::new();
        for param in &generics.params {
            match param {
                syn::GenericParam::Type(ty_param) => {
                    let mut bounds = Vec::new();
                    for bound in &ty_param.bounds {
                        match bound {
                            syn::TypeParamBound::Trait(trait_bound) => {
                                bounds.push(Self::plain_trait_bound_name(
                                    trait_bound,
                                    "generic parameter",
                                    &format!("trait bound on type parameter `{}`", ty_param.ident),
                                )?)
                            }
                            syn::TypeParamBound::Lifetime(_) => {}
                            _ => {}
                        }
                    }
                    type_params.push(TypeParamDef {
                        id: 0,
                        name: ty_param.ident.to_string(),
                        bounds,
                    });
                }
                syn::GenericParam::Lifetime(_) => {}
                syn::GenericParam::Const(cp) => {
                    const_params.push(ConstParamDef {
                        name: cp.ident.to_string(),
                        ty: self.parse_const_param_type(&cp.ty)?,
                    });
                }
            }
        }
        if let Some(where_clause) = &generics.where_clause {
            for predicate in &where_clause.predicates {
                if let syn::WherePredicate::Type(pred_type) = predicate {
                    if let syn::Type::Path(type_path) = &pred_type.bounded_ty {
                        let name = Self::path_to_string(&type_path.path);
                        if let Some(tp) = type_params.iter_mut().find(|tp| tp.name == name) {
                            for bound in &pred_type.bounds {
                                if let syn::TypeParamBound::Trait(trait_bound) = bound {
                                    tp.bounds.push(Self::plain_trait_bound_name(
                                        trait_bound,
                                        "generic parameter",
                                        &format!("trait bound on type parameter `{}`", tp.name),
                                    )?);
                                }
                            }
                        }
                    }
                }
            }
        }
        Ok((type_params, const_params))
    }

    pub(crate) fn parse_const_generic_arg(
        &mut self,
        expr: &syn::Expr,
    ) -> Result<ConstGenericArg, SourceError> {
        match expr {
            syn::Expr::Lit(syn::ExprLit {
                lit: syn::Lit::Int(int),
                ..
            }) => {
                if int.suffix() == "i32" {
                    int.base10_parse::<i32>()
                        .map(ConstGenericValue::I32)
                        .map(ConstGenericArg::Value)
                        .map_err(|err| SourceError::Invalid {
                            context: "const generic argument",
                            detail: err.to_string(),
                        })
                } else {
                    int.base10_parse::<usize>()
                        .map(ConstGenericValue::Usize)
                        .map(ConstGenericArg::Value)
                        .map_err(|err| SourceError::Invalid {
                            context: "const generic argument",
                            detail: err.to_string(),
                        })
                }
            }
            syn::Expr::Lit(syn::ExprLit {
                lit: syn::Lit::Bool(value),
                ..
            }) => Ok(ConstGenericArg::Value(ConstGenericValue::Bool(value.value))),
            syn::Expr::Lit(syn::ExprLit {
                lit: syn::Lit::Char(value),
                ..
            }) => Ok(ConstGenericArg::Value(ConstGenericValue::Char(value.value()))),
            syn::Expr::Paren(paren) => self.parse_const_generic_arg(&paren.expr),
            syn::Expr::Group(group) => self.parse_const_generic_arg(&group.expr),
            // A braced const argument (e.g. `Proj<{N}>` or `Proj<{N + 1}>`). Rust requires
            // the braces to disambiguate a const generic argument that is a bare const
            // parameter or expression from a type argument. A single trailing expression
            // with no statements unwraps to its inner const expression.
            syn::Expr::Block(block)
                if block.attrs.is_empty()
                    && block.label.is_none()
                    && block.block.stmts.len() == 1 =>
            {
                match &block.block.stmts[0] {
                    syn::Stmt::Expr(expr, None) => self.parse_const_generic_arg(expr),
                    _ => Err(Self::unsupported(
                        "const generic argument",
                        "only a single const expression is supported inside braces",
                    )),
                }
            }
            syn::Expr::Unary(unary) if matches!(unary.op, syn::UnOp::Neg(_)) => {
                let arg = self.parse_const_generic_arg(&unary.expr)?;
                match arg {
                    ConstGenericArg::Value(ConstGenericValue::Usize(value)) => i32::try_from(value)
                        .map_err(|_| SourceError::Invalid {
                            context: "const generic argument",
                            detail: "negation overflow".to_string(),
                        })
                        .and_then(|value| {
                            value.checked_neg().ok_or(SourceError::Invalid {
                                context: "const generic argument",
                                detail: "negation overflow".to_string(),
                            })
                        })
                        .map(ConstGenericValue::I32)
                        .map(ConstGenericArg::Value),
                    ConstGenericArg::Value(ConstGenericValue::I32(value)) => value
                        .checked_neg()
                        .ok_or(SourceError::Invalid {
                            context: "const generic argument",
                            detail: "negation overflow".to_string(),
                        })
                        .map(ConstGenericValue::I32)
                        .map(ConstGenericArg::Value),
                    other => Ok(ConstGenericArg::Neg(Box::new(other))),
                }
            }
            syn::Expr::Path(path) if path.qself.is_none() && path.path.segments.len() == 1 => {
                let segment = path.path.segments.first().expect("len checked");
                if !matches!(segment.arguments, syn::PathArguments::None) {
                    return Err(Self::unsupported(
                        "const generic argument",
                        "const generic parameters do not accept generic arguments",
                    ));
                }
                let name = segment.ident.to_string();
                if self.resolve_const_param(&name).is_some() {
                    Ok(ConstGenericArg::Param(name))
                } else {
                    Err(Self::unsupported(
                        "const generic argument",
                        format!("unsupported const expression `{name}`"),
                    ))
                }
            }
            syn::Expr::Binary(binary) => {
                let lhs = Box::new(self.parse_const_generic_arg(&binary.left)?);
                let rhs = Box::new(self.parse_const_generic_arg(&binary.right)?);
                match binary.op {
                    syn::BinOp::Add(_) => Ok(ConstGenericArg::Add(lhs, rhs)),
                    syn::BinOp::Sub(_) => Ok(ConstGenericArg::Sub(lhs, rhs)),
                    syn::BinOp::Mul(_) => Ok(ConstGenericArg::Mul(lhs, rhs)),
                    syn::BinOp::Div(_) => Ok(ConstGenericArg::Div(lhs, rhs)),
                    syn::BinOp::Rem(_) => Ok(ConstGenericArg::Rem(lhs, rhs)),
                    _ => Err(Self::unsupported(
                        "const generic argument",
                        "only arithmetic const generic expressions are supported",
                    )),
                }
            }
            _ => Err(Self::unsupported(
                "const generic argument",
                "only arithmetic const generic expressions and in-scope const parameters are supported",
            )),
        }
    }

    pub(crate) fn parse_array_len_arg(
        &mut self,
        expr: &syn::Expr,
    ) -> Result<ConstGenericArg, SourceError> {
        let arg = self.parse_const_generic_arg(expr)?;
        if self.const_arg_kind(&arg) == Some(ConstArgKind::Usize) {
            Ok(arg)
        } else {
            Err(Self::unsupported(
                "array length",
                "only `usize` const generics are supported in array lengths",
            ))
        }
    }

    pub(crate) fn parse_const_param_type(
        &mut self,
        ty: &syn::Type,
    ) -> Result<RustType, SourceError> {
        let ty = self.parse_type(ty)?;
        match ty {
            RustType::Uint(UintType::Usize)
            | RustType::Bool
            | RustType::Char
            | RustType::Int(IntType::I32) => Ok(ty),
            _ => Err(Self::unsupported(
                "generic parameter",
                "only `usize`, `bool`, `char`, and `i32` const generic parameters are supported",
            )),
        }
    }

    fn const_arg_kind(&self, arg: &ConstGenericArg) -> Option<ConstArgKind> {
        match arg {
            ConstGenericArg::Value(ConstGenericValue::Usize(_)) => Some(ConstArgKind::Usize),
            ConstGenericArg::Value(ConstGenericValue::Bool(_)) => Some(ConstArgKind::Bool),
            ConstGenericArg::Value(ConstGenericValue::Char(_)) => Some(ConstArgKind::Char),
            ConstGenericArg::Value(ConstGenericValue::I32(_)) => Some(ConstArgKind::I32),
            ConstGenericArg::Value(ConstGenericValue::Unknown) => None,
            ConstGenericArg::Param(name) => match self.resolve_const_param(name) {
                Some(RustType::Uint(UintType::Usize)) => Some(ConstArgKind::Usize),
                Some(RustType::Bool) => Some(ConstArgKind::Bool),
                Some(RustType::Char) => Some(ConstArgKind::Char),
                Some(RustType::Int(IntType::I32)) => Some(ConstArgKind::I32),
                _ => None,
            },
            ConstGenericArg::Add(lhs, rhs)
            | ConstGenericArg::Sub(lhs, rhs)
            | ConstGenericArg::Mul(lhs, rhs)
            | ConstGenericArg::Div(lhs, rhs)
            | ConstGenericArg::Rem(lhs, rhs) => {
                match (self.const_arg_kind(lhs), self.const_arg_kind(rhs)) {
                    (Some(ConstArgKind::Usize), Some(ConstArgKind::Usize)) => {
                        Some(ConstArgKind::Usize)
                    }
                    (Some(ConstArgKind::I32), Some(ConstArgKind::I32)) => Some(ConstArgKind::I32),
                    _ => None,
                }
            }
            ConstGenericArg::Neg(inner) => {
                (self.const_arg_kind(inner) == Some(ConstArgKind::I32)).then_some(ConstArgKind::I32)
            }
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ConstArgKind {
    Usize,
    Bool,
    Char,
    I32,
}
