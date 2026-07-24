// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::super::{parser::Parser, SourceError};
use crate::expr::Expr;
use crate::format_intrinsics::{validate_format_call, FORMAT_INTRINSIC};
use crate::values::Value;

impl Parser {
    pub(super) fn parse_format_macro(
        &mut self,
        tokens: &proc_macro2::TokenStream,
    ) -> Result<Expr, SourceError> {
        use syn::parse::Parser as SynParser;

        let args = syn::punctuated::Punctuated::<syn::Expr, syn::Token![,]>::parse_terminated
            .parse2(tokens.clone())
            .map_err(SourceError::Parse)?;
        let template_expr = args.first().ok_or_else(|| SourceError::Invalid {
            context: "format macro",
            detail: "format! requires a template string".to_string(),
        })?;
        let template = Self::parse_format_template(template_expr)?;
        validate_format_call(&template, args.len().saturating_sub(1)).map_err(|detail| {
            SourceError::Unsupported {
                context: "format macro",
                detail: detail.to_string(),
            }
        })?;

        let mut lowered_args = Vec::with_capacity(args.len());
        lowered_args.push(Expr::Literal(Value::Str(template)));
        lowered_args.extend(
            args.iter()
                .skip(1)
                .map(|expr| self.parse_expr(expr))
                .collect::<Result<Vec<_>, _>>()?,
        );
        Ok(Expr::Call {
            func: Box::new(Expr::Var {
                name: FORMAT_INTRINSIC.to_string(),
                local_idx: 0,
            }),
            args: lowered_args,
            type_args: vec![],
        })
    }

    fn parse_format_template(expr: &syn::Expr) -> Result<String, SourceError> {
        match expr {
            syn::Expr::Lit(syn::ExprLit {
                lit: syn::Lit::Str(value),
                ..
            }) => Ok(value.value()),
            other => Err(Self::unsupported(
                "format macro",
                format!(
                    "format! requires a string literal template, found `{}`",
                    Self::expr_kind(other)
                ),
            )),
        }
    }

    pub(super) fn parse_concat_macro(
        &mut self,
        tokens: &proc_macro2::TokenStream,
    ) -> Result<Expr, SourceError> {
        use syn::parse::Parser as SynParser;

        let args = syn::punctuated::Punctuated::<syn::Expr, syn::Token![,]>::parse_terminated
            .parse2(tokens.clone())
            .map_err(SourceError::Parse)?;
        let value = args
            .iter()
            .map(|expr| self.compile_time_string_fragment(expr))
            .collect::<Result<Vec<_>, _>>()?
            .join("");
        Ok(Expr::Literal(Value::Str(value)))
    }

    fn compile_time_string_fragment(&mut self, expr: &syn::Expr) -> Result<String, SourceError> {
        match expr {
            syn::Expr::Lit(expr_lit) => self.literal_string_fragment(&expr_lit.lit),
            syn::Expr::Unary(unary) if matches!(unary.op, syn::UnOp::Neg(_)) => Ok(format!(
                "-{}",
                self.compile_time_numeric_fragment(&unary.expr)?
            )),
            syn::Expr::Macro(expr_macro) => {
                let dispatch_name = Self::builtin_macro_dispatch_name(&expr_macro.mac.path)
                    .unwrap_or_else(|| Self::path_to_string(&expr_macro.mac.path));
                match dispatch_name.as_str() {
                    "stringify" => Ok(expr_macro.mac.tokens.to_string()),
                    "concat" => {
                        let Expr::Literal(Value::Str(value)) =
                            self.parse_concat_macro(&expr_macro.mac.tokens)?
                        else {
                            unreachable!("concat! always lowers to a string literal");
                        };
                        Ok(value)
                    }
                    _ => Err(Self::unsupported(
                        "concat! macro",
                        format!("unsupported nested macro `{dispatch_name}!`"),
                    )),
                }
            }
            other => Err(Self::unsupported(
                "concat! macro",
                format!(
                    "unsupported compile-time argument `{}`",
                    Self::expr_kind(other)
                ),
            )),
        }
    }

    fn literal_string_fragment(&self, lit: &syn::Lit) -> Result<String, SourceError> {
        match lit {
            syn::Lit::Str(value) => Ok(value.value()),
            syn::Lit::Char(value) => Ok(value.value().to_string()),
            syn::Lit::Bool(value) => Ok(value.value.to_string()),
            syn::Lit::Int(value) => Ok(format!("{}{}", value.base10_digits(), value.suffix())),
            syn::Lit::Float(value) => Ok(format!("{}{}", value.base10_digits(), value.suffix())),
            other => Err(Self::unsupported(
                "concat! macro",
                format!("unsupported literal `{}`", Self::literal_kind(other)),
            )),
        }
    }

    fn compile_time_numeric_fragment(&self, expr: &syn::Expr) -> Result<String, SourceError> {
        let syn::Expr::Lit(expr_lit) = expr else {
            return Err(Self::unsupported(
                "concat! macro",
                "negative concat! arguments must be numeric literals",
            ));
        };
        match &expr_lit.lit {
            syn::Lit::Int(value) => Ok(format!("{}{}", value.base10_digits(), value.suffix())),
            syn::Lit::Float(value) => Ok(format!("{}{}", value.base10_digits(), value.suffix())),
            _ => Err(Self::unsupported(
                "concat! macro",
                "negative concat! arguments must be numeric literals",
            )),
        }
    }

    fn literal_kind(lit: &syn::Lit) -> &'static str {
        match lit {
            syn::Lit::Str(_) => "string literal",
            syn::Lit::ByteStr(_) => "byte string literal",
            syn::Lit::Byte(_) => "byte literal",
            syn::Lit::Char(_) => "char literal",
            syn::Lit::Int(_) => "integer literal",
            syn::Lit::Float(_) => "float literal",
            syn::Lit::Bool(_) => "bool literal",
            syn::Lit::Verbatim(_) => "verbatim literal",
            syn::Lit::CStr(_) => "c string literal",
            _ => "literal",
        }
    }
}
