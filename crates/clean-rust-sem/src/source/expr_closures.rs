// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::collections::HashSet;

use super::captures::collect_expr_var_names;
use super::parser::Parser;
use super::SourceError;
use crate::expr::Expr;
use crate::types::{Mutability, RustType};

impl Parser {
    pub(super) fn parse_macro_expr(&mut self, mac: &syn::ExprMacro) -> Result<Expr, SourceError> {
        self.parse_macro_invocation(&mac.mac)
    }

    pub(super) fn parse_closure(
        &mut self,
        closure: &syn::ExprClosure,
    ) -> Result<Expr, SourceError> {
        let is_async = closure.asyncness.is_some();
        let capture_by_value = closure.capture.is_some();
        let params = closure
            .inputs
            .iter()
            .map(|pat| self.parse_closure_param(pat))
            .collect::<Result<Vec<_>, _>>()?;
        let mut body = self.parse_expr(&closure.body)?;
        // Async closures wrap their body in an Async block
        if is_async {
            body = Expr::Async {
                capture_by_value,
                body: Box::new(body),
            };
        }
        let param_names: HashSet<&str> = params.iter().map(|(name, _)| name.as_str()).collect();
        let mut var_names = HashSet::new();
        collect_expr_var_names(&body, &mut var_names);
        let captures = var_names
            .into_iter()
            .filter(|name| !param_names.contains(name.as_str()))
            .map(|name| (name, Mutability::Shared))
            .collect();
        Ok(Expr::Closure {
            params,
            body: Box::new(body),
            captures,
            capture_by_value,
        })
    }

    fn parse_closure_param(&mut self, pat: &syn::Pat) -> Result<(String, RustType), SourceError> {
        match pat {
            syn::Pat::Type(pat_type) => {
                let name = Self::pat_ident_name(&pat_type.pat)?;
                let ty = self.parse_type(&pat_type.ty)?;
                Ok((name, ty))
            }
            syn::Pat::Ident(ident) => Ok((ident.ident.to_string(), RustType::Infer)),
            _ => Err(Self::unsupported(
                "closure parameter",
                "only identifier and typed closure parameters are supported",
            )),
        }
    }
}
