// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Assert macro desugaring (`assert!`, `assert_eq!`, `assert_ne!`, and their
//! `debug_assert` counterparts).

use super::super::{parser::Parser, SourceError};
use crate::expr::Expr;
use crate::values::{BinOp, UnOp, Value};

impl Parser {
    /// Desugar `assert!(cond)` to `if !cond { Expr::Panic { .. } }`.
    pub(super) fn parse_assert_macro(
        &mut self,
        tokens: &proc_macro2::TokenStream,
    ) -> Result<Expr, SourceError> {
        use syn::parse::Parser as SynParser;
        let args = syn::punctuated::Punctuated::<syn::Expr, syn::Token![,]>::parse_terminated
            .parse2(tokens.clone())
            .map_err(SourceError::Parse)?;
        let condition = args.first().ok_or_else(|| SourceError::Invalid {
            context: "assert! macro",
            detail: "assert! requires a condition argument".to_string(),
        })?;
        let cond = self.parse_expr(condition)?;
        Ok(Expr::If {
            condition: Box::new(Expr::UnOp {
                op: UnOp::Not,
                expr: Box::new(cond),
            }),
            then_branch: Box::new(Expr::Panic {
                message: Box::new(Expr::Literal(Value::Unit)),
            }),
            else_branch: Some(Box::new(Expr::Literal(Value::Unit))),
        })
    }

    /// Desugar `assert_eq!(a, b)` / `assert_ne!(a, b)`.
    ///
    /// `fail_op` is the comparison that triggers the abort:
    /// - `BinOp::Ne` for `assert_eq!` (abort when `a != b`)
    /// - `BinOp::Eq` for `assert_ne!` (abort when `a == b`)
    pub(super) fn parse_assert_cmp_macro(
        &mut self,
        tokens: &proc_macro2::TokenStream,
        fail_op: BinOp,
    ) -> Result<Expr, SourceError> {
        use syn::parse::Parser as SynParser;
        let args = syn::punctuated::Punctuated::<syn::Expr, syn::Token![,]>::parse_terminated
            .parse2(tokens.clone())
            .map_err(SourceError::Parse)?;
        let mut iter = args.iter();
        let left = iter.next().ok_or_else(|| SourceError::Invalid {
            context: "assert macro",
            detail: "assert_eq!/assert_ne! requires two arguments".to_string(),
        })?;
        let right = iter.next().ok_or_else(|| SourceError::Invalid {
            context: "assert macro",
            detail: "assert_eq!/assert_ne! requires two arguments".to_string(),
        })?;
        let left_expr = self.parse_expr(left)?;
        let right_expr = self.parse_expr(right)?;
        Ok(Expr::If {
            condition: Box::new(Expr::BinOp {
                op: fail_op,
                left: Box::new(left_expr),
                right: Box::new(right_expr),
            }),
            then_branch: Box::new(Expr::Panic {
                message: Box::new(Expr::Literal(Value::Unit)),
            }),
            else_branch: Some(Box::new(Expr::Literal(Value::Unit))),
        })
    }
}
