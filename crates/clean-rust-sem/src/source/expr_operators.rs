// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::parser::Parser;
use super::SourceError;
use crate::expr::Expr;
use crate::values::{BinOp, UnOp, Value};

impl Parser {
    pub(super) fn parse_unary(&mut self, unary: &syn::ExprUnary) -> Result<Expr, SourceError> {
        match unary.op {
            syn::UnOp::Deref(_) => Ok(Expr::Deref(Box::new(self.parse_expr(&unary.expr)?))),
            syn::UnOp::Neg(_) => Ok(Expr::UnOp {
                op: UnOp::Neg,
                expr: Box::new(self.parse_expr(&unary.expr)?),
            }),
            syn::UnOp::Not(_) => Ok(Expr::UnOp {
                op: UnOp::Not,
                expr: Box::new(self.parse_expr(&unary.expr)?),
            }),
            _ => Err(Self::unsupported(
                "expression",
                "unsupported unary operator",
            )),
        }
    }

    pub(super) fn parse_binary_expr(
        &mut self,
        binary: &syn::ExprBinary,
    ) -> Result<Expr, SourceError> {
        match &binary.op {
            // Short-circuit logical operators: desugar to if-expressions
            // a && b => if a { b } else { false }
            syn::BinOp::And(_) => Ok(Expr::If {
                condition: Box::new(self.parse_expr(&binary.left)?),
                then_branch: Box::new(self.parse_expr(&binary.right)?),
                else_branch: Some(Box::new(Expr::Literal(Value::Bool(false)))),
            }),
            // a || b => if a { true } else { b }
            syn::BinOp::Or(_) => Ok(Expr::If {
                condition: Box::new(self.parse_expr(&binary.left)?),
                then_branch: Box::new(Expr::Literal(Value::Bool(true))),
                else_branch: Some(Box::new(self.parse_expr(&binary.right)?)),
            }),
            // Compound assignment stays explicit in the semantic AST so
            // lowering can preserve single-evaluation place semantics.
            syn::BinOp::AddAssign(_)
            | syn::BinOp::SubAssign(_)
            | syn::BinOp::MulAssign(_)
            | syn::BinOp::DivAssign(_)
            | syn::BinOp::RemAssign(_)
            | syn::BinOp::BitAndAssign(_)
            | syn::BinOp::BitOrAssign(_)
            | syn::BinOp::BitXorAssign(_)
            | syn::BinOp::ShlAssign(_)
            | syn::BinOp::ShrAssign(_) => {
                let op = match &binary.op {
                    syn::BinOp::AddAssign(_) => BinOp::Add,
                    syn::BinOp::SubAssign(_) => BinOp::Sub,
                    syn::BinOp::MulAssign(_) => BinOp::Mul,
                    syn::BinOp::DivAssign(_) => BinOp::Div,
                    syn::BinOp::RemAssign(_) => BinOp::Rem,
                    syn::BinOp::BitAndAssign(_) => BinOp::BitAnd,
                    syn::BinOp::BitOrAssign(_) => BinOp::BitOr,
                    syn::BinOp::BitXorAssign(_) => BinOp::BitXor,
                    syn::BinOp::ShlAssign(_) => BinOp::Shl,
                    syn::BinOp::ShrAssign(_) => BinOp::Shr,
                    _ => unreachable!("filtered by outer match"),
                };
                Ok(Expr::AssignOp {
                    op,
                    target: Box::new(self.parse_expr(&binary.left)?),
                    value: Box::new(self.parse_expr(&binary.right)?),
                })
            }
            // Standard binary operators
            _ => Ok(Expr::BinOp {
                op: Self::parse_binop(&binary.op)?,
                left: Box::new(self.parse_expr(&binary.left)?),
                right: Box::new(self.parse_expr(&binary.right)?),
            }),
        }
    }
}
