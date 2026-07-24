// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Operator-heavy expression parsing: literals, binary/unary/update/assignment/ternary.

use super::{CParser, NodeExt, ParseError, ParseResult};
use crate::expr::{BinOp, CExpr, UnaryOp};
use tree_sitter::Node;

impl CParser {
    /// Parse number literal
    pub(super) fn parse_number_literal(&self, text: &str) -> ParseResult<CExpr> {
        let text = text.trim().trim_end_matches(['u', 'U', 'l', 'L']);

        // Check for hex
        if text.starts_with("0x") || text.starts_with("0X") {
            let val = i64::from_str_radix(&text[2..], 16).map_err(|_| ParseError::InvalidInt {
                value: text.to_string(),
            })?;
            return Ok(CExpr::IntLit(val));
        }

        // Check for octal
        if text.starts_with('0') && text.len() > 1 && !text.contains('.') {
            if let Ok(val) = i64::from_str_radix(&text[1..], 8) {
                return Ok(CExpr::IntLit(val));
            }
        }

        // Check for float
        if text.contains('.') || text.contains('e') || text.contains('E') {
            let val: f64 = text.parse().map_err(|_| ParseError::InvalidFloat {
                value: text.to_string(),
            })?;
            return Ok(CExpr::FloatLit(val));
        }

        // Decimal integer
        let val: i64 = text.parse().map_err(|_| ParseError::InvalidInt {
            value: text.to_string(),
        })?;
        Ok(CExpr::IntLit(val))
    }

    /// Parse char literal
    pub(super) fn parse_char_literal(&self, text: &str) -> ParseResult<CExpr> {
        let inner = text.trim_start_matches('\'').trim_end_matches('\'');

        let ch = if inner.starts_with('\\') {
            match inner.chars().nth(1) {
                Some('n') => b'\n',
                Some('r') => b'\r',
                Some('t') => b'\t',
                Some('0') | None => b'\0',
                Some('\\') => b'\\',
                Some('\'') => b'\'',
                Some('"') => b'"',
                Some(c) => c as u8,
            }
        } else {
            inner.chars().next().unwrap_or('\0') as u8
        };

        Ok(CExpr::CharLit(ch))
    }

    /// Parse int literal (for enums, etc)
    pub(super) fn parse_int_literal(&self, text: &str) -> ParseResult<i64> {
        let text = text.trim().trim_end_matches(['u', 'U', 'l', 'L']);

        if text.starts_with("0x") || text.starts_with("0X") {
            return i64::from_str_radix(&text[2..], 16).map_err(|_| ParseError::InvalidInt {
                value: text.to_string(),
            });
        }

        if text.starts_with('0') && text.len() > 1 {
            return i64::from_str_radix(&text[1..], 8).map_err(|_| ParseError::InvalidInt {
                value: text.to_string(),
            });
        }

        text.parse().map_err(|_| ParseError::InvalidInt {
            value: text.to_string(),
        })
    }

    /// Parse binary expression
    pub(super) fn parse_binary_expr(&self, node: Node, source: &str) -> ParseResult<CExpr> {
        let mut left = None;
        let mut op = None;
        let mut right = None;

        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                let kind = child.kind();
                if let Some(bin_op) = self.parse_binary_op(kind) {
                    op = Some(bin_op);
                } else if left.is_none() {
                    left = Some(self.parse_expr(child, source)?);
                } else {
                    right = Some(self.parse_expr(child, source)?);
                }
            }
        }

        Ok(CExpr::BinOp {
            op: op.ok_or_else(|| ParseError::MissingField {
                field: "operator".to_string(),
                node_kind: "binary_expression".to_string(),
            })?,
            left: Box::new(left.ok_or_else(|| ParseError::MissingField {
                field: "left".to_string(),
                node_kind: "binary_expression".to_string(),
            })?),
            right: Box::new(right.ok_or_else(|| ParseError::MissingField {
                field: "right".to_string(),
                node_kind: "binary_expression".to_string(),
            })?),
        })
    }

    /// Parse binary operator
    fn parse_binary_op(&self, kind: &str) -> Option<BinOp> {
        match kind {
            "+" => Some(BinOp::Add),
            "-" => Some(BinOp::Sub),
            "*" => Some(BinOp::Mul),
            "/" => Some(BinOp::Div),
            "%" => Some(BinOp::Mod),
            "&" => Some(BinOp::BitAnd),
            "|" => Some(BinOp::BitOr),
            "^" => Some(BinOp::BitXor),
            "<<" => Some(BinOp::Shl),
            ">>" => Some(BinOp::Shr),
            "==" => Some(BinOp::Eq),
            "!=" => Some(BinOp::Ne),
            "<" => Some(BinOp::Lt),
            "<=" => Some(BinOp::Le),
            ">" => Some(BinOp::Gt),
            ">=" => Some(BinOp::Ge),
            "&&" => Some(BinOp::LogAnd),
            "||" => Some(BinOp::LogOr),
            "," => Some(BinOp::Comma),
            _ => None,
        }
    }

    /// Parse unary expression
    pub(super) fn parse_unary_expr(&self, node: Node, source: &str) -> ParseResult<CExpr> {
        let mut op = None;
        let mut operand = None;

        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                let kind = child.kind();
                if let Some(unary_op) = self.parse_unary_op(kind) {
                    op = Some(unary_op);
                } else {
                    operand = Some(self.parse_expr(child, source)?);
                }
            }
        }

        Ok(CExpr::UnaryOp {
            op: op.ok_or_else(|| ParseError::MissingField {
                field: "operator".to_string(),
                node_kind: "unary_expression".to_string(),
            })?,
            operand: Box::new(operand.ok_or_else(|| ParseError::MissingField {
                field: "operand".to_string(),
                node_kind: "unary_expression".to_string(),
            })?),
        })
    }

    /// Parse unary operator
    fn parse_unary_op(&self, kind: &str) -> Option<UnaryOp> {
        match kind {
            "-" => Some(UnaryOp::Neg),
            "+" => Some(UnaryOp::Pos),
            "~" => Some(UnaryOp::BitNot),
            "!" => Some(UnaryOp::LogNot),
            "&" => Some(UnaryOp::AddrOf),
            "*" => Some(UnaryOp::Deref),
            _ => None,
        }
    }

    /// Parse update expression (++x, --x, x++, x--)
    pub(super) fn parse_update_expr(&self, node: Node, source: &str) -> ParseResult<CExpr> {
        let mut op = None;
        let mut operand = None;

        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                let kind = child.kind();
                match kind {
                    "++" => {
                        let is_prefix = operand.is_none();
                        op = Some(if is_prefix {
                            UnaryOp::PreInc
                        } else {
                            UnaryOp::PostInc
                        });
                    }
                    "--" => {
                        let is_prefix = operand.is_none();
                        op = Some(if is_prefix {
                            UnaryOp::PreDec
                        } else {
                            UnaryOp::PostDec
                        });
                    }
                    _ => {
                        operand = Some(self.parse_expr(child, source)?);
                    }
                }
            }
        }

        Ok(CExpr::UnaryOp {
            op: op.ok_or_else(|| ParseError::MissingField {
                field: "operator".to_string(),
                node_kind: "update_expression".to_string(),
            })?,
            operand: Box::new(operand.ok_or_else(|| ParseError::MissingField {
                field: "operand".to_string(),
                node_kind: "update_expression".to_string(),
            })?),
        })
    }

    /// Parse assignment expression
    pub(super) fn parse_assignment_expr(&self, node: Node, source: &str) -> ParseResult<CExpr> {
        let mut left = None;
        let mut op = None;
        let mut right = None;

        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                let kind = child.kind();
                if let Some(assign_op) = self.parse_assign_op(kind) {
                    op = Some(assign_op);
                } else if left.is_none() {
                    left = Some(self.parse_expr(child, source)?);
                } else {
                    right = Some(self.parse_expr(child, source)?);
                }
            }
        }

        Ok(CExpr::BinOp {
            op: op.ok_or_else(|| ParseError::MissingField {
                field: "operator".to_string(),
                node_kind: "assignment_expression".to_string(),
            })?,
            left: Box::new(left.ok_or_else(|| ParseError::MissingField {
                field: "left".to_string(),
                node_kind: "assignment_expression".to_string(),
            })?),
            right: Box::new(right.ok_or_else(|| ParseError::MissingField {
                field: "right".to_string(),
                node_kind: "assignment_expression".to_string(),
            })?),
        })
    }

    /// Parse assignment operator
    fn parse_assign_op(&self, kind: &str) -> Option<BinOp> {
        match kind {
            "=" => Some(BinOp::Assign),
            "+=" => Some(BinOp::AddAssign),
            "-=" => Some(BinOp::SubAssign),
            "*=" => Some(BinOp::MulAssign),
            "/=" => Some(BinOp::DivAssign),
            "%=" => Some(BinOp::ModAssign),
            "&=" => Some(BinOp::BitAndAssign),
            "|=" => Some(BinOp::BitOrAssign),
            "^=" => Some(BinOp::BitXorAssign),
            "<<=" => Some(BinOp::ShlAssign),
            ">>=" => Some(BinOp::ShrAssign),
            _ => None,
        }
    }

    /// Parse conditional expression (ternary)
    pub(super) fn parse_conditional_expr(&self, node: Node, source: &str) -> ParseResult<CExpr> {
        let mut cond = None;
        let mut then_expr = None;
        let mut else_expr = None;

        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                let kind = child.kind();
                if kind == "?" || kind == ":" {
                    continue;
                }
                if cond.is_none() {
                    cond = Some(self.parse_expr(child, source)?);
                } else if then_expr.is_none() {
                    then_expr = Some(self.parse_expr(child, source)?);
                } else {
                    else_expr = Some(self.parse_expr(child, source)?);
                }
            }
        }

        Ok(CExpr::Conditional {
            cond: Box::new(cond.ok_or_else(|| ParseError::MissingField {
                field: "condition".to_string(),
                node_kind: "conditional_expression".to_string(),
            })?),
            then_expr: Box::new(then_expr.ok_or_else(|| ParseError::MissingField {
                field: "then".to_string(),
                node_kind: "conditional_expression".to_string(),
            })?),
            else_expr: Box::new(else_expr.ok_or_else(|| ParseError::MissingField {
                field: "else".to_string(),
                node_kind: "conditional_expression".to_string(),
            })?),
        })
    }
}
