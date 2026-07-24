// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{Parser, SourceError};
use crate::types::{FloatType, IntType};
use crate::values::Value;

impl Parser {
    pub(super) fn parse_negated_lit_expr(&self, expr: &syn::Expr) -> Result<Value, SourceError> {
        match expr {
            syn::Expr::Lit(expr_lit) => match &expr_lit.lit {
                syn::Lit::Int(int) => self.parse_negated_int_lit(int),
                syn::Lit::Float(float) => {
                    Self::negate_numeric_literal(self.parse_float_lit(float)?)
                }
                _ => Err(Self::unsupported(
                    "literal",
                    "negation of non-numeric literal",
                )),
            },
            syn::Expr::Paren(paren) => self.parse_negated_lit_expr(&paren.expr),
            syn::Expr::Group(group) => self.parse_negated_lit_expr(&group.expr),
            other => Self::negate_numeric_literal(self.parse_lit_expr(other)?),
        }
    }

    fn parse_negated_int_lit(&self, int: &syn::LitInt) -> Result<Value, SourceError> {
        let suffix = int.suffix();
        let value = int.base10_digits().replace('_', "");
        self.parse_negated_int_value(value.trim_start_matches('-'), suffix)
    }

    pub(super) fn parse_negated_int_value(
        &self,
        value: &str,
        suffix: &str,
    ) -> Result<Value, SourceError> {
        let literal = if suffix.is_empty() {
            value.to_string()
        } else {
            format!("{value}{suffix}")
        };

        let ty = match suffix {
            "" | "i8" | "i16" | "i32" | "i64" | "i128" | "isize" => Self::signed_int_type(suffix)
                .expect("signed suffixes should always resolve to an IntType"),
            "u8" | "u16" | "u32" | "u64" | "u128" | "usize" => {
                return Err(SourceError::Invalid {
                    context: "literal",
                    detail: format!("unsigned integer literal `{literal}` cannot be negated"),
                });
            }
            other => {
                return Err(Self::unsupported(
                    "integer literal",
                    format!("suffix `{other}`"),
                ))
            }
        };

        let magnitude = value
            .parse::<u128>()
            .map_err(Self::invalid_integer_literal)?;
        let min_magnitude = Self::signed_min_value(ty).unsigned_abs();
        if magnitude > min_magnitude {
            return Err(SourceError::Invalid {
                context: "integer literal",
                detail: format!(
                    "negative integer literal `-{literal}` out of range for `{}`",
                    Self::signed_int_name(ty)
                ),
            });
        }

        if magnitude == min_magnitude {
            return Ok(Value::Int {
                value: Self::signed_min_value(ty),
                ty,
            });
        }

        let magnitude = i128::try_from(magnitude).expect("smaller-than-min magnitude fits in i128");
        Ok(Value::Int {
            value: -magnitude,
            ty,
        })
    }

    fn negate_numeric_literal(value: Value) -> Result<Value, SourceError> {
        match value {
            Value::Int { value, ty } => value
                .checked_neg()
                .map(|negated| Value::Int { value: negated, ty })
                .ok_or_else(|| SourceError::Invalid {
                    context: "literal",
                    detail: format!("negation overflow on integer literal {value}"),
                }),
            Value::Uint { .. } => Err(SourceError::Invalid {
                context: "literal",
                detail: "unsigned integer literal cannot be negated".to_string(),
            }),
            Value::Float { bits, ty } => {
                let negated_bits = match ty {
                    FloatType::F32 => {
                        let f = f32::from_bits(bits as u32);
                        (-f).to_bits() as u64
                    }
                    FloatType::F64 => {
                        let f = f64::from_bits(bits);
                        (-f).to_bits()
                    }
                };
                Ok(Value::Float {
                    bits: negated_bits,
                    ty,
                })
            }
            _ => Err(Self::unsupported(
                "literal",
                "negation of non-numeric literal",
            )),
        }
    }

    fn signed_int_type(suffix: &str) -> Option<IntType> {
        match suffix {
            "" | "i32" => Some(IntType::I32),
            "i8" => Some(IntType::I8),
            "i16" => Some(IntType::I16),
            "i64" => Some(IntType::I64),
            "i128" => Some(IntType::I128),
            "isize" => Some(IntType::Isize),
            _ => None,
        }
    }

    fn signed_int_name(ty: IntType) -> &'static str {
        match ty {
            IntType::I8 => "i8",
            IntType::I16 => "i16",
            IntType::I32 => "i32",
            IntType::I64 => "i64",
            IntType::I128 => "i128",
            IntType::Isize => "isize",
        }
    }
}
