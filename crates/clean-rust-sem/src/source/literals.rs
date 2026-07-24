// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

mod negation;

use super::{parser::Parser, SourceError};
use crate::types::{FloatType, IntType, RustType, UintType};
use crate::values::{BinOp, Value};

impl Parser {
    pub(super) fn parse_lit_expr(&self, expr: &syn::Expr) -> Result<Value, SourceError> {
        match expr {
            syn::Expr::Lit(expr_lit) => self.parse_lit(&expr_lit.lit),
            syn::Expr::Paren(paren) => self.parse_lit_expr(&paren.expr),
            syn::Expr::Group(group) => self.parse_lit_expr(&group.expr),
            // Negative integer/float literals: `-1`, `-3.14`
            syn::Expr::Unary(syn::ExprUnary {
                op: syn::UnOp::Neg(_),
                expr: inner,
                ..
            }) => self.parse_negated_lit_expr(inner),
            other => Err(Self::unsupported(
                "literal",
                format!("expected literal, found `{}`", Self::expr_kind(other)),
            )),
        }
    }

    pub(super) fn parse_lit(&self, lit: &syn::Lit) -> Result<Value, SourceError> {
        match lit {
            syn::Lit::Bool(boolean) => Ok(Value::Bool(boolean.value)),
            syn::Lit::Char(ch) => Ok(Value::Char(ch.value())),
            syn::Lit::Byte(byte) => Ok(Value::u8(byte.value())),
            syn::Lit::ByteStr(bytes) => Ok(Value::Array(
                bytes.value().into_iter().map(Value::u8).collect(),
            )),
            syn::Lit::Int(int) => self.parse_int_lit(int),
            syn::Lit::Float(float) => self.parse_float_lit(float),
            syn::Lit::Verbatim(_) => Err(Self::unsupported("literal", "verbatim literal")),
            syn::Lit::Str(s) => Ok(Value::Str(s.value())),
            // C-string literals `c"..."` (and the raw form `cr"..."`, which syn
            // also surfaces as `Lit::CStr`) denote a `&CStr`: a NUL-terminated
            // byte sequence with no interior NULs. We model this faithfully as a
            // `Value::Array` of `u8` scalars whose final element is the trailing
            // NUL, mirroring the byte-string `b"..."` representation above.
            //
            // SOUNDNESS: `syn::LitCStr::value()` returns a `CString`, which by
            // construction forbids interior NUL bytes (Rust rejects them in the
            // lexer); `into_bytes_with_nul()` yields the content bytes followed
            // by exactly one terminating NUL. This exactly matches C-string
            // semantics, so any well-formed `c"..."` literal lowers, and an
            // interior-NUL literal is unrepresentable and never reaches here.
            syn::Lit::CStr(cstr) => Ok(Value::Array(
                cstr.value()
                    .into_bytes_with_nul()
                    .into_iter()
                    .map(Value::u8)
                    .collect(),
            )),
            _ => Err(Self::unsupported("literal", "unsupported literal kind")),
        }
    }

    fn parse_int_lit(&self, int: &syn::LitInt) -> Result<Value, SourceError> {
        let suffix = int.suffix();
        let value = int.base10_digits().replace('_', "");
        if let Some(negated) = value.strip_prefix('-') {
            return self.parse_negated_int_value(negated, suffix);
        }
        match suffix {
            "" | "i8" | "i16" | "i32" | "i64" | "i128" | "isize" => {
                self.parse_signed_int_lit(&value, suffix)
            }
            "u8" | "u16" | "u32" | "u64" | "u128" | "usize" => {
                self.parse_unsigned_int_lit(&value, suffix)
            }
            other => Err(Self::unsupported(
                "integer literal",
                format!("suffix `{other}`"),
            )),
        }
    }

    fn parse_signed_int_lit(&self, value: &str, suffix: &str) -> Result<Value, SourceError> {
        let ty = match suffix {
            "" | "i32" => IntType::I32,
            "i8" => IntType::I8,
            "i16" => IntType::I16,
            "i64" => IntType::I64,
            "i128" => IntType::I128,
            "isize" => IntType::Isize,
            _ => unreachable!("parse_int_lit filters signed suffixes"),
        };
        let value = match ty {
            IntType::I8 => value
                .parse::<i8>()
                .map(i128::from)
                .map_err(Self::invalid_integer_literal),
            IntType::I16 => value
                .parse::<i16>()
                .map(i128::from)
                .map_err(Self::invalid_integer_literal),
            IntType::I32 => value
                .parse::<i32>()
                .map(i128::from)
                .map_err(Self::invalid_integer_literal),
            IntType::I64 => value
                .parse::<i64>()
                .map(i128::from)
                .map_err(Self::invalid_integer_literal),
            IntType::I128 => value.parse::<i128>().map_err(Self::invalid_integer_literal),
            IntType::Isize => {
                let parsed = value
                    .parse::<i128>()
                    .map_err(Self::invalid_integer_literal)?;
                if parsed > isize::MAX as i128 {
                    return Err(SourceError::Invalid {
                        context: "integer literal",
                        detail: format!(
                            "integer literal `{value}{suffix}` out of range for `isize`"
                        ),
                    });
                }
                Ok(parsed)
            }
        }?;
        Ok(Value::Int { value, ty })
    }

    fn parse_unsigned_int_lit(&self, value: &str, suffix: &str) -> Result<Value, SourceError> {
        let ty = match suffix {
            "u8" => UintType::U8,
            "u16" => UintType::U16,
            "u32" => UintType::U32,
            "u64" => UintType::U64,
            "u128" => UintType::U128,
            "usize" => UintType::Usize,
            _ => unreachable!("parse_int_lit filters unsigned suffixes"),
        };
        let value = match ty {
            UintType::U8 => value
                .parse::<u8>()
                .map(u128::from)
                .map_err(Self::invalid_integer_literal),
            UintType::U16 => value
                .parse::<u16>()
                .map(u128::from)
                .map_err(Self::invalid_integer_literal),
            UintType::U32 => value
                .parse::<u32>()
                .map(u128::from)
                .map_err(Self::invalid_integer_literal),
            UintType::U64 => value
                .parse::<u64>()
                .map(u128::from)
                .map_err(Self::invalid_integer_literal),
            UintType::U128 => value.parse::<u128>().map_err(Self::invalid_integer_literal),
            UintType::Usize => {
                let parsed = value
                    .parse::<u128>()
                    .map_err(Self::invalid_integer_literal)?;
                if parsed > usize::MAX as u128 {
                    return Err(SourceError::Invalid {
                        context: "integer literal",
                        detail: format!(
                            "integer literal `{value}{suffix}` out of range for `usize`"
                        ),
                    });
                }
                Ok(parsed)
            }
        }?;
        Ok(Value::Uint { value, ty })
    }

    fn parse_float_lit(&self, float: &syn::LitFloat) -> Result<Value, SourceError> {
        let value = float.base10_digits().replace('_', "");
        match float.suffix() {
            "" | "f64" => {
                value
                    .parse::<f64>()
                    .map(Value::f64)
                    .map_err(|err| SourceError::Invalid {
                        context: "float literal",
                        detail: err.to_string(),
                    })
            }
            "f32" => value
                .parse::<f32>()
                .map(Value::f32)
                .map_err(|err| SourceError::Invalid {
                    context: "float literal",
                    detail: err.to_string(),
                }),
            other => Err(Self::unsupported(
                "float literal",
                format!("suffix `{other}`"),
            )),
        }
    }

    pub(super) fn parse_binop(op: &syn::BinOp) -> Result<BinOp, SourceError> {
        match op {
            syn::BinOp::Add(_) => Ok(BinOp::Add),
            syn::BinOp::Sub(_) => Ok(BinOp::Sub),
            syn::BinOp::Mul(_) => Ok(BinOp::Mul),
            syn::BinOp::Div(_) => Ok(BinOp::Div),
            syn::BinOp::Rem(_) => Ok(BinOp::Rem),
            syn::BinOp::BitAnd(_) => Ok(BinOp::BitAnd),
            syn::BinOp::BitOr(_) => Ok(BinOp::BitOr),
            syn::BinOp::BitXor(_) => Ok(BinOp::BitXor),
            syn::BinOp::Shl(_) => Ok(BinOp::Shl),
            syn::BinOp::Shr(_) => Ok(BinOp::Shr),
            syn::BinOp::Eq(_) => Ok(BinOp::Eq),
            syn::BinOp::Ne(_) => Ok(BinOp::Ne),
            syn::BinOp::Lt(_) => Ok(BinOp::Lt),
            syn::BinOp::Le(_) => Ok(BinOp::Le),
            syn::BinOp::Gt(_) => Ok(BinOp::Gt),
            syn::BinOp::Ge(_) => Ok(BinOp::Ge),
            _ => Err(Self::unsupported(
                "binary operator",
                "unsupported binary operator",
            )),
        }
    }

    fn invalid_integer_literal(err: impl std::fmt::Display) -> SourceError {
        SourceError::Invalid {
            context: "integer literal",
            detail: err.to_string(),
        }
    }

    /// Resolve well-known associated constants on primitive types to literal values.
    ///
    /// Handles `MIN`, `MAX`, `BITS` for integer types and
    /// `INFINITY`, `NEG_INFINITY`, `NAN`, `MIN`, `MAX`, `EPSILON`, `MIN_POSITIVE` for floats.
    pub(super) fn try_resolve_associated_constant(path: &syn::Path) -> Option<Value> {
        if path.segments.len() != 2 {
            return None;
        }
        let ty_name = path.segments[0].ident.to_string();
        let const_name = path.segments[1].ident.to_string();
        Self::try_resolve_associated_constant_parts(&ty_name, &const_name)
    }

    pub(super) fn try_resolve_associated_constant_on_type(
        ty: &RustType,
        const_name: &str,
    ) -> Option<Value> {
        let ty_name = match ty {
            RustType::Uint(UintType::U8) => "u8",
            RustType::Uint(UintType::U16) => "u16",
            RustType::Uint(UintType::U32) => "u32",
            RustType::Uint(UintType::U64) => "u64",
            RustType::Uint(UintType::U128) => "u128",
            RustType::Uint(UintType::Usize) => "usize",
            RustType::Int(IntType::I8) => "i8",
            RustType::Int(IntType::I16) => "i16",
            RustType::Int(IntType::I32) => "i32",
            RustType::Int(IntType::I64) => "i64",
            RustType::Int(IntType::I128) => "i128",
            RustType::Int(IntType::Isize) => "isize",
            RustType::Float(FloatType::F32) => "f32",
            RustType::Float(FloatType::F64) => "f64",
            _ => return None,
        };
        Self::try_resolve_associated_constant_parts(ty_name, const_name)
    }

    fn try_resolve_associated_constant_parts(ty_name: &str, const_name: &str) -> Option<Value> {
        Self::try_resolve_unsigned_associated_constant(ty_name, const_name)
            .or_else(|| Self::try_resolve_signed_associated_constant(ty_name, const_name))
            .or_else(|| Self::try_resolve_float_associated_constant(ty_name, const_name))
    }

    fn try_resolve_unsigned_associated_constant(ty_name: &str, const_name: &str) -> Option<Value> {
        let ty = match ty_name {
            "u8" => UintType::U8,
            "u16" => UintType::U16,
            "u32" => UintType::U32,
            "u64" => UintType::U64,
            "u128" => UintType::U128,
            "usize" => UintType::Usize,
            _ => return None,
        };
        match const_name {
            "MIN" => Some(Value::Uint {
                value: Self::unsigned_min_value(ty),
                ty,
            }),
            "MAX" => Some(Value::Uint {
                value: Self::unsigned_max_value(ty),
                ty,
            }),
            "BITS" => Some(Value::Uint {
                value: Self::unsigned_bits_value(ty),
                ty: UintType::U32,
            }),
            _ => None,
        }
    }

    fn try_resolve_signed_associated_constant(ty_name: &str, const_name: &str) -> Option<Value> {
        let ty = match ty_name {
            "i8" => IntType::I8,
            "i16" => IntType::I16,
            "i32" => IntType::I32,
            "i64" => IntType::I64,
            "i128" => IntType::I128,
            "isize" => IntType::Isize,
            _ => return None,
        };
        match const_name {
            "MIN" => Some(Value::Int {
                value: Self::signed_min_value(ty),
                ty,
            }),
            "MAX" => Some(Value::Int {
                value: Self::signed_max_value(ty),
                ty,
            }),
            "BITS" => Some(Value::Uint {
                value: Self::signed_bits_value(ty),
                ty: UintType::U32,
            }),
            _ => None,
        }
    }

    fn try_resolve_float_associated_constant(ty_name: &str, const_name: &str) -> Option<Value> {
        let ty = match ty_name {
            "f32" => FloatType::F32,
            "f64" => FloatType::F64,
            _ => return None,
        };
        Self::float_constant_bits(ty, const_name).map(|bits| Value::Float { bits, ty })
    }

    fn unsigned_min_value(ty: UintType) -> u128 {
        match ty {
            UintType::U8 => u8::MIN as u128,
            UintType::U16 => u16::MIN as u128,
            UintType::U32 => u32::MIN as u128,
            UintType::U64 => u64::MIN as u128,
            UintType::U128 => u128::MIN,
            UintType::Usize => usize::MIN as u128,
        }
    }

    fn unsigned_max_value(ty: UintType) -> u128 {
        match ty {
            UintType::U8 => u8::MAX as u128,
            UintType::U16 => u16::MAX as u128,
            UintType::U32 => u32::MAX as u128,
            UintType::U64 => u64::MAX as u128,
            UintType::U128 => u128::MAX,
            UintType::Usize => usize::MAX as u128,
        }
    }

    fn unsigned_bits_value(ty: UintType) -> u128 {
        match ty {
            UintType::U8 => u8::BITS as u128,
            UintType::U16 => u16::BITS as u128,
            UintType::U32 => u32::BITS as u128,
            UintType::U64 => u64::BITS as u128,
            UintType::U128 => u128::BITS as u128,
            UintType::Usize => usize::BITS as u128,
        }
    }

    fn signed_min_value(ty: IntType) -> i128 {
        match ty {
            IntType::I8 => i8::MIN as i128,
            IntType::I16 => i16::MIN as i128,
            IntType::I32 => i32::MIN as i128,
            IntType::I64 => i64::MIN as i128,
            IntType::I128 => i128::MIN,
            IntType::Isize => isize::MIN as i128,
        }
    }

    fn signed_max_value(ty: IntType) -> i128 {
        match ty {
            IntType::I8 => i8::MAX as i128,
            IntType::I16 => i16::MAX as i128,
            IntType::I32 => i32::MAX as i128,
            IntType::I64 => i64::MAX as i128,
            IntType::I128 => i128::MAX,
            IntType::Isize => isize::MAX as i128,
        }
    }

    fn signed_bits_value(ty: IntType) -> u128 {
        match ty {
            IntType::I8 => i8::BITS as u128,
            IntType::I16 => i16::BITS as u128,
            IntType::I32 => i32::BITS as u128,
            IntType::I64 => i64::BITS as u128,
            IntType::I128 => i128::BITS as u128,
            IntType::Isize => isize::BITS as u128,
        }
    }

    fn float_constant_bits(ty: FloatType, const_name: &str) -> Option<u64> {
        match ty {
            FloatType::F32 => match const_name {
                "INFINITY" => Some(f32::INFINITY.to_bits() as u64),
                "NEG_INFINITY" => Some(f32::NEG_INFINITY.to_bits() as u64),
                "NAN" => Some(f32::NAN.to_bits() as u64),
                "MIN" => Some(f32::MIN.to_bits() as u64),
                "MAX" => Some(f32::MAX.to_bits() as u64),
                "EPSILON" => Some(f32::EPSILON.to_bits() as u64),
                "MIN_POSITIVE" => Some(f32::MIN_POSITIVE.to_bits() as u64),
                _ => None,
            },
            FloatType::F64 => match const_name {
                "INFINITY" => Some(f64::INFINITY.to_bits()),
                "NEG_INFINITY" => Some(f64::NEG_INFINITY.to_bits()),
                "NAN" => Some(f64::NAN.to_bits()),
                "MIN" => Some(f64::MIN.to_bits()),
                "MAX" => Some(f64::MAX.to_bits()),
                "EPSILON" => Some(f64::EPSILON.to_bits()),
                "MIN_POSITIVE" => Some(f64::MIN_POSITIVE.to_bits()),
                _ => None,
            },
        }
    }
}
