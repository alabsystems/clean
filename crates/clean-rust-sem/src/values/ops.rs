// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// Binary arithmetic operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

/// Unary operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum UnOp {
    /// Negation (-).
    Neg,
    /// Bitwise not (!).
    Not,
}

/// Dispatch a comparison operator on two `Ord` values.
fn eval_cmp_ord<T: Ord>(op: BinOp, l: &T, r: &T) -> Option<Value> {
    match op {
        BinOp::Eq => Some(Value::Bool(l == r)),
        BinOp::Ne => Some(Value::Bool(l != r)),
        BinOp::Lt => Some(Value::Bool(l < r)),
        BinOp::Le => Some(Value::Bool(l <= r)),
        BinOp::Gt => Some(Value::Bool(l > r)),
        BinOp::Ge => Some(Value::Bool(l >= r)),
        _ => None,
    }
}

/// Evaluate a binary operation.
pub fn eval_binop(op: BinOp, left: &Value, right: &Value) -> Option<Value> {
    match (left, right) {
        (Value::Uint { value: l, ty: ty_l }, Value::Uint { value: r, ty: ty_r })
            if ty_l == ty_r =>
        {
            if let Some(cmp) = eval_cmp_ord(op, l, r) {
                return Some(cmp);
            }
            let mask = uint_mask(*ty_l);
            let result = match op {
                BinOp::Add => l.wrapping_add(*r) & mask,
                BinOp::Sub => l.wrapping_sub(*r) & mask,
                BinOp::Mul => l.wrapping_mul(*r) & mask,
                BinOp::Div => l.checked_div(*r)?,
                BinOp::Rem => l.checked_rem(*r)?,
                BinOp::BitAnd => l & r,
                BinOp::BitOr => l | r,
                BinOp::BitXor => l ^ r,
                BinOp::Shl => (l << (r & uint_shift_mask(*ty_l))) & mask,
                BinOp::Shr => l >> (r & uint_shift_mask(*ty_l)),
                _ => return None,
            };
            Some(Value::Uint {
                value: result,
                ty: *ty_l,
            })
        }

        (Value::Int { value: l, ty: ty_l }, Value::Int { value: r, ty: ty_r }) if ty_l == ty_r => {
            if let Some(cmp) = eval_cmp_ord(op, l, r) {
                return Some(cmp);
            }
            let result = match op {
                BinOp::Add => truncate_signed(l.wrapping_add(*r), *ty_l),
                BinOp::Sub => truncate_signed(l.wrapping_sub(*r), *ty_l),
                BinOp::Mul => truncate_signed(l.wrapping_mul(*r), *ty_l),
                BinOp::Div => truncate_signed(l.checked_div(*r)?, *ty_l),
                BinOp::Rem => truncate_signed(l.checked_rem(*r)?, *ty_l),
                BinOp::BitAnd => truncate_signed(l & r, *ty_l),
                BinOp::BitOr => truncate_signed(l | r, *ty_l),
                BinOp::BitXor => truncate_signed(l ^ r, *ty_l),
                BinOp::Shl => truncate_signed(l << (r & int_shift_mask(*ty_l) as i128), *ty_l),
                BinOp::Shr => truncate_signed(l >> (r & int_shift_mask(*ty_l) as i128), *ty_l),
                _ => return None,
            };
            Some(Value::Int {
                value: result,
                ty: *ty_l,
            })
        }

        (Value::Bool(l), Value::Bool(r)) => match op {
            BinOp::BitAnd => Some(Value::Bool(*l && *r)),
            BinOp::BitOr => Some(Value::Bool(*l || *r)),
            BinOp::BitXor => Some(Value::Bool(*l ^ *r)),
            BinOp::Eq => Some(Value::Bool(l == r)),
            BinOp::Ne => Some(Value::Bool(l != r)),
            _ => None,
        },

        (Value::Float { bits: l, ty: ty_l }, Value::Float { bits: r, ty: ty_r })
            if ty_l == ty_r =>
        {
            eval_float_binop(op, *l, *r, *ty_l)
        }

        (Value::Str(l), Value::Str(r)) => eval_cmp_ord(op, l, r),

        _ => None,
    }
}

fn eval_float_binop(op: BinOp, l: u64, r: u64, ty: FloatType) -> Option<Value> {
    let lf = f64::from_bits(l);
    let rf = f64::from_bits(r);
    let result = match op {
        BinOp::Add => Value::Float {
            bits: (lf + rf).to_bits(),
            ty,
        },
        BinOp::Sub => Value::Float {
            bits: (lf - rf).to_bits(),
            ty,
        },
        BinOp::Mul => Value::Float {
            bits: (lf * rf).to_bits(),
            ty,
        },
        BinOp::Div => Value::Float {
            bits: (lf / rf).to_bits(),
            ty,
        },
        BinOp::Rem => Value::Float {
            bits: (lf % rf).to_bits(),
            ty,
        },
        BinOp::Eq => Value::Bool(lf == rf),
        BinOp::Ne => Value::Bool(lf != rf),
        BinOp::Lt => Value::Bool(lf < rf),
        BinOp::Le => Value::Bool(lf <= rf),
        BinOp::Gt => Value::Bool(lf > rf),
        BinOp::Ge => Value::Bool(lf >= rf),
        _ => return None,
    };
    Some(result)
}

/// Evaluate a unary operation.
pub fn eval_unop(op: UnOp, val: &Value) -> Option<Value> {
    match (op, val) {
        (UnOp::Not, Value::Bool(b)) => Some(Value::Bool(!b)),
        (UnOp::Not, Value::Uint { value, ty }) => Some(Value::Uint {
            value: !value & uint_mask(*ty),
            ty: *ty,
        }),
        (UnOp::Neg, Value::Int { value, ty }) => Some(Value::Int {
            value: truncate_signed(value.wrapping_neg(), *ty),
            ty: *ty,
        }),
        (UnOp::Neg, Value::Float { bits, ty }) => {
            let f = f64::from_bits(*bits);
            Some(Value::Float {
                bits: (-f).to_bits(),
                ty: *ty,
            })
        }
        _ => None,
    }
}

/// Mask for the bit-width of an unsigned integer type.
fn uint_mask(ty: UintType) -> u128 {
    match ty {
        UintType::U8 => 0xFF,
        UintType::U16 => 0xFFFF,
        UintType::U32 => 0xFFFF_FFFF,
        UintType::U64 | UintType::Usize => 0xFFFF_FFFF_FFFF_FFFF,
        UintType::U128 => u128::MAX,
    }
}

/// Shift amount mask for unsigned integer types.
fn uint_shift_mask(ty: UintType) -> u128 {
    match ty {
        UintType::U8 => 0x7,
        UintType::U16 => 0xF,
        UintType::U32 => 0x1F,
        UintType::U64 | UintType::Usize => 0x3F,
        UintType::U128 => 0x7F,
    }
}

/// Shift amount mask for signed integer types.
fn int_shift_mask(ty: IntType) -> u128 {
    match ty {
        IntType::I8 => 0x7,
        IntType::I16 => 0xF,
        IntType::I32 => 0x1F,
        IntType::I64 | IntType::Isize => 0x3F,
        IntType::I128 => 0x7F,
    }
}

/// Truncate an i128 value to the bit-width of a signed integer type.
fn truncate_signed(value: i128, ty: IntType) -> i128 {
    let (mask, sign_bit): (u128, u128) = match ty {
        IntType::I8 => (0xFF, 0x80),
        IntType::I16 => (0xFFFF, 0x8000),
        IntType::I32 => (0xFFFF_FFFF, 0x8000_0000),
        IntType::I64 | IntType::Isize => (0xFFFF_FFFF_FFFF_FFFF, 0x8000_0000_0000_0000),
        IntType::I128 => return value,
    };
    let truncated = (value as u128) & mask;
    if truncated & sign_bit != 0 {
        (truncated | !mask) as i128
    } else {
        truncated as i128
    }
}

/// Type cast operations.
pub fn cast_value(val: &Value, target: &RustType) -> Option<Value> {
    match (val, target) {
        (Value::Bool(b), RustType::Uint(ty)) => Some(Value::Uint {
            value: u128::from(*b),
            ty: *ty,
        }),
        (Value::Bool(b), RustType::Int(ty)) => Some(Value::Int {
            value: i128::from(*b),
            ty: *ty,
        }),
        (Value::Uint { value, .. }, RustType::Uint(ty)) => Some(Value::Uint {
            value: value & uint_mask(*ty),
            ty: *ty,
        }),
        (Value::Uint { value, .. }, RustType::Int(ty)) => Some(Value::Int {
            value: truncate_signed(*value as i128, *ty),
            ty: *ty,
        }),
        (Value::Int { value, .. }, RustType::Uint(ty)) => Some(Value::Uint {
            value: (*value as u128) & uint_mask(*ty),
            ty: *ty,
        }),
        (Value::Int { value, .. }, RustType::Int(ty)) => Some(Value::Int {
            value: truncate_signed(*value, *ty),
            ty: *ty,
        }),
        (Value::Uint { value, .. }, RustType::Float(ty)) => Some(Value::Float {
            bits: (*value as f64).to_bits(),
            ty: *ty,
        }),
        (Value::Int { value, .. }, RustType::Float(ty)) => Some(Value::Float {
            bits: (*value as f64).to_bits(),
            ty: *ty,
        }),
        (Value::Float { bits, .. }, RustType::Uint(ty)) => {
            let f = f64::from_bits(*bits);
            Some(Value::Uint {
                value: f as u128,
                ty: *ty,
            })
        }
        (Value::Float { bits, .. }, RustType::Int(ty)) => {
            let f = f64::from_bits(*bits);
            Some(Value::Int {
                value: f as i128,
                ty: *ty,
            })
        }
        (Value::Reference { addr, .. }, RustType::RawPtr { mutability, .. }) => {
            Some(Value::RawPtr {
                addr: *addr,
                mutability: *mutability,
                tag: None,
            })
        }
        _ => None,
    }
}
