// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Native function registry and dynamic value bridge for the Lean 4 runtime.
//!
//! This module provides a small FFI dispatch layer that maps Lean runtime
//! native names such as `String.append` or `Array.get` to Rust closures over a
//! dynamic [`Value`] domain.

use std::any::Any;
use std::collections::HashMap;
use std::fmt;
use std::io::{self, BufRead, Write};
use std::sync::Arc;

use thiserror::Error;

/// Errors returned by native function lookup and execution.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum FfiError {
    /// A requested native name is not present in the registry.
    #[error("unknown native function `{name}`")]
    UnknownFunction { name: String },

    /// An argument had the wrong runtime type.
    #[error(
        "type mismatch in `{function}` at argument {index}: expected {expected}, found {found}"
    )]
    TypeMismatch {
        function: String,
        index: usize,
        expected: &'static str,
        found: &'static str,
    },

    /// A native received the wrong number of arguments.
    #[error("arity mismatch in `{function}`: expected {expected}, got {got}")]
    ArityMismatch {
        function: String,
        expected: usize,
        got: usize,
    },

    /// Native execution failed for a value-level reason or host I/O failure.
    #[error("native execution failed in `{function}`: {message}")]
    ExecutionFailed { function: String, message: String },

    /// The exact kernel result of an arithmetic native is not representable in
    /// the machine-width [`Value`] (`u64` for `Nat`, `i64` for `Int`).
    ///
    /// The kernel treats `Nat`/`Int` as unbounded bignums, so emitting a
    /// wrapped/truncated value would be a wrong `#eval` result. The native
    /// declines here instead, mirroring the const-fold `None` decline in
    /// `clean-compiler/src/const_fold_ext2.rs::fold_arith`.
    #[error("arithmetic overflow in `{function}`: exact result is not representable")]
    ArithmeticOverflow { function: String },
}

#[derive(Clone)]
struct SharedOpaque(Arc<dyn Any + Send + Sync>);

/// Dynamic value domain used by the native bridge.
#[non_exhaustive]
pub enum Value {
    Nat(u64),
    Int(i64),
    String(String),
    Float(f64),
    Array(Vec<Value>),
    Bool(bool),
    /// A Unicode scalar value (`Char` in Lean). Stored as a raw `u32` code
    /// point; values are always valid scalar values because constructors
    /// validate via [`char::from_u32`].
    Char(u32),
    Unit,
    Opaque(Box<dyn Any + Send + Sync>),
}

impl Value {
    /// Construct a clone-friendly opaque value.
    #[must_use]
    pub fn opaque<T>(value: T) -> Self
    where
        T: Any + Send + Sync,
    {
        Self::Opaque(Box::new(SharedOpaque(Arc::new(value))))
    }
}

impl Clone for Value {
    fn clone(&self) -> Self {
        match self {
            Self::Nat(value) => Self::Nat(*value),
            Self::Int(value) => Self::Int(*value),
            Self::String(value) => Self::String(value.clone()),
            Self::Float(value) => Self::Float(*value),
            Self::Array(values) => Self::Array(values.iter().map(Self::clone).collect()),
            Self::Bool(value) => Self::Bool(*value),
            Self::Char(value) => Self::Char(*value),
            Self::Unit => Self::Unit,
            Self::Opaque(value) => match clone_opaque_box(value.as_ref()) {
                Some(cloned) => Self::Opaque(cloned),
                // Opaque values not created via Value::opaque fall back to Unit.
                // Use Value::opaque() for clonable opaques.
                None => Self::Unit,
            },
        }
    }
}

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Nat(value) => f.debug_tuple("Nat").field(value).finish(),
            Self::Int(value) => f.debug_tuple("Int").field(value).finish(),
            Self::String(value) => f.debug_tuple("String").field(value).finish(),
            Self::Float(value) => f.debug_tuple("Float").field(value).finish(),
            Self::Array(values) => f.debug_tuple("Array").field(values).finish(),
            Self::Bool(value) => f.debug_tuple("Bool").field(value).finish(),
            Self::Char(value) => f.debug_tuple("Char").field(value).finish(),
            Self::Unit => f.write_str("Unit"),
            Self::Opaque(_) => f.write_str("Opaque(..)"),
        }
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Nat(lhs), Self::Nat(rhs)) => lhs == rhs,
            (Self::Int(lhs), Self::Int(rhs)) => lhs == rhs,
            (Self::String(lhs), Self::String(rhs)) => lhs == rhs,
            (Self::Float(lhs), Self::Float(rhs)) => lhs == rhs,
            (Self::Array(lhs), Self::Array(rhs)) => lhs == rhs,
            (Self::Bool(lhs), Self::Bool(rhs)) => lhs == rhs,
            (Self::Char(lhs), Self::Char(rhs)) => lhs == rhs,
            (Self::Unit, Self::Unit) => true,
            (Self::Opaque(lhs), Self::Opaque(rhs)) => opaque_eq(lhs.as_ref(), rhs.as_ref()),
            _ => false,
        }
    }
}

/// Native function callable from the bridge registry.
pub type NativeFn = Arc<dyn Fn(&[Value]) -> Result<Value, FfiError> + Send + Sync>;

/// Registry of runtime native functions.
#[derive(Default)]
pub struct FfiBridge {
    registry: HashMap<String, NativeFn>,
}

impl FfiBridge {
    /// Create a bridge with all built-in native functions pre-registered.
    #[must_use]
    pub fn new() -> Self {
        let mut bridge = Self::default();
        bridge.register_builtins();
        bridge
    }

    /// Register or replace a native function.
    pub fn register_native(&mut self, name: &str, func: NativeFn) {
        self.registry.insert(name.to_owned(), func);
    }

    /// Call a registered native function by name.
    pub fn call_native(&self, name: &str, args: &[Value]) -> Result<Value, FfiError> {
        let native = self
            .registry
            .get(name)
            .ok_or_else(|| FfiError::UnknownFunction {
                name: name.to_owned(),
            })?;
        native(args)
    }

    /// Return the registered native names in sorted order.
    #[must_use]
    pub fn registered_names(&self) -> Vec<String> {
        let mut names = self.registry.keys().cloned().collect::<Vec<_>>();
        names.sort_unstable();
        names
    }

    fn register_builtins(&mut self) {
        self.register_native("String.mk", native(builtin_string_mk));
        self.register_native("String.append", native(builtin_string_append));
        self.register_native("String.length", native(builtin_string_length));
        self.register_native("String.push", native(builtin_string_push));
        self.register_native("String.eq", native(builtin_string_eq));
        self.register_native("Array.mk", native(builtin_array_mk));
        self.register_native("Array.push", native(builtin_array_push));
        self.register_native("Array.get", native(builtin_array_get));
        self.register_native("Array.size", native(builtin_array_size));
        self.register_native("Array.set", native(builtin_array_set));
        self.register_native("Array.contains", native(builtin_array_contains));
        self.register_native("Array.eq", native(builtin_array_eq));
        self.register_native("Bool.eq", native(builtin_bool_eq));
        self.register_native("Char.eq", native(builtin_char_eq));
        self.register_native("IO.println", native(builtin_io_println));
        self.register_native("IO.getLine", native(builtin_io_get_line));
        self.register_native("IO.getEnv", native(builtin_io_get_env));
        self.register_native("Float.add", native(builtin_float_add));
        self.register_native("Float.mul", native(builtin_float_mul));
        self.register_native("Float.div", native(builtin_float_div));
        self.register_native("Float.toString", native(builtin_float_to_string));
        self.register_arith_builtins();
    }

    /// Register `Nat`/`Int` arithmetic, comparison, and bitwise natives.
    ///
    /// Every native here is observationally equivalent to the kernel reducer
    /// (`clean-kernel/src/env/native_reducers_arith.rs`) and the authoritative
    /// const-fold spec (`clean-compiler/src/const_fold_ext2.rs::fold_arith` /
    /// `fold_cmp`): each op computes the EXACT value the kernel would reduce to
    /// or returns a typed [`FfiError`]. The kernel treats `Nat`/`Int` as
    /// unbounded bignums, so the `u64`/`i64`-backed [`Value`] declines (errors)
    /// rather than wrap whenever the true result is not representable.
    fn register_arith_builtins(&mut self) {
        // Nat arithmetic.
        self.register_native("Nat.add", native(builtin_nat_add));
        self.register_native("Nat.sub", native(builtin_nat_sub));
        self.register_native("Nat.mul", native(builtin_nat_mul));
        self.register_native("Nat.div", native(builtin_nat_div));
        self.register_native("Nat.mod", native(builtin_nat_mod));
        self.register_native("Nat.pow", native(builtin_nat_pow));
        // Nat comparisons.
        self.register_native("Nat.beq", native(builtin_nat_beq));
        self.register_native("Nat.blt", native(builtin_nat_blt));
        self.register_native("Nat.ble", native(builtin_nat_ble));
        self.register_native("Nat.bge", native(builtin_nat_bge));
        self.register_native("Nat.bgt", native(builtin_nat_bgt));
        // Nat bitwise (exact on non-negative bignums that fit in `u64`).
        self.register_native("Nat.land", native(builtin_nat_land));
        self.register_native("Nat.lor", native(builtin_nat_lor));
        self.register_native("Nat.xor", native(builtin_nat_xor));
        // Int arithmetic.
        self.register_native("Int.add", native(builtin_int_add));
        self.register_native("Int.sub", native(builtin_int_sub));
        self.register_native("Int.mul", native(builtin_int_mul));
        self.register_native("Int.div", native(builtin_int_div));
        self.register_native("Int.mod", native(builtin_int_mod));
        // Int comparisons.
        self.register_native("Int.beq", native(builtin_int_beq));
        self.register_native("Int.blt", native(builtin_int_blt));
        self.register_native("Int.ble", native(builtin_int_ble));
        self.register_native("Int.bge", native(builtin_int_bge));
        self.register_native("Int.bgt", native(builtin_int_bgt));
    }
}

fn native(func: fn(&[Value]) -> Result<Value, FfiError>) -> NativeFn {
    Arc::new(func)
}

fn builtin_string_mk(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "String.mk";
    expect_arity(NAME, args, 1)?;
    let values = expect_array(NAME, args, 0)?;
    let bytes = values
        .iter()
        .enumerate()
        .map(|(index, value)| match value {
            Value::Nat(byte) => u8::try_from(*byte).map_err(|_| {
                execution_failed(
                    NAME,
                    format!("byte value out of range at index {index}: {byte}"),
                )
            }),
            other => Err(type_mismatch(NAME, index, "Nat", other)),
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Value::String(String::from_utf8_lossy(&bytes).into_owned()))
}

fn builtin_string_append(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "String.append";
    expect_arity(NAME, args, 2)?;
    let lhs = expect_string(NAME, args, 0)?;
    let rhs = expect_string(NAME, args, 1)?;
    Ok(Value::String(format!("{lhs}{rhs}")))
}

fn builtin_string_length(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "String.length";
    expect_arity(NAME, args, 1)?;
    Ok(Value::Nat(expect_string(NAME, args, 0)?.len() as u64))
}

fn builtin_string_push(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "String.push";
    expect_arity(NAME, args, 2)?;
    let mut value = expect_string(NAME, args, 0)?.to_owned();
    // Accept either a `Char` value or a raw `Nat` code point. Lean's
    // `String.push : String -> Char -> String` passes a `Char`, but callers
    // that still box the code point as a `Nat` remain supported.
    let code = match args.get(1) {
        Some(Value::Char(code)) => *code,
        Some(Value::Nat(code)) => u32::try_from(*code)
            .map_err(|_| execution_failed(NAME, format!("char code out of range: {code}")))?,
        Some(other) => return Err(type_mismatch(NAME, 1, "Char", other)),
        None => {
            return Err(FfiError::ArityMismatch {
                function: NAME.to_owned(),
                expected: 2,
                got: args.len(),
            })
        }
    };
    let ch = char::from_u32(code)
        .ok_or_else(|| execution_failed(NAME, format!("invalid Unicode scalar value: {code}")))?;
    value.push(ch);
    Ok(Value::String(value))
}

fn builtin_string_eq(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "String.eq";
    expect_arity(NAME, args, 2)?;
    let lhs = expect_string(NAME, args, 0)?;
    let rhs = expect_string(NAME, args, 1)?;
    Ok(Value::Bool(lhs == rhs))
}

fn builtin_array_mk(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "Array.mk";
    expect_arity(NAME, args, 0)?;
    Ok(Value::Array(Vec::new()))
}

fn builtin_array_push(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "Array.push";
    expect_arity(NAME, args, 2)?;
    let mut values = clone_values(expect_array(NAME, args, 0)?, NAME)?;
    values.push(try_clone_value(&args[1], NAME)?);
    Ok(Value::Array(values))
}

fn builtin_array_get(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "Array.get";
    expect_arity(NAME, args, 2)?;
    let values = expect_array(NAME, args, 0)?;
    let index = nat_to_index(expect_nat(NAME, args, 1)?, NAME)?;
    let value = values
        .get(index)
        .ok_or_else(|| execution_failed(NAME, format!("index out of bounds: {index}")))?;
    try_clone_value(value, NAME)
}

fn builtin_array_size(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "Array.size";
    expect_arity(NAME, args, 1)?;
    Ok(Value::Nat(expect_array(NAME, args, 0)?.len() as u64))
}

fn builtin_array_set(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "Array.set";
    expect_arity(NAME, args, 3)?;
    let mut values = clone_values(expect_array(NAME, args, 0)?, NAME)?;
    let index = nat_to_index(expect_nat(NAME, args, 1)?, NAME)?;
    let slot = values
        .get_mut(index)
        .ok_or_else(|| execution_failed(NAME, format!("index out of bounds: {index}")))?;
    *slot = try_clone_value(&args[2], NAME)?;
    Ok(Value::Array(values))
}

fn builtin_array_contains(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "Array.contains";
    expect_arity(NAME, args, 2)?;
    let values = expect_array(NAME, args, 0)?;
    let needle = &args[1];
    Ok(Value::Bool(values.iter().any(|value| value == needle)))
}

fn builtin_array_eq(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "Array.eq";
    expect_arity(NAME, args, 2)?;
    let lhs = expect_array(NAME, args, 0)?;
    let rhs = expect_array(NAME, args, 1)?;
    Ok(Value::Bool(lhs == rhs))
}

fn builtin_bool_eq(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "Bool.eq";
    expect_arity(NAME, args, 2)?;
    let lhs = expect_bool(NAME, args, 0)?;
    let rhs = expect_bool(NAME, args, 1)?;
    Ok(Value::Bool(lhs == rhs))
}

fn builtin_char_eq(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "Char.eq";
    expect_arity(NAME, args, 2)?;
    let lhs = expect_char(NAME, args, 0)?;
    let rhs = expect_char(NAME, args, 1)?;
    Ok(Value::Bool(lhs == rhs))
}

fn builtin_io_println(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "IO.println";
    expect_arity(NAME, args, 1)?;
    let mut stdout = io::stdout().lock();
    writeln!(stdout, "{}", expect_string(NAME, args, 0)?)
        .map_err(|error| execution_failed(NAME, error.to_string()))?;
    Ok(Value::Unit)
}

fn builtin_io_get_line(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "IO.getLine";
    expect_arity(NAME, args, 0)?;
    let stdin = io::stdin();
    let mut handle = stdin.lock();
    let mut line = String::new();
    handle
        .read_line(&mut line)
        .map_err(|error| execution_failed(NAME, error.to_string()))?;
    if line.ends_with('\n') {
        line.pop();
        if line.ends_with('\r') {
            line.pop();
        }
    }
    Ok(Value::String(line))
}

fn builtin_io_get_env(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "IO.getEnv";
    expect_arity(NAME, args, 1)?;
    let name = expect_string(NAME, args, 0)?;
    let value = std::env::var_os(name)
        .map(|raw| raw.to_string_lossy().into_owned())
        .unwrap_or_default();
    Ok(Value::String(value))
}

fn builtin_float_add(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "Float.add";
    expect_arity(NAME, args, 2)?;
    Ok(Value::Float(
        expect_float(NAME, args, 0)? + expect_float(NAME, args, 1)?,
    ))
}

fn builtin_float_mul(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "Float.mul";
    expect_arity(NAME, args, 2)?;
    Ok(Value::Float(
        expect_float(NAME, args, 0)? * expect_float(NAME, args, 1)?,
    ))
}

fn builtin_float_div(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "Float.div";
    expect_arity(NAME, args, 2)?;
    let lhs = expect_float(NAME, args, 0)?;
    let rhs = expect_float(NAME, args, 1)?;
    if rhs == 0.0 {
        return Err(execution_failed(NAME, "division by zero".to_owned()));
    }
    Ok(Value::Float(lhs / rhs))
}

fn builtin_float_to_string(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "Float.toString";
    expect_arity(NAME, args, 1)?;
    Ok(Value::String(expect_float(NAME, args, 0)?.to_string()))
}

// ---------------------------------------------------------------------------
// Nat / Int arithmetic natives
//
// AUTHORITATIVE SEMANTICS are mirrored op-for-op from
// `clean-compiler/src/const_fold_ext2.rs` (`fold_arith` / `fold_cmp`) and the
// kernel reducers in `clean-kernel/src/env/native_reducers_arith.rs`, both of
// which match the Lean 4 kernel `reduce_nat` / `reduce_int`. The kernel treats
// `Nat`/`Int` as UNBOUNDED bignums; the machine-width `Value` (`u64`/`i64`)
// must produce the EXACT kernel value or DECLINE with a typed `FfiError`. A
// wrapped/truncated value would be a wrong `#eval` result (a miscompilation).
// ---------------------------------------------------------------------------

/// `Nat.add : Nat → Nat → Nat`. Exact addition; declines on `u64` overflow
/// because the kernel would produce a bignum (`fold_arith` uses `checked_add`).
fn builtin_nat_add(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "Nat.add";
    expect_arity(NAME, args, 2)?;
    let lhs = expect_nat(NAME, args, 0)?;
    let rhs = expect_nat(NAME, args, 1)?;
    lhs.checked_add(rhs)
        .map(Value::Nat)
        .ok_or_else(|| arithmetic_overflow(NAME))
}

/// `Nat.sub : Nat → Nat → Nat`. Truncated (floored-at-0) subtraction; total,
/// never errors (`fold_arith` uses `saturating_sub`).
fn builtin_nat_sub(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "Nat.sub";
    expect_arity(NAME, args, 2)?;
    let lhs = expect_nat(NAME, args, 0)?;
    let rhs = expect_nat(NAME, args, 1)?;
    Ok(Value::Nat(lhs.saturating_sub(rhs)))
}

/// `Nat.mul : Nat → Nat → Nat`. Exact; declines on `u64` overflow
/// (`fold_arith` uses `checked_mul`).
fn builtin_nat_mul(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "Nat.mul";
    expect_arity(NAME, args, 2)?;
    let lhs = expect_nat(NAME, args, 0)?;
    let rhs = expect_nat(NAME, args, 1)?;
    lhs.checked_mul(rhs)
        .map(Value::Nat)
        .ok_or_else(|| arithmetic_overflow(NAME))
}

/// `Nat.div : Nat → Nat → Nat`. Total: division by zero yields `0`
/// (`fold_arith`: `checked_div(rhs).unwrap_or(0)`).
fn builtin_nat_div(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "Nat.div";
    expect_arity(NAME, args, 2)?;
    let lhs = expect_nat(NAME, args, 0)?;
    let rhs = expect_nat(NAME, args, 1)?;
    Ok(Value::Nat(lhs.checked_div(rhs).unwrap_or(0)))
}

/// `Nat.mod : Nat → Nat → Nat`. Total: modulus by zero yields the dividend
/// (`fold_arith`: `if rhs == 0 { lhs } else { lhs % rhs }`).
fn builtin_nat_mod(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "Nat.mod";
    expect_arity(NAME, args, 2)?;
    let lhs = expect_nat(NAME, args, 0)?;
    let rhs = expect_nat(NAME, args, 1)?;
    Ok(Value::Nat(if rhs == 0 { lhs } else { lhs % rhs }))
}

/// `Nat.pow : Nat → Nat → Nat`. Exact; the exponent must fit in `u32` and the
/// result must fit in `u64`, else declines
/// (`fold_arith`: `u32::try_from(rhs).ok().and_then(|e| lhs.checked_pow(e))`).
fn builtin_nat_pow(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "Nat.pow";
    expect_arity(NAME, args, 2)?;
    let lhs = expect_nat(NAME, args, 0)?;
    let rhs = expect_nat(NAME, args, 1)?;
    u32::try_from(rhs)
        .ok()
        .and_then(|exp| lhs.checked_pow(exp))
        .map(Value::Nat)
        .ok_or_else(|| arithmetic_overflow(NAME))
}

/// `Nat.beq : Nat → Nat → Bool` (`fold_cmp`: `lhs == rhs`).
fn builtin_nat_beq(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "Nat.beq";
    expect_arity(NAME, args, 2)?;
    let lhs = expect_nat(NAME, args, 0)?;
    let rhs = expect_nat(NAME, args, 1)?;
    Ok(Value::Bool(lhs == rhs))
}

/// `Nat.blt : Nat → Nat → Bool` (`fold_cmp`: `lhs < rhs`).
fn builtin_nat_blt(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "Nat.blt";
    expect_arity(NAME, args, 2)?;
    let lhs = expect_nat(NAME, args, 0)?;
    let rhs = expect_nat(NAME, args, 1)?;
    Ok(Value::Bool(lhs < rhs))
}

/// `Nat.ble : Nat → Nat → Bool` (`fold_cmp`: `lhs <= rhs`).
fn builtin_nat_ble(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "Nat.ble";
    expect_arity(NAME, args, 2)?;
    let lhs = expect_nat(NAME, args, 0)?;
    let rhs = expect_nat(NAME, args, 1)?;
    Ok(Value::Bool(lhs <= rhs))
}

/// `Nat.bge : Nat → Nat → Bool` (`fold_cmp`: `lhs >= rhs`).
fn builtin_nat_bge(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "Nat.bge";
    expect_arity(NAME, args, 2)?;
    let lhs = expect_nat(NAME, args, 0)?;
    let rhs = expect_nat(NAME, args, 1)?;
    Ok(Value::Bool(lhs >= rhs))
}

/// `Nat.bgt : Nat → Nat → Bool` (`fold_cmp`: `lhs > rhs`).
fn builtin_nat_bgt(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "Nat.bgt";
    expect_arity(NAME, args, 2)?;
    let lhs = expect_nat(NAME, args, 0)?;
    let rhs = expect_nat(NAME, args, 1)?;
    Ok(Value::Bool(lhs > rhs))
}

/// `Nat.land : Nat → Nat → Nat`. Bitwise AND; exact because non-negative
/// operands that fit in `u64` produce a result that also fits (`fold_arith`:
/// `lhs & rhs`).
fn builtin_nat_land(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "Nat.land";
    expect_arity(NAME, args, 2)?;
    let lhs = expect_nat(NAME, args, 0)?;
    let rhs = expect_nat(NAME, args, 1)?;
    Ok(Value::Nat(lhs & rhs))
}

/// `Nat.lor : Nat → Nat → Nat`. Bitwise OR (`fold_arith`: `lhs | rhs`).
fn builtin_nat_lor(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "Nat.lor";
    expect_arity(NAME, args, 2)?;
    let lhs = expect_nat(NAME, args, 0)?;
    let rhs = expect_nat(NAME, args, 1)?;
    Ok(Value::Nat(lhs | rhs))
}

/// `Nat.xor : Nat → Nat → Nat`. Bitwise XOR; registered under the Lean name
/// `Nat.xor` (`fold_arith`: `lhs ^ rhs`).
fn builtin_nat_xor(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "Nat.xor";
    expect_arity(NAME, args, 2)?;
    let lhs = expect_nat(NAME, args, 0)?;
    let rhs = expect_nat(NAME, args, 1)?;
    Ok(Value::Nat(lhs ^ rhs))
}

/// `Int.add : Int → Int → Int`. Exact; declines on `i64` overflow
/// (`fold_arith`: `(lhs as i64).checked_add(rhs as i64)?`).
fn builtin_int_add(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "Int.add";
    expect_arity(NAME, args, 2)?;
    let lhs = expect_int(NAME, args, 0)?;
    let rhs = expect_int(NAME, args, 1)?;
    lhs.checked_add(rhs)
        .map(Value::Int)
        .ok_or_else(|| arithmetic_overflow(NAME))
}

/// `Int.sub : Int → Int → Int`. Exact; declines on `i64` overflow
/// (`fold_arith`: `(lhs as i64).checked_sub(rhs as i64)?`).
fn builtin_int_sub(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "Int.sub";
    expect_arity(NAME, args, 2)?;
    let lhs = expect_int(NAME, args, 0)?;
    let rhs = expect_int(NAME, args, 1)?;
    lhs.checked_sub(rhs)
        .map(Value::Int)
        .ok_or_else(|| arithmetic_overflow(NAME))
}

/// `Int.mul : Int → Int → Int`. Exact; declines on `i64` overflow
/// (`fold_arith`: `(lhs as i64).checked_mul(rhs as i64)?`).
fn builtin_int_mul(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "Int.mul";
    expect_arity(NAME, args, 2)?;
    let lhs = expect_int(NAME, args, 0)?;
    let rhs = expect_int(NAME, args, 1)?;
    lhs.checked_mul(rhs)
        .map(Value::Int)
        .ok_or_else(|| arithmetic_overflow(NAME))
}

/// `Int.div : Int → Int → Int`. Division by zero yields `0` (Lean convention);
/// otherwise truncating division, declining the `i64::MIN / -1` overflow
/// (`fold_arith`: `Int.div if rhs != 0 => (lhs as i64).checked_div(rhs as i64)?`,
/// and a 0 divisor is left untouched at the IR level — which for a closed
/// `#eval` reduces to the Lean total result `0`).
fn builtin_int_div(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "Int.div";
    expect_arity(NAME, args, 2)?;
    let lhs = expect_int(NAME, args, 0)?;
    let rhs = expect_int(NAME, args, 1)?;
    if rhs == 0 {
        return Ok(Value::Int(0));
    }
    lhs.checked_div(rhs)
        .map(Value::Int)
        .ok_or_else(|| arithmetic_overflow(NAME))
}

/// `Int.mod : Int → Int → Int`. Modulus by zero yields `0` (Lean convention);
/// otherwise truncating remainder, declining the `i64::MIN % -1` overflow
/// (`fold_arith`: `Int.mod if rhs != 0 => (lhs as i64).checked_rem(rhs as i64)?`).
fn builtin_int_mod(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "Int.mod";
    expect_arity(NAME, args, 2)?;
    let lhs = expect_int(NAME, args, 0)?;
    let rhs = expect_int(NAME, args, 1)?;
    if rhs == 0 {
        return Ok(Value::Int(0));
    }
    lhs.checked_rem(rhs)
        .map(Value::Int)
        .ok_or_else(|| arithmetic_overflow(NAME))
}

/// `Int.beq : Int → Int → Bool` (`fold_cmp`: `(lhs as i64) == (rhs as i64)`).
fn builtin_int_beq(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "Int.beq";
    expect_arity(NAME, args, 2)?;
    let lhs = expect_int(NAME, args, 0)?;
    let rhs = expect_int(NAME, args, 1)?;
    Ok(Value::Bool(lhs == rhs))
}

/// `Int.blt : Int → Int → Bool` (`fold_cmp`: `(lhs as i64) < (rhs as i64)`).
fn builtin_int_blt(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "Int.blt";
    expect_arity(NAME, args, 2)?;
    let lhs = expect_int(NAME, args, 0)?;
    let rhs = expect_int(NAME, args, 1)?;
    Ok(Value::Bool(lhs < rhs))
}

/// `Int.ble : Int → Int → Bool` (`fold_cmp`: `(lhs as i64) <= (rhs as i64)`).
fn builtin_int_ble(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "Int.ble";
    expect_arity(NAME, args, 2)?;
    let lhs = expect_int(NAME, args, 0)?;
    let rhs = expect_int(NAME, args, 1)?;
    Ok(Value::Bool(lhs <= rhs))
}

/// `Int.bge : Int → Int → Bool` (`fold_cmp`: `(lhs as i64) >= (rhs as i64)`).
fn builtin_int_bge(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "Int.bge";
    expect_arity(NAME, args, 2)?;
    let lhs = expect_int(NAME, args, 0)?;
    let rhs = expect_int(NAME, args, 1)?;
    Ok(Value::Bool(lhs >= rhs))
}

/// `Int.bgt : Int → Int → Bool` (`fold_cmp`: `(lhs as i64) > (rhs as i64)`).
fn builtin_int_bgt(args: &[Value]) -> Result<Value, FfiError> {
    const NAME: &str = "Int.bgt";
    expect_arity(NAME, args, 2)?;
    let lhs = expect_int(NAME, args, 0)?;
    let rhs = expect_int(NAME, args, 1)?;
    Ok(Value::Bool(lhs > rhs))
}

fn clone_values(values: &[Value], function: &str) -> Result<Vec<Value>, FfiError> {
    values
        .iter()
        .map(|value| try_clone_value(value, function))
        .collect()
}

fn try_clone_value(value: &Value, function: &str) -> Result<Value, FfiError> {
    match value {
        Value::Nat(inner) => Ok(Value::Nat(*inner)),
        Value::Int(inner) => Ok(Value::Int(*inner)),
        Value::String(inner) => Ok(Value::String(inner.clone())),
        Value::Float(inner) => Ok(Value::Float(*inner)),
        Value::Array(inner) => clone_values(inner, function).map(Value::Array),
        Value::Bool(inner) => Ok(Value::Bool(*inner)),
        Value::Char(inner) => Ok(Value::Char(*inner)),
        Value::Unit => Ok(Value::Unit),
        Value::Opaque(inner) => clone_opaque_box(inner.as_ref())
            .map(Value::Opaque)
            .ok_or_else(|| execution_failed(function, "opaque value is not cloneable".to_owned())),
    }
}

fn clone_opaque_box(value: &(dyn Any + Send + Sync)) -> Option<Box<dyn Any + Send + Sync>> {
    value
        .downcast_ref::<SharedOpaque>()
        .map(|shared| Box::new(shared.clone()) as Box<dyn Any + Send + Sync>)
}

fn opaque_eq(lhs: &(dyn Any + Send + Sync), rhs: &(dyn Any + Send + Sync)) -> bool {
    match (
        lhs.downcast_ref::<SharedOpaque>(),
        rhs.downcast_ref::<SharedOpaque>(),
    ) {
        (Some(lhs), Some(rhs)) => Arc::ptr_eq(&lhs.0, &rhs.0),
        _ => std::ptr::eq(lhs, rhs),
    }
}

fn expect_arity(function: &str, args: &[Value], expected: usize) -> Result<(), FfiError> {
    if args.len() == expected {
        Ok(())
    } else {
        Err(FfiError::ArityMismatch {
            function: function.to_owned(),
            expected,
            got: args.len(),
        })
    }
}

fn expect_array<'a>(
    function: &str,
    args: &'a [Value],
    index: usize,
) -> Result<&'a [Value], FfiError> {
    match args.get(index) {
        Some(Value::Array(values)) => Ok(values),
        Some(value) => Err(type_mismatch(function, index, "Array", value)),
        None => Err(FfiError::ArityMismatch {
            function: function.to_owned(),
            expected: index + 1,
            got: args.len(),
        }),
    }
}

fn expect_string<'a>(function: &str, args: &'a [Value], index: usize) -> Result<&'a str, FfiError> {
    match args.get(index) {
        Some(Value::String(value)) => Ok(value),
        Some(value) => Err(type_mismatch(function, index, "String", value)),
        None => Err(FfiError::ArityMismatch {
            function: function.to_owned(),
            expected: index + 1,
            got: args.len(),
        }),
    }
}

fn expect_nat(function: &str, args: &[Value], index: usize) -> Result<u64, FfiError> {
    match args.get(index) {
        Some(Value::Nat(value)) => Ok(*value),
        Some(value) => Err(type_mismatch(function, index, "Nat", value)),
        None => Err(FfiError::ArityMismatch {
            function: function.to_owned(),
            expected: index + 1,
            got: args.len(),
        }),
    }
}

fn expect_int(function: &str, args: &[Value], index: usize) -> Result<i64, FfiError> {
    match args.get(index) {
        Some(Value::Int(value)) => Ok(*value),
        Some(value) => Err(type_mismatch(function, index, "Int", value)),
        None => Err(FfiError::ArityMismatch {
            function: function.to_owned(),
            expected: index + 1,
            got: args.len(),
        }),
    }
}

fn expect_float(function: &str, args: &[Value], index: usize) -> Result<f64, FfiError> {
    match args.get(index) {
        Some(Value::Float(value)) => Ok(*value),
        Some(value) => Err(type_mismatch(function, index, "Float", value)),
        None => Err(FfiError::ArityMismatch {
            function: function.to_owned(),
            expected: index + 1,
            got: args.len(),
        }),
    }
}

fn expect_bool(function: &str, args: &[Value], index: usize) -> Result<bool, FfiError> {
    match args.get(index) {
        Some(Value::Bool(value)) => Ok(*value),
        Some(value) => Err(type_mismatch(function, index, "Bool", value)),
        None => Err(FfiError::ArityMismatch {
            function: function.to_owned(),
            expected: index + 1,
            got: args.len(),
        }),
    }
}

fn expect_char(function: &str, args: &[Value], index: usize) -> Result<u32, FfiError> {
    match args.get(index) {
        Some(Value::Char(value)) => Ok(*value),
        Some(value) => Err(type_mismatch(function, index, "Char", value)),
        None => Err(FfiError::ArityMismatch {
            function: function.to_owned(),
            expected: index + 1,
            got: args.len(),
        }),
    }
}

fn nat_to_index(value: u64, function: &str) -> Result<usize, FfiError> {
    usize::try_from(value)
        .map_err(|_| execution_failed(function, format!("index out of range for usize: {value}")))
}

fn type_mismatch(function: &str, index: usize, expected: &'static str, value: &Value) -> FfiError {
    FfiError::TypeMismatch {
        function: function.to_owned(),
        index,
        expected,
        found: value_kind(value),
    }
}

fn execution_failed(function: &str, message: String) -> FfiError {
    FfiError::ExecutionFailed {
        function: function.to_owned(),
        message,
    }
}

fn arithmetic_overflow(function: &str) -> FfiError {
    FfiError::ArithmeticOverflow {
        function: function.to_owned(),
    }
}

fn value_kind(value: &Value) -> &'static str {
    match value {
        Value::Nat(_) => "Nat",
        Value::Int(_) => "Int",
        Value::String(_) => "String",
        Value::Float(_) => "Float",
        Value::Array(_) => "Array",
        Value::Bool(_) => "Bool",
        Value::Char(_) => "Char",
        Value::Unit => "Unit",
        Value::Opaque(_) => "Opaque",
    }
}

#[cfg(test)]
#[path = "ffi_bridge_tests.rs"]
mod tests;
