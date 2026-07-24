// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Builtin intrinsic function and method dispatch for the Rust interpreter.
//!
//! Handles standard-library intrinsic associated functions (String::new, Vec::new, etc.),
//! immutable intrinsic methods (len, is_empty, unwrap, map, etc.),
//! and mutating intrinsic methods (push, pop, push_str).
//!
//! The main `try_intrinsic_method` dispatcher delegates to per-type submodules:
//! - `collection_methods`: Array and String methods
//! - `option_methods`: Option combinators and inspection
//! - `result_methods`: Result combinators and inspection

mod collection_methods;
mod iterator_adapters;
mod option_methods;
mod result_combinators;
mod result_methods;

use super::Interpreter;
use crate::error::RustSemError;
use crate::expr::EvalResult;
use crate::format_intrinsics::{render_format_call, FORMAT_INTRINSIC};
use crate::types::{Lifetime, Mutability};
use crate::values::{EnumPayload, Value};

impl Interpreter {
    /// Try to evaluate a standard-library intrinsic associated function.
    /// Returns `Some(result)` if `name` is a recognized intrinsic, `None` otherwise.
    pub(in crate::eval) fn try_intrinsic(
        &mut self,
        name: &str,
        args: &[Value],
    ) -> Option<Result<Value, RustSemError>> {
        if let Some(result) = self.try_atomic_intrinsic(name, args) {
            return Some(result);
        }

        match name {
            FORMAT_INTRINSIC => Some(self.eval_format_intrinsic(args)),
            name if Self::is_interior_mutability_intrinsic_function_name(name) => {
                self.try_interior_mutability_intrinsic(name, args)
            }
            "String::new" if args.is_empty() => Some(Ok(Value::Str(String::new()))),
            "String::from" if args.len() == 1 => Some(self.eval_string_from_intrinsic(&args[0])),
            "Vec::new" if args.is_empty() => Some(Ok(Value::Array(Vec::new()))),
            "Vec::with_capacity" if args.len() == 1 => {
                // Capacity is a runtime hint; the semantic model uses a plain Vec.
                Some(Ok(Value::Array(Vec::new())))
            }
            "Box::new" if args.len() == 1 => Some(Ok(args[0].clone())),
            _ => None,
        }
    }

    pub(in crate::eval) fn is_intrinsic_function_name(name: &str) -> bool {
        Self::is_atomic_intrinsic_function_name(name)
            || matches!(
                name,
                FORMAT_INTRINSIC
                    | "Cell::new"
                    | "RefCell::new"
                    | "UnsafeCell::new"
                    | "OnceCell::new"
                    | "OnceLock::new"
                    | "Mutex::new"
                    | "RwLock::new"
                    | "String::new"
                    | "String::from"
                    | "Vec::new"
                    | "Vec::with_capacity"
                    | "Box::new"
            )
    }

    pub(in crate::eval) fn option_value(value: Option<Value>) -> Value {
        let (variant, payload) = match value {
            Some(value) => ("Some", EnumPayload::Tuple(vec![value])),
            None => ("None", EnumPayload::Unit),
        };
        Value::Enum {
            name: "Option".to_string(),
            variant: variant.to_string(),
            payload: Box::new(payload),
        }
    }

    pub(in crate::eval) fn result_value(value: Result<Value, Value>) -> Value {
        let (variant, payload) = match value {
            Ok(value) => ("Ok", EnumPayload::Tuple(vec![value])),
            Err(value) => ("Err", EnumPayload::Tuple(vec![value])),
        };
        Value::Enum {
            name: "Result".to_string(),
            variant: variant.to_string(),
            payload: Box::new(payload),
        }
    }

    pub(in crate::eval) fn preserved_reference(
        &mut self,
        referent: Value,
        mutability: Mutability,
    ) -> Result<Value, RustSemError> {
        let referent_ty = referent.get_type();
        let size = referent_ty.size().unwrap_or(8);
        let align = size.next_power_of_two().min(8);
        let addr = self.ctx.memory.allocate_aligned(size, align)?;
        self.ctx
            .memory
            .set_allocation_type(addr, referent_ty)
            .expect("fresh allocation should accept type metadata");
        if let Some(len) = referent.slice_len() {
            self.ctx
                .memory
                .record_slice_len(addr, len)
                .expect("fresh allocation should accept slice metadata");
        }
        Ok(Value::Reference {
            addr,
            mutability,
            lifetime: Lifetime::Static,
            referent: Some(Box::new(referent)),
        })
    }

    fn eval_format_intrinsic(&self, args: &[Value]) -> Result<Value, RustSemError> {
        match args.split_first() {
            Some((Value::Str(template), values)) => render_format_call(template, values)
                .map(Value::Str)
                .map_err(RustSemError::format_intrinsic_failed),
            Some(_) => Err(RustSemError::FormatIntrinsicTemplateMustBeString),
            None => Err(RustSemError::FormatIntrinsicMissingArgument),
        }
    }

    fn eval_string_from_intrinsic(&self, arg: &Value) -> Result<Value, RustSemError> {
        match arg {
            Value::Str(text) => Ok(Value::Str(text.clone())),
            _ => Err(RustSemError::intrinsic_string_argument("String::from")),
        }
    }

    fn eval_string_push_str_mutation(
        &self,
        text: &str,
        args: &[Value],
    ) -> Result<(Value, Value), RustSemError> {
        if args.len() != 1 {
            return Err(RustSemError::intrinsic_arity("push_str", 1, args.len()));
        }
        let Value::Str(suffix) = &args[0] else {
            return Err(RustSemError::intrinsic_string_argument("str::push_str"));
        };
        let mut updated = text.to_string();
        updated.push_str(suffix);
        Ok((Value::Unit, Value::Str(updated)))
    }

    fn eval_string_push_mutation(
        &self,
        text: &str,
        args: &[Value],
    ) -> Result<(Value, Value), RustSemError> {
        if args.len() != 1 {
            return Err(RustSemError::intrinsic_arity("push", 1, args.len()));
        }
        let Value::Char(ch) = &args[0] else {
            return Err(RustSemError::intrinsic_char_argument("str::push"));
        };
        let mut updated = text.to_string();
        updated.push(*ch);
        Ok((Value::Unit, Value::Str(updated)))
    }

    fn eval_string_pop_mutation(
        &self,
        text: &str,
        args: &[Value],
    ) -> Result<(Value, Value), RustSemError> {
        if !args.is_empty() {
            return Err(RustSemError::intrinsic_arity("pop", 0, args.len()));
        }
        let mut updated = text.to_string();
        let popped = updated.pop().map(Value::Char);
        Ok((Self::option_value(popped), Value::Str(updated)))
    }

    fn eval_array_push_mutation(
        &self,
        elems: &[Value],
        args: &[Value],
    ) -> Result<(Value, Value), RustSemError> {
        if args.len() != 1 {
            return Err(RustSemError::intrinsic_arity("push", 1, args.len()));
        }
        let mut updated = elems.to_vec();
        updated.push(args[0].clone());
        Ok((Value::Unit, Value::Array(updated)))
    }

    fn eval_array_pop_mutation(
        &self,
        elems: &[Value],
        args: &[Value],
    ) -> Result<(Value, Value), RustSemError> {
        if !args.is_empty() {
            return Err(RustSemError::intrinsic_arity("pop", 0, args.len()));
        }
        let mut updated = elems.to_vec();
        let popped = updated.pop();
        Ok((Self::option_value(popped), Value::Array(updated)))
    }

    /// Try to evaluate a mutating standard-library intrinsic method on a builtin value.
    /// Returns the method result plus the updated receiver value.
    pub(in crate::eval) fn try_intrinsic_mutating_method(
        &self,
        receiver: &Value,
        method: &str,
        args: &[Value],
    ) -> Option<Result<(Value, Value), RustSemError>> {
        if let Some(result) = self.try_atomic_mutating_method(receiver, method, args) {
            return Some(result);
        }

        match (receiver, method) {
            (Value::Str(text), "push_str") => Some(self.eval_string_push_str_mutation(text, args)),
            (Value::Str(text), "push") => Some(self.eval_string_push_mutation(text, args)),
            (Value::Str(text), "pop") => Some(self.eval_string_pop_mutation(text, args)),
            (Value::Array(elems), "push") => Some(self.eval_array_push_mutation(elems, args)),
            (Value::Array(elems), "pop") => Some(self.eval_array_pop_mutation(elems, args)),
            _ => None,
        }
    }

    /// Try to evaluate a standard-library intrinsic method on a builtin value.
    /// Returns `Some(result)` if the receiver/method pair is recognized.
    ///
    /// Dispatches to per-type submodules: collection, option, result.
    pub(in crate::eval) fn try_intrinsic_method(
        &mut self,
        receiver: &Value,
        method: &str,
        args: &[Value],
    ) -> Option<EvalResult> {
        self.try_atomic_method(receiver, method, args)
            .or_else(|| self.try_interior_mutability_method(receiver, method, args))
            .or_else(|| self.try_iterator_adapter_method(receiver, method, args))
            .or_else(|| {
                self.try_collection_intrinsic_method(receiver.deref_view(), method, args)
                    .map(|result| match result {
                        Ok(value) => EvalResult::Value(value),
                        Err(err) => EvalResult::Error(err.to_string()),
                    })
            })
            .or_else(|| self.try_option_intrinsic_method(receiver.deref_view(), method, args))
            .or_else(|| self.try_result_intrinsic_method(receiver.deref_view(), method, args))
    }
}
