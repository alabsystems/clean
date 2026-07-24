// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Intrinsic methods on Array and String values: len, is_empty, contains,
//! starts_with, ends_with, first, last, get.
//!
//! Also covers the `HashMap` / `BTreeMap` iteration and query methods. Maps are
//! modeled as a `Value::Struct` whose `entries` field is a `Value::Array` of
//! `(K, V)` 2-tuples. The iteration methods (`iter`, `into_iter`, `keys`,
//! `values`) materialize the requested element sequence as a `Value::Array`,
//! which the for-loop and iterator machinery then consume exactly like any
//! other array. HashMap order is unspecified in Rust, so this materializes the
//! pairs in the model's stored order and verification must not depend on it.

use super::super::Interpreter;
use crate::error::RustSemError;
use crate::values::Value;
use std::collections::BTreeMap;

impl Interpreter {
    fn eval_len_method(&self, receiver: &Value, args: &[Value]) -> Result<Value, RustSemError> {
        if !args.is_empty() {
            return Err(RustSemError::intrinsic_arity("len", 0, args.len()));
        }
        match receiver {
            Value::Array(elems) => Ok(Value::usize(elems.len())),
            Value::Str(text) => Ok(Value::usize(text.len())),
            _ => unreachable!("len is only dispatched for array/string receivers"),
        }
    }

    fn eval_is_empty_method(
        &self,
        receiver: &Value,
        args: &[Value],
    ) -> Result<Value, RustSemError> {
        if !args.is_empty() {
            return Err(RustSemError::intrinsic_arity("is_empty", 0, args.len()));
        }
        match receiver {
            Value::Array(elems) => Ok(Value::Bool(elems.is_empty())),
            Value::Str(text) => Ok(Value::Bool(text.is_empty())),
            _ => unreachable!("is_empty is only dispatched for array/string receivers"),
        }
    }

    fn eval_contains_method(
        &self,
        receiver: &Value,
        args: &[Value],
    ) -> Result<Value, RustSemError> {
        if args.len() != 1 {
            return Err(RustSemError::intrinsic_arity("contains", 1, args.len()));
        }
        match receiver {
            Value::Array(elems) => Ok(Value::Bool(elems.contains(&args[0]))),
            Value::Str(text) => {
                let Value::Str(pattern) = &args[0] else {
                    return Err(RustSemError::intrinsic_string_argument("str::contains"));
                };
                Ok(Value::Bool(text.contains(pattern.as_str())))
            }
            _ => unreachable!("contains is only dispatched for array/string receivers"),
        }
    }

    fn eval_starts_with_method(&self, text: &str, args: &[Value]) -> Result<Value, RustSemError> {
        if args.len() != 1 {
            return Err(RustSemError::intrinsic_arity("starts_with", 1, args.len()));
        }
        let Value::Str(pattern) = &args[0] else {
            return Err(RustSemError::intrinsic_string_argument("str::starts_with"));
        };
        Ok(Value::Bool(text.starts_with(pattern.as_str())))
    }

    fn eval_ends_with_method(&self, text: &str, args: &[Value]) -> Result<Value, RustSemError> {
        if args.len() != 1 {
            return Err(RustSemError::intrinsic_arity("ends_with", 1, args.len()));
        }
        let Value::Str(pattern) = &args[0] else {
            return Err(RustSemError::intrinsic_string_argument("str::ends_with"));
        };
        Ok(Value::Bool(text.ends_with(pattern.as_str())))
    }

    fn eval_first_method(&self, elems: &[Value], args: &[Value]) -> Result<Value, RustSemError> {
        if !args.is_empty() {
            return Err(RustSemError::intrinsic_arity("first", 0, args.len()));
        }
        Ok(Self::option_value(elems.first().cloned()))
    }

    fn eval_last_method(&self, elems: &[Value], args: &[Value]) -> Result<Value, RustSemError> {
        if !args.is_empty() {
            return Err(RustSemError::intrinsic_arity("last", 0, args.len()));
        }
        Ok(Self::option_value(elems.last().cloned()))
    }

    /// Bounds-checked slice indexing: `slice::get(i)` yields `Some(elem)` when
    /// `i < len` and `None` otherwise. Unlike `slice[i]`, an out-of-bounds index
    /// is not a hard error — it is the defining safe alternative to panicking
    /// indexing, so a too-large index must produce `None` rather than fail.
    fn eval_get_method(&self, elems: &[Value], args: &[Value]) -> Result<Value, RustSemError> {
        if args.len() != 1 {
            return Err(RustSemError::intrinsic_arity("get", 1, args.len()));
        }
        let Some(index) = args[0].as_u64() else {
            return Err(RustSemError::intrinsic_usize_argument("slice::get"));
        };
        let element = usize::try_from(index)
            .ok()
            .and_then(|i| elems.get(i).cloned());
        Ok(Self::option_value(element))
    }

    /// Borrow a map struct's `entries` array, returning an empty slice when the
    /// field is absent or mistyped (an empty map iterates to nothing).
    fn map_entries(fields: &BTreeMap<String, Value>) -> &[Value] {
        match fields.get("entries") {
            Some(Value::Array(entries)) => entries.as_slice(),
            _ => &[],
        }
    }

    /// `map.iter()` / `map.into_iter()`: materialize the `(K, V)` pairs as an
    /// array the for-loop and iterator adapters consume like any other array.
    fn eval_map_into_iter(
        &self,
        fields: &BTreeMap<String, Value>,
        method: &str,
        args: &[Value],
    ) -> Result<Value, RustSemError> {
        if !args.is_empty() {
            return Err(RustSemError::intrinsic_arity(method, 0, args.len()));
        }
        Ok(Value::Array(Self::map_entries(fields).to_vec()))
    }

    /// `map.keys()`: the first component of each `(K, V)` pair, in stored order.
    fn eval_map_keys(
        &self,
        fields: &BTreeMap<String, Value>,
        args: &[Value],
    ) -> Result<Value, RustSemError> {
        if !args.is_empty() {
            return Err(RustSemError::intrinsic_arity("keys", 0, args.len()));
        }
        let keys = Self::map_entries(fields)
            .iter()
            .filter_map(|entry| match entry {
                Value::Tuple(pair) => pair.first().cloned(),
                _ => None,
            })
            .collect();
        Ok(Value::Array(keys))
    }

    /// `map.values()`: the second component of each `(K, V)` pair, in stored order.
    fn eval_map_values(
        &self,
        fields: &BTreeMap<String, Value>,
        args: &[Value],
    ) -> Result<Value, RustSemError> {
        if !args.is_empty() {
            return Err(RustSemError::intrinsic_arity("values", 0, args.len()));
        }
        let values = Self::map_entries(fields)
            .iter()
            .filter_map(|entry| match entry {
                Value::Tuple(pair) => pair.get(1).cloned(),
                _ => None,
            })
            .collect();
        Ok(Value::Array(values))
    }

    /// `map.len()` / `map.is_empty()`: entry-count queries on a map struct.
    fn eval_map_len(
        &self,
        fields: &BTreeMap<String, Value>,
        method: &str,
        args: &[Value],
    ) -> Result<Value, RustSemError> {
        if !args.is_empty() {
            return Err(RustSemError::intrinsic_arity(method, 0, args.len()));
        }
        let count = Self::map_entries(fields).len();
        if method == "is_empty" {
            Ok(Value::Bool(count == 0))
        } else {
            Ok(Value::usize(count))
        }
    }

    /// `map.contains_key(k)`: whether any stored pair has key equal to `k`.
    /// The argument is `deref_view`-normalized so a borrowed key (`&k`) matches
    /// an owned stored key.
    fn eval_map_contains_key(
        &self,
        fields: &BTreeMap<String, Value>,
        args: &[Value],
    ) -> Result<Value, RustSemError> {
        if args.len() != 1 {
            return Err(RustSemError::intrinsic_arity("contains_key", 1, args.len()));
        }
        let needle = args[0].deref_view();
        let found = Self::map_entries(fields).iter().any(|entry| match entry {
            Value::Tuple(pair) => pair.first().map(Value::deref_view) == Some(needle),
            _ => false,
        });
        Ok(Value::Bool(found))
    }

    /// `map.get(k)`: `Some(v)` for the first stored pair whose key equals `k`,
    /// else `None`. Mirrors `HashMap::get` returning an `Option`.
    fn eval_map_get(
        &self,
        fields: &BTreeMap<String, Value>,
        args: &[Value],
    ) -> Result<Value, RustSemError> {
        if args.len() != 1 {
            return Err(RustSemError::intrinsic_arity("get", 1, args.len()));
        }
        let needle = args[0].deref_view();
        let found = Self::map_entries(fields)
            .iter()
            .find_map(|entry| match entry {
                Value::Tuple(pair) if pair.first().map(Value::deref_view) == Some(needle) => {
                    pair.get(1).cloned()
                }
                _ => None,
            });
        Ok(Self::option_value(found))
    }

    /// Dispatch the immutable intrinsic methods that apply to a `HashMap` /
    /// `BTreeMap` struct receiver.
    fn try_map_intrinsic_method(
        &self,
        name: &str,
        fields: &BTreeMap<String, Value>,
        method: &str,
        args: &[Value],
    ) -> Option<Result<Value, RustSemError>> {
        if name != "HashMap" && name != "BTreeMap" {
            return None;
        }
        match method {
            "iter" | "into_iter" | "iter_mut" => {
                Some(self.eval_map_into_iter(fields, method, args))
            }
            "keys" => Some(self.eval_map_keys(fields, args)),
            "values" => Some(self.eval_map_values(fields, args)),
            "len" | "is_empty" => Some(self.eval_map_len(fields, method, args)),
            "contains_key" => Some(self.eval_map_contains_key(fields, args)),
            "get" => Some(self.eval_map_get(fields, args)),
            _ => None,
        }
    }

    pub(in crate::eval) fn try_collection_intrinsic_method(
        &self,
        receiver: &Value,
        method: &str,
        args: &[Value],
    ) -> Option<Result<Value, RustSemError>> {
        if let Value::Struct { name, fields } = receiver {
            if let Some(result) = self.try_map_intrinsic_method(name, fields, method, args) {
                return Some(result);
            }
        }
        match (receiver, method) {
            (Value::Array(_) | Value::Str(_), "len") => Some(self.eval_len_method(receiver, args)),
            (Value::Array(_) | Value::Str(_), "is_empty") => {
                Some(self.eval_is_empty_method(receiver, args))
            }
            (Value::Array(_) | Value::Str(_), "contains") => {
                Some(self.eval_contains_method(receiver, args))
            }
            (Value::Str(text), "starts_with") => Some(self.eval_starts_with_method(text, args)),
            (Value::Str(text), "ends_with") => Some(self.eval_ends_with_method(text, args)),
            (Value::Array(elems), "first") => Some(self.eval_first_method(elems, args)),
            (Value::Array(elems), "last") => Some(self.eval_last_method(elems, args)),
            (Value::Array(elems), "get") => Some(self.eval_get_method(elems, args)),
            _ => None,
        }
    }
}
