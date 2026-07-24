// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Iterator adapter and consumer lowering for the Rust interpreter.
//!
//! The interpreter models iteration eagerly: every iterable value
//! (`Vec`/array, integer range, `HashMap`/`BTreeMap`) is materialized to a
//! `Value::Array` of its elements, exactly as the for-loop machinery and the
//! map-iteration intrinsics already do. This module extends that eager model to
//! the chained `Iterator` adapters and consumers so expressions like
//!
//! ```text
//! [1, 2, 3].iter().map(|x| x + 1).filter(|x| *x > 2).collect::<Vec<_>>()
//! ```
//!
//! interpret end to end.
//!
//! ## Model
//!
//! Each lazy adapter (`map`, `filter`, `enumerate`, `zip`, `rev`, `take`,
//! `skip`, `copied`, `cloned`, `iter`, `into_iter`) returns a fresh
//! `Value::Array` holding the transformed element sequence. Because adapters
//! return arrays, chaining is just repeated method dispatch on the previous
//! result. The terminal consumers (`collect`, `sum`, `product`, `count`,
//! `last`, `max`, `min`) fold or reduce that array into a final value.
//!
//! ## Soundness
//!
//! - Dispatch is gated strictly on iterable receivers (`Array`, `Range`, and
//!   map structs) so a user-defined method named `map`/`count`/... on some
//!   other type is never shadowed.
//! - `map`/`filter` apply the supplied callable through the regular
//!   `call_callable_value` path, so a closure panic or evaluation error
//!   propagates rather than being silently swallowed or treated as success.
//! - `filter` predicates that do not yield a `bool` are a hard error rather
//!   than a defaulted decision.
//! - `sum`/`product` fold with the shared `eval_binop`, preserving Rust's
//!   wrapping/typed arithmetic; an empty fold with no element type to seed a
//!   zero is reported as an error instead of being guessed.
//! - HashMap/BTreeMap iteration order is unspecified in Rust; this materializes
//!   the model's stored order and verification must not depend on it.

use super::super::Interpreter;
use crate::error::RustSemError;
use crate::expr::EvalResult;
use crate::iterator::extract_iter_elements;
use crate::values::{eval_binop, BinOp, EnumPayload, Value};

/// Method names this module handles as iterator adapters/consumers.
///
/// Used to gate dispatch so only these methods are intercepted for iterable
/// receivers, leaving every other method to normal resolution.
fn is_iterator_method(method: &str) -> bool {
    matches!(
        method,
        "iter"
            | "into_iter"
            | "iter_mut"
            | "copied"
            | "cloned"
            | "map"
            | "filter"
            | "filter_map"
            | "enumerate"
            | "zip"
            | "rev"
            | "take"
            | "skip"
            | "collect"
            | "sum"
            | "product"
            | "count"
            | "last"
            | "max"
            | "min"
    )
}

impl Interpreter {
    /// Materialize an iterable receiver into its element sequence.
    ///
    /// Returns `None` when the (deref-viewed) receiver is not an iterable the
    /// adapter model understands, so the caller can decline to handle the call.
    fn iterator_source_elements(receiver: &Value) -> Option<Vec<Value>> {
        match receiver.deref_view() {
            Value::Array(_) | Value::Tuple(_) | Value::Range { .. } => {
                extract_iter_elements(receiver.deref_view()).ok()
            }
            Value::Struct { name, .. } if name == "HashMap" || name == "BTreeMap" => {
                extract_iter_elements(receiver.deref_view()).ok()
            }
            _ => None,
        }
    }

    /// Try to evaluate an iterator adapter or consumer on an iterable receiver.
    ///
    /// Returns `Some(result)` only when `method` is a known iterator method and
    /// `receiver` is an iterable value; otherwise `None` so other dispatchers
    /// run. The result may be an [`EvalResult::Panic`] / [`EvalResult::Error`]
    /// surfaced from applying a `map`/`filter` callable.
    pub(in crate::eval) fn try_iterator_adapter_method(
        &mut self,
        receiver: &Value,
        method: &str,
        args: &[Value],
    ) -> Option<EvalResult> {
        if !is_iterator_method(method) {
            return None;
        }
        let elements = Self::iterator_source_elements(receiver)?;

        // Adapters/consumers that take no argument share the canonical arity
        // error so callers see the same message as the other intrinsic methods.
        let zero_arg = |build: &dyn Fn() -> EvalResult| match Self::adapter_arity(method, args) {
            Ok(()) => build(),
            Err(err) => EvalResult::Error(err.to_string()),
        };

        let result = match method {
            // Borrowing/owning views are identity in the value-cloning model:
            // the element sequence is the same regardless of by-ref vs by-value.
            "iter" | "into_iter" | "iter_mut" | "copied" | "cloned" => {
                zero_arg(&|| EvalResult::Value(Value::Array(elements.clone())))
            }
            "map" => self.adapter_map(&elements, args),
            "filter" => self.adapter_filter(&elements, args),
            "filter_map" => self.adapter_filter_map(&elements, args),
            "enumerate" => zero_arg(&|| Self::adapter_enumerate(&elements)),
            "zip" => Self::adapter_zip(&elements, args),
            "rev" => zero_arg(&|| {
                let mut rev = elements.clone();
                rev.reverse();
                EvalResult::Value(Value::Array(rev))
            }),
            "take" => Self::adapter_take(&elements, args),
            "skip" => Self::adapter_skip(&elements, args),
            "collect" => zero_arg(&|| EvalResult::Value(Value::Array(elements.clone()))),
            "count" => zero_arg(&|| EvalResult::Value(Value::usize(elements.len()))),
            "last" => zero_arg(&|| EvalResult::Value(Self::option_value(elements.last().cloned()))),
            "sum" => zero_arg(&|| Self::adapter_fold_arith("sum", &elements, BinOp::Add)),
            "product" => zero_arg(&|| Self::adapter_fold_arith("product", &elements, BinOp::Mul)),
            "max" => zero_arg(&|| Self::adapter_reduce_extreme(&elements, Extreme::Max)),
            "min" => zero_arg(&|| Self::adapter_reduce_extreme(&elements, Extreme::Min)),
            _ => return None,
        };
        Some(result)
    }

    /// Enforce a zero-argument adapter/consumer, reusing the canonical arity
    /// error so the message matches the other intrinsic methods (e.g. `last`).
    fn adapter_arity(method: &str, args: &[Value]) -> Result<(), RustSemError> {
        if args.is_empty() {
            Ok(())
        } else {
            Err(RustSemError::intrinsic_arity(method, 0, args.len()))
        }
    }

    /// `iter.map(f)`: apply `f` to each element, collecting the results.
    fn adapter_map(&mut self, elements: &[Value], args: &[Value]) -> EvalResult {
        let callable = match Self::single_callable("map", args) {
            Ok(callable) => callable.clone(),
            Err(err) => return EvalResult::Error(err),
        };
        let mut mapped = Vec::with_capacity(elements.len());
        for element in elements {
            match self.call_callable_value(&callable, vec![element.clone()], &[]) {
                EvalResult::Value(v) | EvalResult::Return(v) => mapped.push(v),
                other => return other,
            }
        }
        EvalResult::Value(Value::Array(mapped))
    }

    /// `iter.filter(p)`: keep elements for which `p` yields `true`.
    fn adapter_filter(&mut self, elements: &[Value], args: &[Value]) -> EvalResult {
        let callable = match Self::single_callable("filter", args) {
            Ok(callable) => callable.clone(),
            Err(err) => return EvalResult::Error(err),
        };
        let mut kept = Vec::new();
        for element in elements {
            match self.call_callable_value(&callable, vec![element.clone()], &[]) {
                EvalResult::Value(v) | EvalResult::Return(v) => match v.deref_view().as_bool() {
                    Some(true) => kept.push(element.clone()),
                    Some(false) => {}
                    None => {
                        return EvalResult::Error(
                            "iterator adapter `filter` predicate must return bool".to_string(),
                        )
                    }
                },
                other => return other,
            }
        }
        EvalResult::Value(Value::Array(kept))
    }

    /// `iter.filter_map(f)`: apply `f`, keeping the `Some(_)` payloads.
    fn adapter_filter_map(&mut self, elements: &[Value], args: &[Value]) -> EvalResult {
        let callable = match Self::single_callable("filter_map", args) {
            Ok(callable) => callable.clone(),
            Err(err) => return EvalResult::Error(err),
        };
        let mut kept = Vec::new();
        for element in elements {
            let produced = match self.call_callable_value(&callable, vec![element.clone()], &[]) {
                EvalResult::Value(v) | EvalResult::Return(v) => v,
                other => return other,
            };
            match produced.deref_view() {
                Value::Enum {
                    name,
                    variant,
                    payload,
                } if name == "Option" => match (variant.as_str(), payload.as_ref()) {
                    ("Some", EnumPayload::Tuple(inner)) if inner.len() == 1 => {
                        kept.push(inner[0].clone());
                    }
                    ("None", _) => {}
                    _ => {
                        return EvalResult::Error(
                            "iterator adapter `filter_map` closure must return Option".to_string(),
                        )
                    }
                },
                _ => {
                    return EvalResult::Error(
                        "iterator adapter `filter_map` closure must return Option".to_string(),
                    )
                }
            }
        }
        EvalResult::Value(Value::Array(kept))
    }

    /// `iter.enumerate()`: pair each element with its zero-based index.
    fn adapter_enumerate(elements: &[Value]) -> EvalResult {
        let pairs = elements
            .iter()
            .enumerate()
            .map(|(idx, element)| Value::Tuple(vec![Value::usize(idx), element.clone()]))
            .collect();
        EvalResult::Value(Value::Array(pairs))
    }

    /// `iter.zip(other)`: pair elements positionally, truncating to the shorter.
    fn adapter_zip(elements: &[Value], args: &[Value]) -> EvalResult {
        if args.len() != 1 {
            return EvalResult::Error(format!(
                "iterator adapter `zip` expects 1 argument, got {}",
                args.len()
            ));
        }
        let Some(other) = Self::iterator_source_elements(&args[0]) else {
            return EvalResult::Error(
                "iterator adapter `zip` argument is not iterable".to_string(),
            );
        };
        let zipped = elements
            .iter()
            .zip(other.iter())
            .map(|(left, right)| Value::Tuple(vec![left.clone(), right.clone()]))
            .collect();
        EvalResult::Value(Value::Array(zipped))
    }

    /// `iter.take(n)`: keep at most the first `n` elements.
    fn adapter_take(elements: &[Value], args: &[Value]) -> EvalResult {
        match Self::single_count("take", args) {
            Ok(n) => EvalResult::Value(Value::Array(elements.iter().take(n).cloned().collect())),
            Err(err) => EvalResult::Error(err),
        }
    }

    /// `iter.skip(n)`: drop the first `n` elements.
    fn adapter_skip(elements: &[Value], args: &[Value]) -> EvalResult {
        match Self::single_count("skip", args) {
            Ok(n) => EvalResult::Value(Value::Array(elements.iter().skip(n).cloned().collect())),
            Err(err) => EvalResult::Error(err),
        }
    }

    /// `iter.sum()` / `iter.product()`: fold the elements with `op`.
    ///
    /// Folds left-to-right starting from the first element so the accumulator
    /// keeps the element's concrete integer/float type. An empty sequence has
    /// no element to seed the zero/one identity at the right width, so it is an
    /// error here rather than a guessed value.
    fn adapter_fold_arith(method: &str, elements: &[Value], op: BinOp) -> EvalResult {
        let mut iter = elements.iter();
        let Some(first) = iter.next() else {
            return EvalResult::Error(format!(
                "iterator consumer `{method}` over an empty iterator needs an explicit element type"
            ));
        };
        let mut acc = first.deref_view().clone();
        for element in iter {
            match eval_binop(op, &acc, element.deref_view()) {
                Some(next) => acc = next,
                None => {
                    return EvalResult::Error(format!(
                        "iterator consumer `{method}` cannot combine elements of differing types"
                    ))
                }
            }
        }
        EvalResult::Value(acc)
    }

    /// `iter.max()` / `iter.min()`: reduce to the extreme element.
    fn adapter_reduce_extreme(elements: &[Value], extreme: Extreme) -> EvalResult {
        let mut iter = elements.iter();
        let Some(first) = iter.next() else {
            return EvalResult::Value(Self::option_value(None));
        };
        let mut best = first.deref_view().clone();
        for element in iter {
            let candidate = element.deref_view();
            // `Gt` keeps the larger for `max`; `Lt` keeps the smaller for `min`.
            let op = match extreme {
                Extreme::Max => BinOp::Gt,
                Extreme::Min => BinOp::Lt,
            };
            match eval_binop(op, candidate, &best) {
                Some(Value::Bool(true)) => best = candidate.clone(),
                Some(Value::Bool(false)) => {}
                _ => {
                    return EvalResult::Error(
                        "iterator consumer cannot compare elements of these types".to_string(),
                    )
                }
            }
        }
        EvalResult::Value(Self::option_value(Some(best)))
    }

    /// Extract the single callable argument for a `map`/`filter` adapter.
    fn single_callable<'a>(method: &str, args: &'a [Value]) -> Result<&'a Value, String> {
        match args {
            [callable @ (Value::Closure { .. } | Value::FnPtr { .. })] => Ok(callable),
            [_] => Err(format!(
                "iterator adapter `{method}` argument must be a closure or function"
            )),
            _ => Err(format!(
                "iterator adapter `{method}` expects 1 argument, got {}",
                args.len()
            )),
        }
    }

    /// Extract the single `usize` count argument for `take`/`skip`.
    fn single_count(method: &str, args: &[Value]) -> Result<usize, String> {
        match args {
            [count] => count
                .deref_view()
                .as_u64()
                .and_then(|n| usize::try_from(n).ok())
                .ok_or_else(|| {
                    format!("iterator adapter `{method}` argument must be a usize count")
                }),
            _ => Err(format!(
                "iterator adapter `{method}` expects 1 argument, got {}",
                args.len()
            )),
        }
    }
}

/// Which extreme `max`/`min` reduces toward.
#[derive(Debug, Clone, Copy)]
enum Extreme {
    Max,
    Min,
}

#[cfg(test)]
#[path = "iterator_adapters_tests.rs"]
mod tests;
