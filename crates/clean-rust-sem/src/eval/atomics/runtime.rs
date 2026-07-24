// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::super::Interpreter;
use super::model::{
    validate_compare_exchange_failure_ordering, validate_fence_ordering, validate_ordering,
    AtomicFence, AtomicFenceKind, AtomicOp, MemoryOrdering,
};
use crate::error::RustSemError;
use crate::expr::EvalResult;
use crate::values::{eval_binop, BinOp, EnumPayload, Value};

fn require_atomic_receiver(op: AtomicOp, value: &mut Value) -> Result<&mut Value, String> {
    match value {
        Value::Atomic { inner } => Ok(inner.as_mut()),
        _ => Err(format!(
            "atomic {} requires an atomic receiver value",
            op.name()
        )),
    }
}

fn require_arg(op: AtomicOp, arg: Option<Value>) -> Result<Value, String> {
    arg.ok_or_else(|| format!("atomic {} requires an argument", op.name()))
}

fn require_compare_exchange_args(arg: Option<Value>) -> Result<(Value, Value), String> {
    match arg {
        Some(Value::Tuple(mut args)) if args.len() == 2 => {
            let new = args.pop().expect("length checked above");
            let current = args.pop().expect("length checked above");
            Ok((current, new))
        }
        Some(_) | None => {
            Err("atomic compare_exchange requires a `(current, new)` argument tuple".to_string())
        }
    }
}

fn result_value(value: Result<Value, Value>) -> Value {
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

fn eval_fetch_op(op: AtomicOp, current: &Value, arg: &Value) -> Result<Value, String> {
    let binop = match op {
        AtomicOp::FetchAdd => BinOp::Add,
        AtomicOp::FetchSub => BinOp::Sub,
        AtomicOp::FetchAnd => BinOp::BitAnd,
        AtomicOp::FetchOr => BinOp::BitOr,
        AtomicOp::FetchXor => BinOp::BitXor,
        AtomicOp::Load | AtomicOp::Store | AtomicOp::Swap | AtomicOp::CompareExchange => {
            unreachable!("fetch operations always map to a BinOp")
        }
    };
    eval_binop(binop, current, arg).ok_or_else(|| {
        format!(
            "atomic {} is unsupported for values `{:?}` and `{:?}`",
            op.name(),
            current,
            arg
        )
    })
}

fn parse_ordering(value: &Value) -> Result<MemoryOrdering, RustSemError> {
    MemoryOrdering::try_from(value).map_err(RustSemError::Eval)
}

/// Evaluate a single atomic operation under the current SeqCst-only model.
pub fn eval_atomic_op(
    op: AtomicOp,
    value: &mut Value,
    arg: Option<Value>,
    ordering: MemoryOrdering,
) -> EvalResult {
    if let Err(err) = validate_ordering(op, ordering) {
        return EvalResult::Error(err);
    }

    let current = match require_atomic_receiver(op, value) {
        Ok(current) => current,
        Err(err) => return EvalResult::Error(err),
    };

    match op {
        AtomicOp::Load => EvalResult::Value(current.clone()),
        AtomicOp::Store => {
            let next = match require_arg(op, arg) {
                Ok(next) => next,
                Err(err) => return EvalResult::Error(err),
            };
            *current = next;
            EvalResult::Value(Value::Unit)
        }
        AtomicOp::Swap => {
            let next = match require_arg(op, arg) {
                Ok(next) => next,
                Err(err) => return EvalResult::Error(err),
            };
            let previous = std::mem::replace(current, next);
            EvalResult::Value(previous)
        }
        AtomicOp::CompareExchange => {
            let (expected, next) = match require_compare_exchange_args(arg) {
                Ok(values) => values,
                Err(err) => return EvalResult::Error(err),
            };

            if *current == expected {
                let previous = std::mem::replace(current, next);
                EvalResult::Value(result_value(Ok(previous)))
            } else {
                EvalResult::Value(result_value(Err(current.clone())))
            }
        }
        AtomicOp::FetchAdd
        | AtomicOp::FetchSub
        | AtomicOp::FetchAnd
        | AtomicOp::FetchOr
        | AtomicOp::FetchXor => {
            let arg = match require_arg(op, arg) {
                Ok(arg) => arg,
                Err(err) => return EvalResult::Error(err),
            };
            let previous = current.clone();
            let next = match eval_fetch_op(op, &previous, &arg) {
                Ok(next) => next,
                Err(err) => return EvalResult::Error(err),
            };
            *current = next;
            EvalResult::Value(previous)
        }
    }
}

impl Interpreter {
    fn atomic_intrinsic_type_name(name: &str) -> Option<&str> {
        let type_name = name.strip_suffix("::new")?;
        let type_name = type_name.rsplit("::").next().unwrap_or(type_name);
        matches!(
            type_name,
            "AtomicBool"
                | "AtomicI8"
                | "AtomicI16"
                | "AtomicI32"
                | "AtomicI64"
                | "AtomicIsize"
                | "AtomicU8"
                | "AtomicU16"
                | "AtomicU32"
                | "AtomicU64"
                | "AtomicUsize"
                | "AtomicPtr"
        )
        .then_some(type_name)
    }

    fn atomic_fence_kind(name: &str) -> Option<AtomicFenceKind> {
        match name.rsplit("::").next().unwrap_or(name) {
            "fence" => Some(AtomicFenceKind::Fence),
            "compiler_fence" => Some(AtomicFenceKind::CompilerFence),
            _ => None,
        }
    }

    pub(in crate::eval) fn is_atomic_intrinsic_function_name(name: &str) -> bool {
        Self::atomic_intrinsic_type_name(name).is_some() || Self::atomic_fence_kind(name).is_some()
    }

    pub(in crate::eval) fn try_atomic_intrinsic(
        &self,
        name: &str,
        args: &[Value],
    ) -> Option<Result<Value, RustSemError>> {
        if let Some(kind) = Self::atomic_fence_kind(name) {
            if args.len() != 1 {
                return Some(Err(RustSemError::intrinsic_arity(name, 1, args.len())));
            }
            let ordering = match parse_ordering(&args[0]) {
                Ok(ordering) => ordering,
                Err(err) => return Some(Err(err)),
            };
            let fence = AtomicFence::with_kind(kind, ordering);
            return Some(
                validate_fence_ordering(fence)
                    .map(|()| Value::Unit)
                    .map_err(RustSemError::Eval),
            );
        }

        let _ = Self::atomic_intrinsic_type_name(name)?;
        if args.len() != 1 {
            return Some(Err(RustSemError::intrinsic_arity(name, 1, args.len())));
        }
        Some(Ok(Value::Atomic {
            inner: Box::new(self.materialize_value(&args[0])),
        }))
    }

    pub(in crate::eval) fn try_atomic_method(
        &self,
        receiver: &Value,
        method: &str,
        args: &[Value],
    ) -> Option<EvalResult> {
        let Value::Atomic { .. } = receiver else {
            return None;
        };

        match method {
            "load" => {
                if args.len() != 1 {
                    return Some(EvalResult::Error(
                        RustSemError::intrinsic_arity(method, 1, args.len()).to_string(),
                    ));
                }
                let ordering = match parse_ordering(&args[0]) {
                    Ok(ordering) => ordering,
                    Err(err) => return Some(EvalResult::Error(err.to_string())),
                };
                let mut value = receiver.clone();
                Some(eval_atomic_op(AtomicOp::Load, &mut value, None, ordering))
            }
            _ => None,
        }
    }

    pub(in crate::eval) fn try_atomic_mutating_method(
        &self,
        receiver: &Value,
        method: &str,
        args: &[Value],
    ) -> Option<Result<(Value, Value), RustSemError>> {
        let Value::Atomic { .. } = receiver else {
            return None;
        };

        let mut updated_receiver = receiver.clone();
        let result = match method {
            "store" => {
                if args.len() != 2 {
                    return Some(Err(RustSemError::intrinsic_arity(method, 2, args.len())));
                }
                let ordering = match parse_ordering(&args[1]) {
                    Ok(ordering) => ordering,
                    Err(err) => return Some(Err(err)),
                };
                eval_atomic_op(
                    AtomicOp::Store,
                    &mut updated_receiver,
                    Some(args[0].clone()),
                    ordering,
                )
            }
            "swap" => {
                if args.len() != 2 {
                    return Some(Err(RustSemError::intrinsic_arity(method, 2, args.len())));
                }
                let ordering = match parse_ordering(&args[1]) {
                    Ok(ordering) => ordering,
                    Err(err) => return Some(Err(err)),
                };
                eval_atomic_op(
                    AtomicOp::Swap,
                    &mut updated_receiver,
                    Some(args[0].clone()),
                    ordering,
                )
            }
            "compare_exchange" | "compare_exchange_weak" => {
                if args.len() != 4 {
                    return Some(Err(RustSemError::intrinsic_arity(method, 4, args.len())));
                }
                let success = match parse_ordering(&args[2]) {
                    Ok(ordering) => ordering,
                    Err(err) => return Some(Err(err)),
                };
                let failure = match parse_ordering(&args[3]) {
                    Ok(ordering) => ordering,
                    Err(err) => return Some(Err(err)),
                };
                if let Err(err) = validate_compare_exchange_failure_ordering(success, failure) {
                    return Some(Err(RustSemError::Eval(err)));
                }
                eval_atomic_op(
                    AtomicOp::CompareExchange,
                    &mut updated_receiver,
                    Some(Value::Tuple(vec![args[0].clone(), args[1].clone()])),
                    success,
                )
            }
            "fetch_add" => {
                if args.len() != 2 {
                    return Some(Err(RustSemError::intrinsic_arity(method, 2, args.len())));
                }
                let ordering = match parse_ordering(&args[1]) {
                    Ok(ordering) => ordering,
                    Err(err) => return Some(Err(err)),
                };
                eval_atomic_op(
                    AtomicOp::FetchAdd,
                    &mut updated_receiver,
                    Some(args[0].clone()),
                    ordering,
                )
            }
            "fetch_sub" => {
                if args.len() != 2 {
                    return Some(Err(RustSemError::intrinsic_arity(method, 2, args.len())));
                }
                let ordering = match parse_ordering(&args[1]) {
                    Ok(ordering) => ordering,
                    Err(err) => return Some(Err(err)),
                };
                eval_atomic_op(
                    AtomicOp::FetchSub,
                    &mut updated_receiver,
                    Some(args[0].clone()),
                    ordering,
                )
            }
            "fetch_and" => {
                if args.len() != 2 {
                    return Some(Err(RustSemError::intrinsic_arity(method, 2, args.len())));
                }
                let ordering = match parse_ordering(&args[1]) {
                    Ok(ordering) => ordering,
                    Err(err) => return Some(Err(err)),
                };
                eval_atomic_op(
                    AtomicOp::FetchAnd,
                    &mut updated_receiver,
                    Some(args[0].clone()),
                    ordering,
                )
            }
            "fetch_or" => {
                if args.len() != 2 {
                    return Some(Err(RustSemError::intrinsic_arity(method, 2, args.len())));
                }
                let ordering = match parse_ordering(&args[1]) {
                    Ok(ordering) => ordering,
                    Err(err) => return Some(Err(err)),
                };
                eval_atomic_op(
                    AtomicOp::FetchOr,
                    &mut updated_receiver,
                    Some(args[0].clone()),
                    ordering,
                )
            }
            "fetch_xor" => {
                if args.len() != 2 {
                    return Some(Err(RustSemError::intrinsic_arity(method, 2, args.len())));
                }
                let ordering = match parse_ordering(&args[1]) {
                    Ok(ordering) => ordering,
                    Err(err) => return Some(Err(err)),
                };
                eval_atomic_op(
                    AtomicOp::FetchXor,
                    &mut updated_receiver,
                    Some(args[0].clone()),
                    ordering,
                )
            }
            _ => return None,
        };

        Some(match result {
            EvalResult::Value(value) => Ok((value, updated_receiver)),
            EvalResult::Error(err) => Err(RustSemError::Eval(err)),
            EvalResult::Return(_)
            | EvalResult::Break { .. }
            | EvalResult::Continue { .. }
            | EvalResult::Panic(_) => {
                unreachable!("atomic evaluator only produces values or errors")
            }
        })
    }
}
