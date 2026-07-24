// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Intrinsic basic methods on Result values: unwrap, unwrap_err, map, map_or,
//! map_or_else, unwrap_or, unwrap_or_else, is_ok, is_err, as_ref, as_mut.
//!
//! Combinator methods (expect, and_then, map_err, or, or_else, ok, err, flatten)
//! are in `result_combinators.rs`.

use super::super::Interpreter;
use crate::expr::EvalResult;
use crate::types::Mutability;
use crate::values::{EnumPayload, Value};

impl Interpreter {
    pub(in crate::eval) fn try_result_intrinsic_method(
        &mut self,
        receiver: &Value,
        method: &str,
        args: &[Value],
    ) -> Option<EvalResult> {
        // Try basic Result methods first, then combinators
        self.try_result_basic_method(receiver, method, args)
            .or_else(|| self.try_result_combinator_method(receiver, method, args))
    }

    fn try_result_basic_method(
        &mut self,
        receiver: &Value,
        method: &str,
        args: &[Value],
    ) -> Option<EvalResult> {
        match (receiver, method) {
            (
                Value::Enum {
                    name,
                    variant,
                    payload,
                },
                "unwrap",
            ) if name == "Result" && args.is_empty() => match variant.as_str() {
                "Ok" => match payload.as_ref() {
                    EnumPayload::Tuple(fields) if fields.len() == 1 => {
                        Some(EvalResult::Value(fields[0].clone()))
                    }
                    _ => Some(EvalResult::Error(
                        "Result::Ok has invalid payload".to_string(),
                    )),
                },
                "Err" => Some(EvalResult::Panic(
                    "called `Result::unwrap()` on an `Err` value".to_string(),
                )),
                _ => None,
            },
            (
                Value::Enum {
                    name,
                    variant,
                    payload,
                },
                "map",
            ) if name == "Result" && args.len() == 1 => match variant.as_str() {
                "Ok" => {
                    let inner = match payload.as_ref() {
                        EnumPayload::Tuple(fields) if fields.len() == 1 => fields[0].clone(),
                        _ => {
                            return Some(EvalResult::Error(
                                "Result::Ok has invalid payload".to_string(),
                            ));
                        }
                    };
                    Some(match self.call_callable_value(&args[0], vec![inner], &[]) {
                        EvalResult::Value(value) => {
                            EvalResult::Value(Self::result_value(Ok(value)))
                        }
                        other => other,
                    })
                }
                "Err" => match payload.as_ref() {
                    EnumPayload::Tuple(fields) if fields.len() == 1 => Some(EvalResult::Value(
                        Self::result_value(Err(fields[0].clone())),
                    )),
                    _ => Some(EvalResult::Error(
                        "Result::Err has invalid payload".to_string(),
                    )),
                },
                _ => None,
            },
            (
                Value::Enum {
                    name,
                    variant,
                    payload,
                },
                "map_or",
            ) if name == "Result" && args.len() == 2 => match variant.as_str() {
                "Ok" => {
                    let inner = match payload.as_ref() {
                        EnumPayload::Tuple(fields) if fields.len() == 1 => fields[0].clone(),
                        _ => {
                            return Some(EvalResult::Error(
                                "Result::Ok has invalid payload".to_string(),
                            ));
                        }
                    };
                    Some(self.call_callable_value(&args[1], vec![inner], &[]))
                }
                "Err" => Some(EvalResult::Value(args[0].clone())),
                _ => None,
            },
            (
                Value::Enum {
                    name,
                    variant,
                    payload,
                },
                "map_or_else",
            ) if name == "Result" && args.len() == 2 => match variant.as_str() {
                "Ok" => {
                    let inner = match payload.as_ref() {
                        EnumPayload::Tuple(fields) if fields.len() == 1 => fields[0].clone(),
                        _ => {
                            return Some(EvalResult::Error(
                                "Result::Ok has invalid payload".to_string(),
                            ));
                        }
                    };
                    Some(self.call_callable_value(&args[1], vec![inner], &[]))
                }
                "Err" => {
                    let err = match payload.as_ref() {
                        EnumPayload::Tuple(fields) if fields.len() == 1 => fields[0].clone(),
                        _ => {
                            return Some(EvalResult::Error(
                                "Result::Err has invalid payload".to_string(),
                            ));
                        }
                    };
                    Some(self.call_callable_value(&args[0], vec![err], &[]))
                }
                _ => None,
            },
            (
                Value::Enum {
                    name,
                    variant,
                    payload,
                },
                "unwrap_or",
            ) if name == "Result" && args.len() == 1 => match variant.as_str() {
                "Ok" => match payload.as_ref() {
                    EnumPayload::Tuple(fields) if fields.len() == 1 => {
                        Some(EvalResult::Value(fields[0].clone()))
                    }
                    _ => Some(EvalResult::Error(
                        "Result::Ok has invalid payload".to_string(),
                    )),
                },
                "Err" => Some(EvalResult::Value(args[0].clone())),
                _ => None,
            },
            (
                Value::Enum {
                    name,
                    variant,
                    payload,
                },
                "unwrap_or_else",
            ) if name == "Result" && args.len() == 1 => match variant.as_str() {
                "Ok" => match payload.as_ref() {
                    EnumPayload::Tuple(fields) if fields.len() == 1 => {
                        Some(EvalResult::Value(fields[0].clone()))
                    }
                    _ => Some(EvalResult::Error(
                        "Result::Ok has invalid payload".to_string(),
                    )),
                },
                "Err" => {
                    let err = match payload.as_ref() {
                        EnumPayload::Tuple(fields) if fields.len() == 1 => fields[0].clone(),
                        _ => {
                            return Some(EvalResult::Error(
                                "Result::Err has invalid payload".to_string(),
                            ));
                        }
                    };
                    Some(self.call_callable_value(&args[0], vec![err], &[]))
                }
                _ => None,
            },
            (Value::Enum { name, variant, .. }, "is_ok") if name == "Result" && args.is_empty() => {
                Some(EvalResult::Value(Value::Bool(variant == "Ok")))
            }
            (Value::Enum { name, variant, .. }, "is_err")
                if name == "Result" && args.is_empty() =>
            {
                Some(EvalResult::Value(Value::Bool(variant == "Err")))
            }
            (
                Value::Enum {
                    name,
                    variant,
                    payload,
                },
                "as_ref",
            ) if name == "Result" && args.is_empty() => match variant.as_str() {
                "Ok" => {
                    let inner = match payload.as_ref() {
                        EnumPayload::Tuple(fields) if fields.len() == 1 => fields[0].clone(),
                        _ => {
                            return Some(EvalResult::Error(
                                "Result::Ok has invalid payload".to_string(),
                            ));
                        }
                    };
                    Some(match self.preserved_reference(inner, Mutability::Shared) {
                        Ok(reference) => EvalResult::Value(Self::result_value(Ok(reference))),
                        Err(err) => EvalResult::Error(err.to_string()),
                    })
                }
                "Err" => {
                    let err = match payload.as_ref() {
                        EnumPayload::Tuple(fields) if fields.len() == 1 => fields[0].clone(),
                        _ => {
                            return Some(EvalResult::Error(
                                "Result::Err has invalid payload".to_string(),
                            ));
                        }
                    };
                    Some(match self.preserved_reference(err, Mutability::Shared) {
                        Ok(reference) => EvalResult::Value(Self::result_value(Err(reference))),
                        Err(alloc_err) => EvalResult::Error(alloc_err.to_string()),
                    })
                }
                _ => None,
            },
            (
                Value::Enum {
                    name,
                    variant,
                    payload,
                },
                "as_mut",
            ) if name == "Result" && args.is_empty() => match variant.as_str() {
                "Ok" => {
                    let inner = match payload.as_ref() {
                        EnumPayload::Tuple(fields) if fields.len() == 1 => fields[0].clone(),
                        _ => {
                            return Some(EvalResult::Error(
                                "Result::Ok has invalid payload".to_string(),
                            ));
                        }
                    };
                    Some(match self.preserved_reference(inner, Mutability::Mutable) {
                        Ok(reference) => EvalResult::Value(Self::result_value(Ok(reference))),
                        Err(err) => EvalResult::Error(err.to_string()),
                    })
                }
                "Err" => {
                    let err = match payload.as_ref() {
                        EnumPayload::Tuple(fields) if fields.len() == 1 => fields[0].clone(),
                        _ => {
                            return Some(EvalResult::Error(
                                "Result::Err has invalid payload".to_string(),
                            ));
                        }
                    };
                    Some(match self.preserved_reference(err, Mutability::Mutable) {
                        Ok(reference) => EvalResult::Value(Self::result_value(Err(reference))),
                        Err(alloc_err) => EvalResult::Error(alloc_err.to_string()),
                    })
                }
                _ => None,
            },
            // Arity-check error arms for basic Result methods
            (Value::Enum { name, .. }, "unwrap") if name == "Result" => Some(EvalResult::Error(
                format!("method `unwrap` takes 0 args, got {}", args.len()),
            )),
            (Value::Enum { name, .. }, "unwrap_err") if name == "Result" => {
                Some(EvalResult::Error(format!(
                    "method `unwrap_err` takes 0 args, got {}",
                    args.len()
                )))
            }
            (Value::Enum { name, .. }, "map") if name == "Result" => Some(EvalResult::Error(
                format!("method `map` takes 1 arg, got {}", args.len()),
            )),
            (Value::Enum { name, .. }, "map_or") if name == "Result" => Some(EvalResult::Error(
                format!("method `map_or` takes 2 args, got {}", args.len()),
            )),
            (Value::Enum { name, .. }, "map_or_else") if name == "Result" => {
                Some(EvalResult::Error(format!(
                    "method `map_or_else` takes 2 args, got {}",
                    args.len()
                )))
            }
            (Value::Enum { name, .. }, "unwrap_or") if name == "Result" => Some(EvalResult::Error(
                format!("method `unwrap_or` takes 1 arg, got {}", args.len()),
            )),
            (Value::Enum { name, .. }, "unwrap_or_else") if name == "Result" => {
                Some(EvalResult::Error(format!(
                    "method `unwrap_or_else` takes 1 arg, got {}",
                    args.len()
                )))
            }
            (Value::Enum { name, .. }, "is_ok") if name == "Result" => Some(EvalResult::Error(
                format!("method `is_ok` takes 0 args, got {}", args.len()),
            )),
            (Value::Enum { name, .. }, "is_err") if name == "Result" => Some(EvalResult::Error(
                format!("method `is_err` takes 0 args, got {}", args.len()),
            )),
            (Value::Enum { name, .. }, "as_ref") if name == "Result" => Some(EvalResult::Error(
                format!("method `as_ref` takes 0 args, got {}", args.len()),
            )),
            (Value::Enum { name, .. }, "as_mut") if name == "Result" => Some(EvalResult::Error(
                format!("method `as_mut` takes 0 args, got {}", args.len()),
            )),
            _ => None,
        }
    }
}
