// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Result combinator methods: expect, expect_err, and_then, map_err, or, or_else,
//! ok, err, flatten.

use super::super::Interpreter;
use crate::expr::EvalResult;
use crate::values::{EnumPayload, Value};

impl Interpreter {
    pub(in crate::eval::intrinsics) fn try_result_combinator_method(
        &mut self,
        receiver: &Value,
        method: &str,
        args: &[Value],
    ) -> Option<EvalResult> {
        match (receiver, method) {
            // Result::expect — Ok(x).expect(msg) => x, Err(e).expect(msg) => aborts with msg
            (
                Value::Enum {
                    name,
                    variant,
                    payload,
                },
                "expect",
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
                    let msg = match &args[0] {
                        Value::Str(s) => s.clone(),
                        _ => "Result::expect failed".to_string(),
                    };
                    Some(EvalResult::Panic(msg))
                }
                _ => None,
            },
            // Result::expect_err — Err(e).expect_err(msg) => e, Ok(x).expect_err(msg) => aborts with msg
            (
                Value::Enum {
                    name,
                    variant,
                    payload,
                },
                "expect_err",
            ) if name == "Result" && args.len() == 1 => match variant.as_str() {
                "Ok" => {
                    let msg = match &args[0] {
                        Value::Str(s) => s.clone(),
                        _ => "Result::expect_err failed".to_string(),
                    };
                    Some(EvalResult::Panic(msg))
                }
                "Err" => match payload.as_ref() {
                    EnumPayload::Tuple(fields) if fields.len() == 1 => {
                        Some(EvalResult::Value(fields[0].clone()))
                    }
                    _ => Some(EvalResult::Error(
                        "Result::Err has invalid payload".to_string(),
                    )),
                },
                _ => None,
            },
            // Result::and_then — Ok(x).and_then(f) => f(x), Err(e).and_then(f) => Err(e)
            (
                Value::Enum {
                    name,
                    variant,
                    payload,
                },
                "and_then",
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
                    Some(self.call_callable_value(&args[0], vec![inner], &[]))
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
            // Result::map_err — Ok(x).map_err(f) => Ok(x), Err(e).map_err(f) => Err(f(e))
            (
                Value::Enum {
                    name,
                    variant,
                    payload,
                },
                "map_err",
            ) if name == "Result" && args.len() == 1 => match variant.as_str() {
                "Ok" => match payload.as_ref() {
                    EnumPayload::Tuple(fields) if fields.len() == 1 => {
                        Some(EvalResult::Value(Self::result_value(Ok(fields[0].clone()))))
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
                    Some(match self.call_callable_value(&args[0], vec![err], &[]) {
                        EvalResult::Value(new_err) => {
                            EvalResult::Value(Self::result_value(Err(new_err)))
                        }
                        other => other,
                    })
                }
                _ => None,
            },
            // Result::or — Ok(x).or(y) => Ok(x), Err(e).or(y) => y
            (
                Value::Enum {
                    name,
                    variant,
                    payload,
                },
                "or",
            ) if name == "Result" && args.len() == 1 => match variant.as_str() {
                "Ok" => match payload.as_ref() {
                    EnumPayload::Tuple(fields) if fields.len() == 1 => {
                        Some(EvalResult::Value(Self::result_value(Ok(fields[0].clone()))))
                    }
                    _ => Some(EvalResult::Error(
                        "Result::Ok has invalid payload".to_string(),
                    )),
                },
                "Err" => Some(EvalResult::Value(args[0].clone())),
                _ => None,
            },
            // Result::or_else — Ok(x).or_else(f) => Ok(x), Err(e).or_else(f) => f(e)
            (
                Value::Enum {
                    name,
                    variant,
                    payload,
                },
                "or_else",
            ) if name == "Result" && args.len() == 1 => match variant.as_str() {
                "Ok" => match payload.as_ref() {
                    EnumPayload::Tuple(fields) if fields.len() == 1 => {
                        Some(EvalResult::Value(Self::result_value(Ok(fields[0].clone()))))
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
            // Result::ok — Ok(x).ok() => Some(x), Err(e).ok() => None
            (
                Value::Enum {
                    name,
                    variant,
                    payload,
                },
                "ok",
            ) if name == "Result" && args.is_empty() => match variant.as_str() {
                "Ok" => match payload.as_ref() {
                    EnumPayload::Tuple(fields) if fields.len() == 1 => Some(EvalResult::Value(
                        Self::option_value(Some(fields[0].clone())),
                    )),
                    _ => Some(EvalResult::Error(
                        "Result::Ok has invalid payload".to_string(),
                    )),
                },
                "Err" => Some(EvalResult::Value(Self::option_value(None))),
                _ => None,
            },
            // Result::err — Ok(x).err() => None, Err(e).err() => Some(e)
            (
                Value::Enum {
                    name,
                    variant,
                    payload,
                },
                "err",
            ) if name == "Result" && args.is_empty() => match variant.as_str() {
                "Ok" => Some(EvalResult::Value(Self::option_value(None))),
                "Err" => match payload.as_ref() {
                    EnumPayload::Tuple(fields) if fields.len() == 1 => Some(EvalResult::Value(
                        Self::option_value(Some(fields[0].clone())),
                    )),
                    _ => Some(EvalResult::Error(
                        "Result::Err has invalid payload".to_string(),
                    )),
                },
                _ => None,
            },
            // Result::flatten — Ok(Ok(x)).flatten() => Ok(x), Ok(Err(e)).flatten() => Err(e)
            (
                Value::Enum {
                    name,
                    variant,
                    payload,
                },
                "flatten",
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
                    if matches!(&inner, Value::Enum { name, .. } if name == "Result") {
                        Some(EvalResult::Value(inner))
                    } else {
                        Some(EvalResult::Error(
                            "Result::flatten() requires nested Result payload".to_string(),
                        ))
                    }
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
            // Arity-check error arms for Result combinator methods
            (Value::Enum { name, .. }, "expect") if name == "Result" => Some(EvalResult::Error(
                format!("method `expect` takes 1 arg, got {}", args.len()),
            )),
            (Value::Enum { name, .. }, "expect_err") if name == "Result" => {
                Some(EvalResult::Error(format!(
                    "method `expect_err` takes 1 arg, got {}",
                    args.len()
                )))
            }
            (Value::Enum { name, .. }, "and_then") if name == "Result" => Some(EvalResult::Error(
                format!("method `and_then` takes 1 arg, got {}", args.len()),
            )),
            (Value::Enum { name, .. }, "map_err") if name == "Result" => Some(EvalResult::Error(
                format!("method `map_err` takes 1 arg, got {}", args.len()),
            )),
            (Value::Enum { name, .. }, "or") if name == "Result" => Some(EvalResult::Error(
                format!("method `or` takes 1 arg, got {}", args.len()),
            )),
            (Value::Enum { name, .. }, "or_else") if name == "Result" => Some(EvalResult::Error(
                format!("method `or_else` takes 1 arg, got {}", args.len()),
            )),
            (Value::Enum { name, .. }, "ok") if name == "Result" => Some(EvalResult::Error(
                format!("method `ok` takes 0 args, got {}", args.len()),
            )),
            (Value::Enum { name, .. }, "err") if name == "Result" => Some(EvalResult::Error(
                format!("method `err` takes 0 args, got {}", args.len()),
            )),
            (Value::Enum { name, .. }, "flatten") if name == "Result" => Some(EvalResult::Error(
                format!("method `flatten` takes 0 args, got {}", args.len()),
            )),
            _ => None,
        }
    }
}
