// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Intrinsic methods on Option values: unwrap, unwrap_or, unwrap_or_else, expect,
//! map, map_or, map_or_else, is_some, is_none, as_ref, as_mut, and_then, filter,
//! flatten, ok_or, ok_or_else, or, or_else.

use super::super::Interpreter;
use crate::expr::EvalResult;
use crate::types::Mutability;
use crate::values::{EnumPayload, Value};

impl Interpreter {
    pub(in crate::eval) fn try_option_intrinsic_method(
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
            ) if name == "Option" && args.is_empty() => match variant.as_str() {
                "Some" => match payload.as_ref() {
                    EnumPayload::Tuple(fields) if fields.len() == 1 => {
                        Some(EvalResult::Value(fields[0].clone()))
                    }
                    _ => Some(EvalResult::Error(
                        "Option::Some has invalid payload".to_string(),
                    )),
                },
                "None" => Some(EvalResult::Panic(
                    "called `Option::unwrap()` on a `None` value".to_string(),
                )),
                _ => None,
            },
            (
                Value::Enum {
                    name,
                    variant,
                    payload,
                },
                "unwrap_err",
            ) if name == "Result" && args.is_empty() => match variant.as_str() {
                "Ok" => Some(EvalResult::Panic(
                    "called `Result::unwrap_err()` on an `Ok` value".to_string(),
                )),
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
            (
                Value::Enum {
                    name,
                    variant,
                    payload,
                },
                "unwrap_or",
            ) if name == "Option" && args.len() == 1 => match variant.as_str() {
                "Some" => match payload.as_ref() {
                    EnumPayload::Tuple(fields) if fields.len() == 1 => {
                        Some(EvalResult::Value(fields[0].clone()))
                    }
                    _ => Some(EvalResult::Error(
                        "Option::Some has invalid payload".to_string(),
                    )),
                },
                "None" => Some(EvalResult::Value(args[0].clone())),
                _ => None,
            },
            (
                Value::Enum {
                    name,
                    variant,
                    payload,
                },
                "unwrap_or_else",
            ) if name == "Option" && args.len() == 1 => match variant.as_str() {
                "Some" => match payload.as_ref() {
                    EnumPayload::Tuple(fields) if fields.len() == 1 => {
                        Some(EvalResult::Value(fields[0].clone()))
                    }
                    _ => Some(EvalResult::Error(
                        "Option::Some has invalid payload".to_string(),
                    )),
                },
                "None" => Some(self.call_callable_value(&args[0], vec![], &[])),
                _ => None,
            },
            (
                Value::Enum {
                    name,
                    variant,
                    payload,
                },
                "expect",
            ) if name == "Option" && args.len() == 1 => match variant.as_str() {
                "Some" => match payload.as_ref() {
                    EnumPayload::Tuple(fields) if fields.len() == 1 => {
                        Some(EvalResult::Value(fields[0].clone()))
                    }
                    _ => Some(EvalResult::Error(
                        "Option::Some has invalid payload".to_string(),
                    )),
                },
                "None" => {
                    let msg = match &args[0] {
                        Value::Str(s) => s.clone(),
                        _ => "Option::expect failed".to_string(),
                    };
                    Some(EvalResult::Panic(msg))
                }
                _ => None,
            },
            (
                Value::Enum {
                    name,
                    variant,
                    payload,
                },
                "map",
            ) if name == "Option" && args.len() == 1 => match variant.as_str() {
                "Some" => {
                    let inner = match payload.as_ref() {
                        EnumPayload::Tuple(fields) if fields.len() == 1 => fields[0].clone(),
                        _ => {
                            return Some(EvalResult::Error(
                                "Option::Some has invalid payload".to_string(),
                            ));
                        }
                    };
                    Some(match self.call_callable_value(&args[0], vec![inner], &[]) {
                        EvalResult::Value(value) => {
                            EvalResult::Value(Self::option_value(Some(value)))
                        }
                        other => other,
                    })
                }
                "None" => Some(EvalResult::Value(Self::option_value(None))),
                _ => None,
            },
            (
                Value::Enum {
                    name,
                    variant,
                    payload,
                },
                "map_or",
            ) if name == "Option" && args.len() == 2 => match variant.as_str() {
                "Some" => {
                    let inner = match payload.as_ref() {
                        EnumPayload::Tuple(fields) if fields.len() == 1 => fields[0].clone(),
                        _ => {
                            return Some(EvalResult::Error(
                                "Option::Some has invalid payload".to_string(),
                            ));
                        }
                    };
                    Some(self.call_callable_value(&args[1], vec![inner], &[]))
                }
                "None" => Some(EvalResult::Value(args[0].clone())),
                _ => None,
            },
            (
                Value::Enum {
                    name,
                    variant,
                    payload,
                },
                "map_or_else",
            ) if name == "Option" && args.len() == 2 => match variant.as_str() {
                "Some" => {
                    let inner = match payload.as_ref() {
                        EnumPayload::Tuple(fields) if fields.len() == 1 => fields[0].clone(),
                        _ => {
                            return Some(EvalResult::Error(
                                "Option::Some has invalid payload".to_string(),
                            ));
                        }
                    };
                    Some(self.call_callable_value(&args[1], vec![inner], &[]))
                }
                "None" => Some(self.call_callable_value(&args[0], vec![], &[])),
                _ => None,
            },
            (Value::Enum { name, variant, .. }, "is_some")
                if name == "Option" && args.is_empty() =>
            {
                Some(EvalResult::Value(Value::Bool(variant == "Some")))
            }
            (Value::Enum { name, variant, .. }, "is_none")
                if name == "Option" && args.is_empty() =>
            {
                Some(EvalResult::Value(Value::Bool(variant == "None")))
            }
            (
                Value::Enum {
                    name,
                    variant,
                    payload,
                },
                "as_ref",
            ) if name == "Option" && args.is_empty() => match variant.as_str() {
                "Some" => {
                    let inner = match payload.as_ref() {
                        EnumPayload::Tuple(fields) if fields.len() == 1 => fields[0].clone(),
                        _ => {
                            return Some(EvalResult::Error(
                                "Option::Some has invalid payload".to_string(),
                            ));
                        }
                    };
                    Some(match self.preserved_reference(inner, Mutability::Shared) {
                        Ok(reference) => EvalResult::Value(Self::option_value(Some(reference))),
                        Err(err) => EvalResult::Error(err.to_string()),
                    })
                }
                "None" => Some(EvalResult::Value(Self::option_value(None))),
                _ => None,
            },
            (
                Value::Enum {
                    name,
                    variant,
                    payload,
                },
                "as_mut",
            ) if name == "Option" && args.is_empty() => match variant.as_str() {
                "Some" => {
                    let inner = match payload.as_ref() {
                        EnumPayload::Tuple(fields) if fields.len() == 1 => fields[0].clone(),
                        _ => {
                            return Some(EvalResult::Error(
                                "Option::Some has invalid payload".to_string(),
                            ));
                        }
                    };
                    Some(match self.preserved_reference(inner, Mutability::Mutable) {
                        Ok(reference) => EvalResult::Value(Self::option_value(Some(reference))),
                        Err(err) => EvalResult::Error(err.to_string()),
                    })
                }
                "None" => Some(EvalResult::Value(Self::option_value(None))),
                _ => None,
            },
            // Option::and_then — flatmap: Some(x).and_then(f) => f(x), None.and_then(f) => None
            (
                Value::Enum {
                    name,
                    variant,
                    payload,
                },
                "and_then",
            ) if name == "Option" && args.len() == 1 => match variant.as_str() {
                "Some" => {
                    let inner = match payload.as_ref() {
                        EnumPayload::Tuple(fields) if fields.len() == 1 => fields[0].clone(),
                        _ => {
                            return Some(EvalResult::Error(
                                "Option::Some has invalid payload".to_string(),
                            ));
                        }
                    };
                    Some(self.call_callable_value(&args[0], vec![inner], &[]))
                }
                "None" => Some(EvalResult::Value(Self::option_value(None))),
                _ => None,
            },
            // Option::filter — Some(x).filter(p) => if p(x) { Some(x) } else { None }
            (
                Value::Enum {
                    name,
                    variant,
                    payload,
                },
                "filter",
            ) if name == "Option" && args.len() == 1 => match variant.as_str() {
                "Some" => {
                    let inner = match payload.as_ref() {
                        EnumPayload::Tuple(fields) if fields.len() == 1 => fields[0].clone(),
                        _ => {
                            return Some(EvalResult::Error(
                                "Option::Some has invalid payload".to_string(),
                            ));
                        }
                    };
                    match self.call_callable_value(&args[0], vec![inner.clone()], &[]) {
                        EvalResult::Value(Value::Bool(true)) => {
                            Some(EvalResult::Value(Self::option_value(Some(inner))))
                        }
                        EvalResult::Value(Value::Bool(false)) => {
                            Some(EvalResult::Value(Self::option_value(None)))
                        }
                        other @ EvalResult::Error(_) | other @ EvalResult::Panic(_) => Some(other),
                        _ => Some(EvalResult::Error(
                            "Option::filter predicate must return bool".to_string(),
                        )),
                    }
                }
                "None" => Some(EvalResult::Value(Self::option_value(None))),
                _ => None,
            },
            // Option::flatten — Some(Some(x)).flatten() => Some(x), Some(None).flatten() => None
            (
                Value::Enum {
                    name,
                    variant,
                    payload,
                },
                "flatten",
            ) if name == "Option" && args.is_empty() => match variant.as_str() {
                "Some" => {
                    let inner = match payload.as_ref() {
                        EnumPayload::Tuple(fields) if fields.len() == 1 => fields[0].clone(),
                        _ => {
                            return Some(EvalResult::Error(
                                "Option::Some has invalid payload".to_string(),
                            ));
                        }
                    };
                    if matches!(&inner, Value::Enum { name, .. } if name == "Option") {
                        Some(EvalResult::Value(inner))
                    } else {
                        Some(EvalResult::Error(
                            "Option::flatten() requires nested Option payload".to_string(),
                        ))
                    }
                }
                "None" => Some(EvalResult::Value(Self::option_value(None))),
                _ => None,
            },
            // Option::ok_or — Some(x).ok_or(e) => Ok(x), None.ok_or(e) => Err(e)
            (
                Value::Enum {
                    name,
                    variant,
                    payload,
                },
                "ok_or",
            ) if name == "Option" && args.len() == 1 => match variant.as_str() {
                "Some" => match payload.as_ref() {
                    EnumPayload::Tuple(fields) if fields.len() == 1 => {
                        Some(EvalResult::Value(Self::result_value(Ok(fields[0].clone()))))
                    }
                    _ => Some(EvalResult::Error(
                        "Option::Some has invalid payload".to_string(),
                    )),
                },
                "None" => Some(EvalResult::Value(Self::result_value(Err(args[0].clone())))),
                _ => None,
            },
            // Option::ok_or_else — Some(x).ok_or_else(f) => Ok(x), None.ok_or_else(f) => Err(f())
            (
                Value::Enum {
                    name,
                    variant,
                    payload,
                },
                "ok_or_else",
            ) if name == "Option" && args.len() == 1 => match variant.as_str() {
                "Some" => match payload.as_ref() {
                    EnumPayload::Tuple(fields) if fields.len() == 1 => {
                        Some(EvalResult::Value(Self::result_value(Ok(fields[0].clone()))))
                    }
                    _ => Some(EvalResult::Error(
                        "Option::Some has invalid payload".to_string(),
                    )),
                },
                "None" => match self.call_callable_value(&args[0], vec![], &[]) {
                    EvalResult::Value(err) => Some(EvalResult::Value(Self::result_value(Err(err)))),
                    other => Some(other),
                },
                _ => None,
            },
            // Option::or — Some(x).or(y) => Some(x), None.or(y) => y
            (
                Value::Enum {
                    name,
                    variant,
                    payload,
                },
                "or",
            ) if name == "Option" && args.len() == 1 => match variant.as_str() {
                "Some" => match payload.as_ref() {
                    EnumPayload::Tuple(fields) if fields.len() == 1 => Some(EvalResult::Value(
                        Self::option_value(Some(fields[0].clone())),
                    )),
                    _ => Some(EvalResult::Error(
                        "Option::Some has invalid payload".to_string(),
                    )),
                },
                "None" => Some(EvalResult::Value(args[0].clone())),
                _ => None,
            },
            // Option::or_else — Some(x).or_else(f) => Some(x), None.or_else(f) => f()
            (
                Value::Enum {
                    name,
                    variant,
                    payload,
                },
                "or_else",
            ) if name == "Option" && args.len() == 1 => match variant.as_str() {
                "Some" => match payload.as_ref() {
                    EnumPayload::Tuple(fields) if fields.len() == 1 => Some(EvalResult::Value(
                        Self::option_value(Some(fields[0].clone())),
                    )),
                    _ => Some(EvalResult::Error(
                        "Option::Some has invalid payload".to_string(),
                    )),
                },
                "None" => Some(self.call_callable_value(&args[0], vec![], &[])),
                _ => None,
            },
            // Arity-check error arms
            (Value::Enum { name, .. }, "unwrap") if name == "Option" => Some(EvalResult::Error(
                format!("method `unwrap` takes 0 args, got {}", args.len()),
            )),
            (Value::Enum { name, .. }, "unwrap_or") if name == "Option" => Some(EvalResult::Error(
                format!("method `unwrap_or` takes 1 arg, got {}", args.len()),
            )),
            (Value::Enum { name, .. }, "unwrap_or_else") if name == "Option" => {
                Some(EvalResult::Error(format!(
                    "method `unwrap_or_else` takes 1 arg, got {}",
                    args.len()
                )))
            }
            (Value::Enum { name, .. }, "expect") if name == "Option" => Some(EvalResult::Error(
                format!("method `expect` takes 1 arg, got {}", args.len()),
            )),
            (Value::Enum { name, .. }, "map") if name == "Option" => Some(EvalResult::Error(
                format!("method `map` takes 1 arg, got {}", args.len()),
            )),
            (Value::Enum { name, .. }, "map_or") if name == "Option" => Some(EvalResult::Error(
                format!("method `map_or` takes 2 args, got {}", args.len()),
            )),
            (Value::Enum { name, .. }, "map_or_else") if name == "Option" => {
                Some(EvalResult::Error(format!(
                    "method `map_or_else` takes 2 args, got {}",
                    args.len()
                )))
            }
            (Value::Enum { name, .. }, "is_some") if name == "Option" => Some(EvalResult::Error(
                format!("method `is_some` takes 0 args, got {}", args.len()),
            )),
            (Value::Enum { name, .. }, "is_none") if name == "Option" => Some(EvalResult::Error(
                format!("method `is_none` takes 0 args, got {}", args.len()),
            )),
            (Value::Enum { name, .. }, "and_then") if name == "Option" => Some(EvalResult::Error(
                format!("method `and_then` takes 1 arg, got {}", args.len()),
            )),
            (Value::Enum { name, .. }, "filter") if name == "Option" => Some(EvalResult::Error(
                format!("method `filter` takes 1 arg, got {}", args.len()),
            )),
            (Value::Enum { name, .. }, "ok_or") if name == "Option" => Some(EvalResult::Error(
                format!("method `ok_or` takes 1 arg, got {}", args.len()),
            )),
            (Value::Enum { name, .. }, "ok_or_else") if name == "Option" => {
                Some(EvalResult::Error(format!(
                    "method `ok_or_else` takes 1 arg, got {}",
                    args.len()
                )))
            }
            (Value::Enum { name, .. }, "or") if name == "Option" => Some(EvalResult::Error(
                format!("method `or` takes 1 arg, got {}", args.len()),
            )),
            (Value::Enum { name, .. }, "or_else") if name == "Option" => Some(EvalResult::Error(
                format!("method `or_else` takes 1 arg, got {}", args.len()),
            )),
            (Value::Enum { name, .. }, "flatten") if name == "Option" => Some(EvalResult::Error(
                format!("method `flatten` takes 0 args, got {}", args.len()),
            )),
            (Value::Enum { name, .. }, "as_ref") if name == "Option" => Some(EvalResult::Error(
                format!("method `as_ref` takes 0 args, got {}", args.len()),
            )),
            (Value::Enum { name, .. }, "as_mut") if name == "Option" => Some(EvalResult::Error(
                format!("method `as_mut` takes 0 args, got {}", args.len()),
            )),
            _ => None,
        }
    }
}
