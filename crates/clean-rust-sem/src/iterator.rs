// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Full Rust Iterator protocol for semantics verification.
//!
//! Extends the for-loop support beyond Array/Tuple to the complete
//! `Iterator` trait protocol: `IntoIterator::into_iter()` followed by
//! repeated `Iterator::next()` calls until `None`.
//!
//! ## Supported iterable types
//!
//! - **Range** (`start..end`, `start..=end`): integer ranges
//! - **Vec\<T\>**: owned vector iteration
//! - **Array** (`[T; N]`): fixed-size array iteration
//! - **Slice** (`&[T]`): borrowed slice iteration
//! - **HashMap\<K, V\>**: key-value pair iteration
//!
//! ## Desugaring
//!
//! ```text
//! for pattern in iterable { body }
//! ```
//! becomes:
//! ```text
//! let mut __iter = IntoIterator::into_iter(iterable);
//! loop {
//!     match Iterator::next(&mut __iter) {
//!         Some(pattern) => { body },
//!         None => break,
//!     }
//! }
//! ```

use crate::error::RustSemError;
use crate::expr::{Expr, MatchArm, Pattern, Stmt};
use crate::types::{Lifetime, Mutability, RustType, UintType};
use crate::values::Value;

/// Describes how a concrete type implements the `Iterator` trait.
///
/// Each variant captures the item type yielded by `Iterator::next()`.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum IteratorProtocol {
    /// Integer range iterator — yields successive integers.
    Range {
        element_ty: RustType,
        inclusive: bool,
    },
    /// Owned `Vec<T>` — yields owned `T` values.
    Vec { element_ty: RustType },
    /// Fixed-size array `[T; N]` — yields owned `T` values.
    Array { element_ty: RustType, len: usize },
    /// Borrowed slice `&[T]` — yields `&T` references.
    Slice { element_ty: RustType },
    /// `HashMap<K, V>` — yields `(K, V)` pairs.
    HashMap {
        key_ty: RustType,
        value_ty: RustType,
    },
}

impl IteratorProtocol {
    /// The `Item` associated type yielded by this iterator.
    #[must_use]
    pub fn item_type(&self) -> RustType {
        match self {
            Self::Range { element_ty, .. } | Self::Vec { element_ty } => element_ty.clone(),
            Self::Array { element_ty, .. } => element_ty.clone(),
            Self::Slice { element_ty } => RustType::Reference {
                lifetime: Lifetime::Anonymous(0),
                mutability: Mutability::Shared,
                inner: Box::new(element_ty.clone()),
            },
            Self::HashMap { key_ty, value_ty } => {
                RustType::Tuple(vec![key_ty.clone(), value_ty.clone()])
            }
        }
    }
}

/// Desugared representation of a `for` loop (inspectable before expr conversion).
#[derive(Debug, Clone)]
pub struct ForLoopDesugar {
    /// Synthetic iterator variable name (`__iter`).
    pub iter_var: String,
    /// `IntoIterator::into_iter(iterable)` call.
    pub into_iter_call: Expr,
    /// `Iterator::next(&mut __iter)` call.
    pub next_call: Expr,
    /// Binding pattern for each element.
    pub pattern: Pattern,
    /// Loop body expression.
    pub body: Expr,
    /// Optional loop label.
    pub label: Option<String>,
    /// Resolved iterator protocol.
    pub protocol: IteratorProtocol,
}

/// Resolve the [`IteratorProtocol`] for a [`RustType`] via `IntoIterator`.
///
/// # Errors
///
/// Returns [`RustSemError::Iteration`] when the type is not iterable.
pub fn resolve_into_iterator(ty: &RustType) -> Result<IteratorProtocol, RustSemError> {
    match ty {
        RustType::Array { element, len } => {
            let Some(len) = len.as_usize(&std::collections::HashMap::new()) else {
                return Err(RustSemError::Iteration(
                    "array iterator requires a concrete usize length".to_string(),
                ));
            };
            Ok(IteratorProtocol::Array {
                element_ty: *element.clone(),
                len,
            })
        }

        RustType::Vec { element } => Ok(IteratorProtocol::Vec {
            element_ty: *element.clone(),
        }),

        RustType::Slice { elem } => Ok(IteratorProtocol::Slice {
            element_ty: *elem.clone(),
        }),

        // &[T] — reference to slice
        RustType::Reference { inner, .. } if matches!(inner.as_ref(), RustType::Slice { .. }) => {
            let elem = match inner.as_ref() {
                RustType::Slice { elem } => *elem.clone(),
                _ => unreachable!(),
            };
            Ok(IteratorProtocol::Slice { element_ty: elem })
        }

        // &[T; N] — reference to array, iterates like a slice
        RustType::Reference { inner, .. } if matches!(inner.as_ref(), RustType::Array { .. }) => {
            let elem = match inner.as_ref() {
                RustType::Array { element, .. } => *element.clone(),
                _ => unreachable!(),
            };
            Ok(IteratorProtocol::Slice { element_ty: elem })
        }

        // Named types: HashMap, BTreeMap, etc.
        RustType::Named {
            name, type_args, ..
        } => resolve_named_into_iterator(name, type_args),

        _ => Err(RustSemError::iteration(format!(
            "type `{ty:?}` does not implement IntoIterator"
        ))),
    }
}

/// Resolve `IntoIterator` for well-known named collection types.
fn resolve_named_into_iterator(
    name: &str,
    type_args: &[RustType],
) -> Result<IteratorProtocol, RustSemError> {
    match name {
        "HashMap" | "BTreeMap" => {
            let key_ty = type_args.first().cloned().unwrap_or(RustType::Unit);
            let value_ty = type_args.get(1).cloned().unwrap_or(RustType::Unit);
            Ok(IteratorProtocol::HashMap { key_ty, value_ty })
        }
        "Vec" => {
            let element_ty = type_args.first().cloned().unwrap_or(RustType::Unit);
            Ok(IteratorProtocol::Vec { element_ty })
        }
        "HashSet" | "BTreeSet" => {
            let element_ty = type_args.first().cloned().unwrap_or(RustType::Unit);
            Ok(IteratorProtocol::Vec { element_ty })
        }
        _ => Err(RustSemError::iteration(format!(
            "named type `{name}` does not implement IntoIterator"
        ))),
    }
}

/// Value-level counterpart to [`resolve_into_iterator`] for runtime values.
///
/// # Errors
///
/// Returns [`RustSemError::Iteration`] when the value is not iterable.
pub fn resolve_value_iterator(value: &Value) -> Result<IteratorProtocol, RustSemError> {
    match value {
        Value::Array(elems) => {
            let element_ty = elems.first().map_or(RustType::Unit, Value::get_type);
            Ok(IteratorProtocol::Array {
                element_ty,
                len: elems.len(),
            })
        }
        Value::Range {
            start,
            end,
            inclusive,
        } => {
            let element_ty = start
                .as_deref()
                .or(end.as_deref())
                .map_or(RustType::Uint(UintType::Usize), Value::get_type);
            Ok(IteratorProtocol::Range {
                element_ty,
                inclusive: *inclusive,
            })
        }
        Value::Struct { name, fields } => {
            // HashMap/BTreeMap struct values store entries under "entries"
            if name == "HashMap" || name == "BTreeMap" {
                let (key_ty, value_ty) = infer_map_entry_types(fields);
                return Ok(IteratorProtocol::HashMap { key_ty, value_ty });
            }
            Err(RustSemError::iteration(format!(
                "struct `{name}` does not implement IntoIterator"
            )))
        }
        _ => Err(RustSemError::iteration(format!(
            "value `{value:?}` is not iterable"
        ))),
    }
}

/// Infer key/value types from a map's struct fields.
fn infer_map_entry_types(
    fields: &std::collections::BTreeMap<String, Value>,
) -> (RustType, RustType) {
    if let Some(Value::Array(entries)) = fields.get("entries") {
        if let Some(Value::Tuple(pair)) = entries.first() {
            let key_ty = pair.first().map_or(RustType::Unit, Value::get_type);
            let val_ty = pair.get(1).map_or(RustType::Unit, Value::get_type);
            return (key_ty, val_ty);
        }
    }
    (RustType::Unit, RustType::Unit)
}

/// Desugar a `for` loop into its `Iterator::next()` expansion.
///
/// Transforms `for <var> in <iterable> { <body> }` into:
/// ```text
/// {
///     let mut __iter = IntoIterator::into_iter(<iterable>);
///     loop {
///         match Iterator::next(&mut __iter) {
///             Some(__val) => { let <var> = __val; <body> },
///             None => break,
///         }
///     }
/// }
/// ```
///
/// # Errors
///
/// Returns [`RustSemError::Iteration`] if `iterable_ty` does not implement
/// `IntoIterator`.
pub fn desugar_for_loop(
    var: &Pattern,
    iterable: &Expr,
    iterable_ty: &RustType,
    body: &Expr,
    label: Option<&str>,
) -> Result<Expr, RustSemError> {
    let ds = build_desugar(var, iterable, iterable_ty, body, label)?;
    let item_ty = ds.protocol.item_type();

    let some_arm = MatchArm {
        pattern: Pattern::EnumVariant {
            enum_name: "Option".to_string(),
            variant: "Some".to_string(),
            payload: crate::expr::EnumPatternPayload::Tuple(vec![Pattern::Binding {
                name: "__val".to_string(),
                mutable: false,
                subpattern: None,
            }]),
        },
        guard: None,
        body: Expr::Block {
            stmts: vec![Stmt::Let {
                pattern: var.clone(),
                ty: Some(item_ty),
                init: Some(Box::new(Expr::Var {
                    name: "__val".to_string(),
                    local_idx: 0,
                })),
                else_block: None,
            }],
            expr: Some(Box::new(body.clone())),
        },
    };

    let none_arm = MatchArm {
        pattern: Pattern::EnumVariant {
            enum_name: "Option".to_string(),
            variant: "None".to_string(),
            payload: crate::expr::EnumPatternPayload::Unit,
        },
        guard: None,
        body: Expr::Break {
            label: label.map(str::to_string),
            value: None,
        },
    };

    Ok(Expr::Block {
        stmts: vec![Stmt::Let {
            pattern: Pattern::Binding {
                name: ds.iter_var,
                mutable: true,
                subpattern: None,
            },
            ty: None,
            init: Some(Box::new(ds.into_iter_call)),
            else_block: None,
        }],
        expr: Some(Box::new(Expr::Loop {
            label: label.map(str::to_string),
            body: Box::new(Expr::Match {
                scrutinee: Box::new(ds.next_call),
                arms: vec![some_arm, none_arm],
            }),
        })),
    })
}

/// Extract elements from a [`Value`] using the full iterator protocol.
///
/// This extends the original `for_loop_elements` (Array/Tuple only) to
/// support all iterable types via [`resolve_value_iterator`].
///
/// # Errors
///
/// Returns [`RustSemError::Iteration`] if the value is not iterable.
pub fn extract_iter_elements(value: &Value) -> Result<Vec<Value>, RustSemError> {
    match value {
        Value::Array(elems) => Ok(elems.clone()),
        Value::Tuple(elems) => Ok(elems.clone()),
        Value::Range {
            start,
            end,
            inclusive,
        } => extract_range_elements(start.as_deref(), end.as_deref(), *inclusive),
        Value::Struct { name, fields } if name == "HashMap" || name == "BTreeMap" => {
            extract_map_elements(fields)
        }
        _ => Err(RustSemError::iteration(format!(
            "cannot extract elements from `{:?}`",
            value.get_type()
        ))),
    }
}

/// Extract elements from a range value.
fn extract_range_elements(
    start: Option<&Value>,
    end: Option<&Value>,
    inclusive: bool,
) -> Result<Vec<Value>, RustSemError> {
    match (start, end) {
        (
            Some(Value::Int {
                value: s, ty: s_ty, ..
            }),
            Some(Value::Int {
                value: e, ty: e_ty, ..
            }),
        ) => {
            if s_ty != e_ty {
                return Err(RustSemError::iteration(
                    "range bounds must use the same integer type",
                ));
            }
            // Iterate via the native range iterators so that `end == i128::MAX`
            // does not overflow when computing an exclusive upper bound: an
            // inclusive range cannot be re-expressed as `end + 1`. Both forms
            // yield no elements when `start > end`, matching Rust semantics.
            let elems = if inclusive {
                (*s..=*e)
                    .map(|value| Value::Int { value, ty: *s_ty })
                    .collect()
            } else {
                (*s..*e)
                    .map(|value| Value::Int { value, ty: *s_ty })
                    .collect()
            };
            Ok(elems)
        }
        (
            Some(Value::Uint {
                value: s, ty: s_ty, ..
            }),
            Some(Value::Uint {
                value: e, ty: e_ty, ..
            }),
        ) => {
            if s_ty != e_ty {
                return Err(RustSemError::iteration(
                    "range bounds must use the same integer type",
                ));
            }
            // As above: `end == u128::MAX` would overflow `end + 1`, so use the
            // native inclusive/exclusive iterators directly.
            let elems = if inclusive {
                (*s..=*e)
                    .map(|value| Value::Uint { value, ty: *s_ty })
                    .collect()
            } else {
                (*s..*e)
                    .map(|value| Value::Uint { value, ty: *s_ty })
                    .collect()
            };
            Ok(elems)
        }
        (Some(Value::Char(s)), Some(Value::Char(e))) => {
            // `char` iterators handle the `end == char::MAX` boundary without
            // an explicit `+ 1`, avoiding a scalar-value overflow.
            let elems = if inclusive {
                (*s..=*e).map(Value::Char).collect()
            } else {
                (*s..*e).map(Value::Char).collect()
            };
            Ok(elems)
        }
        _ => Err(RustSemError::iteration(
            "unsupported or unbounded range in for loop",
        )),
    }
}

/// Extract `(key, value)` pairs from a map struct value.
fn extract_map_elements(
    fields: &std::collections::BTreeMap<String, Value>,
) -> Result<Vec<Value>, RustSemError> {
    match fields.get("entries") {
        Some(Value::Array(entries)) => Ok(entries.clone()),
        _ => Ok(Vec::new()),
    }
}

/// Build a `ForLoopDesugar` from the high-level for-loop components.
///
/// This is the structured form that callers can inspect before converting
/// to an [`Expr`] via [`desugar_for_loop`].
///
/// # Errors
///
/// Returns [`RustSemError::Iteration`] if the iterable type does not
/// implement `IntoIterator`.
pub fn build_desugar(
    pattern: &Pattern,
    iterable: &Expr,
    iterable_ty: &RustType,
    body: &Expr,
    label: Option<&str>,
) -> Result<ForLoopDesugar, RustSemError> {
    let protocol = resolve_into_iterator(iterable_ty)?;
    let iter_var = "__iter".to_string();

    let into_iter_call = Expr::Call {
        func: Box::new(Expr::Var {
            name: "IntoIterator::into_iter".to_string(),
            local_idx: 0,
        }),
        args: vec![iterable.clone()],
        type_args: vec![],
    };

    let next_call = Expr::MethodCall {
        receiver: Box::new(Expr::AddrOf {
            mutability: Mutability::Mutable,
            expr: Box::new(Expr::Var {
                name: iter_var.clone(),
                local_idx: 0,
            }),
        }),
        method: "next".to_string(),
        args: vec![],
        type_args: vec![],
    };

    Ok(ForLoopDesugar {
        iter_var,
        into_iter_call,
        next_call,
        pattern: pattern.clone(),
        body: body.clone(),
        label: label.map(str::to_string),
        protocol,
    })
}

#[cfg(test)]
#[path = "iterator_tests.rs"]
mod tests;
