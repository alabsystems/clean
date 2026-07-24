// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pattern matching runtime for Rust semantic patterns.
//!
//! Extracted from `stmt.rs` to keep file and function sizes within bounds.
//! Provides `PatternBindings` and `match_pattern` for runtime pattern dispatch.

use crate::expr::Pattern;
use crate::types::RustType;
use crate::values::Value;

/// Pattern matching result
#[derive(Debug, Clone)]
pub struct PatternBindings {
    /// Bindings created by the pattern: (name, value, mutable, drop_type_hint)
    pub bindings: Vec<(String, Value, bool, Option<RustType>)>,
}

impl PatternBindings {
    #[must_use]
    pub fn new() -> Self {
        Self {
            bindings: Vec::new(),
        }
    }

    pub fn add(&mut self, name: String, value: Value, mutable: bool) {
        self.bindings.push((name, value, mutable, None));
    }

    pub fn add_typed(
        &mut self,
        name: String,
        value: Value,
        mutable: bool,
        drop_type: Option<RustType>,
    ) {
        self.bindings.push((name, value, mutable, drop_type));
    }

    pub fn merge(&mut self, other: PatternBindings) {
        self.bindings.extend(other.bindings);
    }
}

impl Default for PatternBindings {
    fn default() -> Self {
        Self::new()
    }
}

/// Match a pattern against a value, returning bindings on success.
pub fn match_pattern(pattern: &Pattern, value: &Value) -> Option<PatternBindings> {
    let mut bindings = PatternBindings::new();

    match pattern {
        Pattern::Wildcard => Some(bindings),

        Pattern::Binding {
            name,
            mutable,
            subpattern,
        } => {
            if let Some(sub) = subpattern {
                let sub_bindings = match_pattern(sub, value)?;
                bindings.merge(sub_bindings);
            }
            bindings.add(name.clone(), value.clone(), *mutable);
            Some(bindings)
        }

        Pattern::Literal(lit) => {
            if value == lit {
                Some(bindings)
            } else {
                None
            }
        }

        Pattern::Tuple(patterns) => match_tuple(patterns, value, bindings),

        Pattern::Struct {
            name,
            fields,
            rest: _,
        } => match_struct(name, fields, value, bindings),

        Pattern::EnumVariant {
            enum_name,
            variant,
            payload,
        } => match_enum(enum_name, variant, payload, value, bindings),

        Pattern::Or(patterns) => {
            for p in patterns {
                if let Some(b) = match_pattern(p, value) {
                    return Some(b);
                }
            }
            None
        }

        Pattern::Range {
            start,
            end,
            inclusive,
        } => match_range(start, end, *inclusive, value, bindings),

        Pattern::Ref {
            mutability: _,
            pattern,
        } => match_pattern(pattern, value),

        Pattern::Slice(patterns) => match_slice(patterns, value, bindings),

        Pattern::Rest => Some(bindings),
    }
}

/// Match a pattern against a value with a type hint, propagating concrete
/// drop types through the pattern structure so pattern-created bindings
/// preserve generic type arguments.
pub fn match_pattern_typed(
    pattern: &Pattern,
    value: &Value,
    type_hint: Option<&RustType>,
) -> Option<PatternBindings> {
    let mut bindings = PatternBindings::new();

    match pattern {
        Pattern::Wildcard => Some(bindings),

        Pattern::Binding {
            name,
            mutable,
            subpattern,
        } => {
            if let Some(sub) = subpattern {
                let sub_bindings = match_pattern_typed(sub, value, type_hint)?;
                bindings.merge(sub_bindings);
            }
            bindings.add_typed(name.clone(), value.clone(), *mutable, type_hint.cloned());
            Some(bindings)
        }

        Pattern::Literal(lit) => {
            if value == lit {
                Some(bindings)
            } else {
                None
            }
        }

        Pattern::Tuple(patterns) => match_tuple_typed(patterns, value, bindings, type_hint),

        // For struct/enum/or/range/ref/slice, delegate to untyped matching
        // since these patterns don't introduce the same type-erasure gap.
        Pattern::Struct {
            name,
            fields,
            rest: _,
        } => match_struct(name, fields, value, bindings),

        Pattern::EnumVariant {
            enum_name,
            variant,
            payload,
        } => match_enum(enum_name, variant, payload, value, bindings),

        Pattern::Or(patterns) => {
            for p in patterns {
                if let Some(b) = match_pattern_typed(p, value, type_hint) {
                    return Some(b);
                }
            }
            None
        }

        Pattern::Range {
            start,
            end,
            inclusive,
        } => match_range(start, end, *inclusive, value, bindings),

        Pattern::Ref {
            mutability: _,
            pattern,
        } => match_pattern_typed(pattern, value, type_hint),

        Pattern::Slice(patterns) => match_slice(patterns, value, bindings),

        Pattern::Rest => Some(bindings),
    }
}

fn match_tuple(
    patterns: &[Pattern],
    value: &Value,
    mut bindings: PatternBindings,
) -> Option<PatternBindings> {
    if let Value::Tuple(values) = value {
        if patterns.len() != values.len() {
            return None;
        }
        for (p, v) in patterns.iter().zip(values.iter()) {
            let sub_bindings = match_pattern(p, v)?;
            bindings.merge(sub_bindings);
        }
        Some(bindings)
    } else {
        None
    }
}

fn match_tuple_typed(
    patterns: &[Pattern],
    value: &Value,
    mut bindings: PatternBindings,
    type_hint: Option<&RustType>,
) -> Option<PatternBindings> {
    if let Value::Tuple(values) = value {
        if patterns.len() != values.len() {
            return None;
        }
        let elem_types: Option<&Vec<RustType>> = type_hint.and_then(|ty| {
            if let RustType::Tuple(elems) = ty {
                Some(elems)
            } else {
                None
            }
        });
        for (i, (p, v)) in patterns.iter().zip(values.iter()).enumerate() {
            let elem_hint = elem_types.and_then(|elems| elems.get(i));
            let sub_bindings = match_pattern_typed(p, v, elem_hint)?;
            bindings.merge(sub_bindings);
        }
        Some(bindings)
    } else {
        None
    }
}

fn match_struct(
    name: &str,
    fields: &[(String, Pattern)],
    value: &Value,
    mut bindings: PatternBindings,
) -> Option<PatternBindings> {
    if let Value::Struct {
        name: struct_name,
        fields: struct_fields,
    } = value
    {
        if name != struct_name {
            return None;
        }
        for (field_name, field_pattern) in fields {
            let field_value = struct_fields.get(field_name)?;
            let sub_bindings = match_pattern(field_pattern, field_value)?;
            bindings.merge(sub_bindings);
        }
        Some(bindings)
    } else {
        None
    }
}

fn match_enum(
    enum_name: &str,
    variant: &str,
    payload: &crate::expr::EnumPatternPayload,
    value: &Value,
    mut bindings: PatternBindings,
) -> Option<PatternBindings> {
    if let Value::Enum {
        name,
        variant: var,
        payload: val_payload,
    } = value
    {
        if enum_name != name || variant != var {
            return None;
        }
        match (payload, val_payload.as_ref()) {
            (crate::expr::EnumPatternPayload::Unit, crate::values::EnumPayload::Unit) => {
                Some(bindings)
            }
            (
                crate::expr::EnumPatternPayload::Tuple(patterns),
                crate::values::EnumPayload::Tuple(values),
            ) => {
                if patterns.len() != values.len() {
                    return None;
                }
                for (p, v) in patterns.iter().zip(values.iter()) {
                    let sub_bindings = match_pattern(p, v)?;
                    bindings.merge(sub_bindings);
                }
                Some(bindings)
            }
            (
                crate::expr::EnumPatternPayload::Struct(patterns),
                crate::values::EnumPayload::Struct(fields),
            ) => {
                for (field_name, field_pattern) in patterns {
                    let field_value = fields.get(field_name)?;
                    let sub_bindings = match_pattern(field_pattern, field_value)?;
                    bindings.merge(sub_bindings);
                }
                Some(bindings)
            }
            _ => None,
        }
    } else {
        None
    }
}

fn in_range<T: PartialOrd>(v: &T, s: &T, e: &T, inclusive: bool) -> bool {
    if inclusive {
        v >= s && v <= e
    } else {
        v >= s && v < e
    }
}

fn match_range(
    start: &Value,
    end: &Value,
    inclusive: bool,
    value: &Value,
    bindings: PatternBindings,
) -> Option<PatternBindings> {
    let ok = match (start, end, value) {
        (
            Value::Uint { value: s, ty: ty_s },
            Value::Uint { value: e, ty: ty_e },
            Value::Uint { value: v, ty: ty_v },
        ) if ty_s == ty_e && ty_s == ty_v => in_range(v, s, e, inclusive),
        (
            Value::Int { value: s, ty: ty_s },
            Value::Int { value: e, ty: ty_e },
            Value::Int { value: v, ty: ty_v },
        ) if ty_s == ty_e && ty_s == ty_v => in_range(v, s, e, inclusive),
        (Value::Char(s), Value::Char(e), Value::Char(v)) => in_range(v, s, e, inclusive),
        _ => return None,
    };
    if ok {
        Some(bindings)
    } else {
        None
    }
}

fn match_slice(
    patterns: &[Pattern],
    value: &Value,
    mut bindings: PatternBindings,
) -> Option<PatternBindings> {
    if let Value::Array(values) = value {
        let rest_pos = patterns.iter().position(|p| matches!(p, Pattern::Rest));
        match rest_pos {
            None => {
                if patterns.len() != values.len() {
                    return None;
                }
                for (p, v) in patterns.iter().zip(values.iter()) {
                    let sub_bindings = match_pattern(p, v)?;
                    bindings.merge(sub_bindings);
                }
                Some(bindings)
            }
            Some(pos) => {
                let before = &patterns[..pos];
                let after = &patterns[pos + 1..];
                let min_len = before.len() + after.len();
                if values.len() < min_len {
                    return None;
                }
                for (p, v) in before.iter().zip(values.iter()) {
                    let sub_bindings = match_pattern(p, v)?;
                    bindings.merge(sub_bindings);
                }
                let suffix_start = values.len() - after.len();
                for (p, v) in after.iter().zip(values[suffix_start..].iter()) {
                    let sub_bindings = match_pattern(p, v)?;
                    bindings.merge(sub_bindings);
                }
                Some(bindings)
            }
        }
    } else {
        None
    }
}

#[cfg(test)]
mod tests;
