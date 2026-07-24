// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::error::RustSemError;
use crate::types::FloatType;
use crate::values::Value;

pub(crate) const FORMAT_INTRINSIC: &str = "__clean::format";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FormatStyle {
    Display,
    Debug,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum FormatFragment {
    Literal(String),
    Placeholder(FormatStyle),
}

pub(crate) fn validate_format_call(template: &str, arg_count: usize) -> Result<(), RustSemError> {
    let placeholder_count = parse_format_fragments(template)?
        .iter()
        .filter(|fragment| matches!(fragment, FormatFragment::Placeholder(_)))
        .count();
    if placeholder_count != arg_count {
        return Err(RustSemError::format(format!(
            "format string expects {placeholder_count} argument(s), got {arg_count}"
        )));
    }
    Ok(())
}

pub(crate) fn render_format_call(template: &str, args: &[Value]) -> Result<String, RustSemError> {
    let fragments = parse_format_fragments(template)?;
    let mut rendered = String::with_capacity(template.len().saturating_add(args.len() * 4));
    let mut arg_index = 0;
    for fragment in fragments {
        match fragment {
            FormatFragment::Literal(text) => rendered.push_str(&text),
            FormatFragment::Placeholder(style) => {
                let value = args.get(arg_index).ok_or_else(|| {
                    RustSemError::format("format string placeholder/argument mismatch")
                })?;
                rendered.push_str(&render_format_value(value, style)?);
                arg_index += 1;
            }
        }
    }
    if arg_index != args.len() {
        return Err(RustSemError::format(
            "format string placeholder/argument mismatch",
        ));
    }
    Ok(rendered)
}

fn parse_format_fragments(template: &str) -> Result<Vec<FormatFragment>, RustSemError> {
    let mut fragments = Vec::new();
    let mut literal = String::new();
    let bytes = template.as_bytes();
    let mut index = 0;

    while index < bytes.len() {
        match bytes[index] {
            b'{' => {
                if index + 1 >= bytes.len() {
                    return Err(RustSemError::format("unmatched `{` in format string"));
                }
                match bytes[index + 1] {
                    b'{' => {
                        literal.push('{');
                        index += 2;
                    }
                    b'}' => {
                        flush_literal(&mut fragments, &mut literal);
                        fragments.push(FormatFragment::Placeholder(FormatStyle::Display));
                        index += 2;
                    }
                    b':' if index + 3 < bytes.len()
                        && bytes[index + 2] == b'?'
                        && bytes[index + 3] == b'}' =>
                    {
                        flush_literal(&mut fragments, &mut literal);
                        fragments.push(FormatFragment::Placeholder(FormatStyle::Debug));
                        index += 4;
                    }
                    _ => {
                        return Err(RustSemError::format(format!(
                            "unsupported format placeholder starting at byte {index}"
                        )));
                    }
                }
            }
            b'}' => {
                if index + 1 < bytes.len() && bytes[index + 1] == b'}' {
                    literal.push('}');
                    index += 2;
                } else {
                    return Err(RustSemError::format("unmatched `}` in format string"));
                }
            }
            _ => {
                let ch = template[index..]
                    .chars()
                    .next()
                    .expect("index is always on a char boundary");
                literal.push(ch);
                index += ch.len_utf8();
            }
        }
    }

    flush_literal(&mut fragments, &mut literal);
    Ok(fragments)
}

fn flush_literal(fragments: &mut Vec<FormatFragment>, literal: &mut String) {
    if !literal.is_empty() {
        fragments.push(FormatFragment::Literal(std::mem::take(literal)));
    }
}

fn render_format_value(value: &Value, style: FormatStyle) -> Result<String, RustSemError> {
    let value = value.deref_view();
    match value {
        Value::Bool(flag) => Ok(match style {
            FormatStyle::Display => flag.to_string(),
            FormatStyle::Debug => format!("{flag:?}"),
        }),
        Value::Char(ch) => Ok(match style {
            FormatStyle::Display => ch.to_string(),
            FormatStyle::Debug => format!("{ch:?}"),
        }),
        Value::Str(text) => Ok(match style {
            FormatStyle::Display => text.clone(),
            FormatStyle::Debug => format!("{text:?}"),
        }),
        Value::Uint { value, .. } => Ok(match style {
            FormatStyle::Display => value.to_string(),
            FormatStyle::Debug => format!("{value:?}"),
        }),
        Value::Int { value, .. } => Ok(match style {
            FormatStyle::Display => value.to_string(),
            FormatStyle::Debug => format!("{value:?}"),
        }),
        Value::Float { bits, ty } => Ok(match ty {
            FloatType::F32 => {
                let value = f32::from_bits(u32::try_from(*bits).expect("f32 bits fit in u32"));
                match style {
                    FormatStyle::Display => format!("{value}"),
                    FormatStyle::Debug => format!("{value:?}"),
                }
            }
            FloatType::F64 => {
                let value = f64::from_bits(*bits);
                match style {
                    FormatStyle::Display => format!("{value}"),
                    FormatStyle::Debug => format!("{value:?}"),
                }
            }
        }),
        Value::Unit if style == FormatStyle::Debug => Ok("()".to_string()),
        other => Err(RustSemError::format(format!(
            "unsupported format! argument value `{other:?}`; only primitive values are supported"
        ))),
    }
}

#[cfg(test)]
mod tests {
    use super::{render_format_call, validate_format_call};
    use crate::error::RustSemError;
    use crate::memory::{Address, AllocId};
    use crate::types::{Lifetime, Mutability};
    use crate::values::Value;

    #[test]
    fn test_validate_format_call_counts_placeholders() {
        assert!(validate_format_call("{} {:?} {{}}", 2).is_ok());
    }

    #[test]
    fn test_render_format_call_formats_primitives_and_escapes_braces() {
        let rendered = render_format_call(
            "count={} debug={:?} braces={{}}",
            &[Value::u32(42), Value::Str("clean".to_string())],
        )
        .expect("render should succeed");
        assert_eq!(rendered, "count=42 debug=\"clean\" braces={}");
    }

    // ---- validate_format_call: argument-count mismatch (both directions) ----

    #[test]
    fn test_validate_format_call_too_few_args_errors() {
        // Two placeholders, one argument.
        let err = validate_format_call("{} {}", 1).expect_err("count mismatch should error");
        assert!(matches!(err, RustSemError::Format(_)));
        assert!(err.to_string().contains("expects 2 argument(s), got 1"));
    }

    #[test]
    fn test_validate_format_call_too_many_args_errors() {
        // One placeholder, two arguments.
        let err = validate_format_call("{}", 2).expect_err("count mismatch should error");
        assert!(matches!(err, RustSemError::Format(_)));
        assert!(err.to_string().contains("expects 1 argument(s), got 2"));
    }

    #[test]
    fn test_validate_format_call_escaped_braces_not_counted() {
        // `{{` and `}}` are literals, not placeholders.
        assert!(validate_format_call("{{ {} }}", 1).is_ok());
        assert!(validate_format_call("{{}}", 0).is_ok());
    }

    // ---- parse_format_fragments error paths (via render_format_call) ----

    #[test]
    fn test_render_format_call_unmatched_open_brace_errors() {
        let err = render_format_call("{", &[]).expect_err("trailing `{` should error");
        assert_eq!(
            err.to_string(),
            "format error: unmatched `{` in format string"
        );
    }

    #[test]
    fn test_render_format_call_unmatched_close_brace_errors() {
        let err = render_format_call("}", &[]).expect_err("lone `}` should error");
        assert_eq!(
            err.to_string(),
            "format error: unmatched `}` in format string"
        );
    }

    #[test]
    fn test_render_format_call_unsupported_placeholder_errors() {
        // `{:x}` style specs are not supported.
        let err = render_format_call("{:x}", &[Value::u32(1)])
            .expect_err("unsupported spec should error");
        assert!(matches!(err, RustSemError::Format(_)));
        assert!(err.to_string().contains("unsupported format placeholder"));
    }

    #[test]
    fn test_render_format_call_too_few_args_mismatch_errors() {
        // One placeholder, zero args: placeholder/argument mismatch on lookup.
        let err = render_format_call("{}", &[]).expect_err("missing arg should error");
        assert!(matches!(err, RustSemError::Format(_)));
        assert!(err.to_string().contains("placeholder/argument mismatch"));
    }

    #[test]
    fn test_render_format_call_too_many_args_mismatch_errors() {
        // Zero placeholders, one arg: leftover argument is a mismatch.
        let err =
            render_format_call("literal", &[Value::u32(1)]).expect_err("extra arg should error");
        assert!(matches!(err, RustSemError::Format(_)));
        assert!(err.to_string().contains("placeholder/argument mismatch"));
    }

    // ---- Display vs Debug for each primitive ----

    #[test]
    fn test_render_format_call_bool_display_and_debug() {
        assert_eq!(
            render_format_call("{}", &[Value::Bool(true)]).unwrap(),
            "true"
        );
        assert_eq!(
            render_format_call("{:?}", &[Value::Bool(false)]).unwrap(),
            "false"
        );
    }

    #[test]
    fn test_render_format_call_char_display_and_debug() {
        assert_eq!(render_format_call("{}", &[Value::Char('a')]).unwrap(), "a");
        // Debug quotes the char and escapes control characters.
        assert_eq!(
            render_format_call("{:?}", &[Value::Char('a')]).unwrap(),
            "'a'"
        );
        assert_eq!(
            render_format_call("{:?}", &[Value::Char('\n')]).unwrap(),
            "'\\n'"
        );
    }

    #[test]
    fn test_render_format_call_str_display_and_debug() {
        assert_eq!(
            render_format_call("{}", &[Value::Str("hi\"x".to_string())]).unwrap(),
            "hi\"x"
        );
        // Debug quotes and escapes the embedded quote.
        assert_eq!(
            render_format_call("{:?}", &[Value::Str("hi\"x".to_string())]).unwrap(),
            "\"hi\\\"x\""
        );
    }

    #[test]
    fn test_render_format_call_uint_display_and_debug() {
        assert_eq!(render_format_call("{}", &[Value::u32(42)]).unwrap(), "42");
        assert_eq!(render_format_call("{:?}", &[Value::u32(42)]).unwrap(), "42");
    }

    #[test]
    fn test_render_format_call_int_display_and_debug() {
        assert_eq!(render_format_call("{}", &[Value::i32(-7)]).unwrap(), "-7");
        assert_eq!(render_format_call("{:?}", &[Value::i32(-7)]).unwrap(), "-7");
    }

    // ---- F32 vs F64 float branches ----

    #[test]
    fn test_render_format_call_f64_display_drops_trailing_zero() {
        // Display of an integral float drops `.0`; Debug keeps it.
        assert_eq!(render_format_call("{}", &[Value::f64(1.0)]).unwrap(), "1");
        assert_eq!(
            render_format_call("{:?}", &[Value::f64(1.0)]).unwrap(),
            "1.0"
        );
        assert_eq!(
            render_format_call("{}", &[Value::f64(2.25)]).unwrap(),
            "2.25"
        );
    }

    #[test]
    fn test_render_format_call_f32_display_and_debug() {
        assert_eq!(render_format_call("{}", &[Value::f32(1.5)]).unwrap(), "1.5");
        assert_eq!(
            render_format_call("{:?}", &[Value::f32(1.5)]).unwrap(),
            "1.5"
        );
        // Round-trips through f32 precision (no widening to f64 artifacts).
        assert_eq!(render_format_call("{}", &[Value::f32(0.5)]).unwrap(), "0.5");
    }

    // ---- Value::Unit is Debug-only ----

    #[test]
    fn test_render_format_call_unit_debug_renders_parens() {
        assert_eq!(render_format_call("{:?}", &[Value::Unit]).unwrap(), "()");
    }

    #[test]
    fn test_render_format_call_unit_display_is_unsupported() {
        // Display falls through to the unsupported-value arm.
        let err =
            render_format_call("{}", &[Value::Unit]).expect_err("Display of Unit is unsupported");
        assert!(matches!(err, RustSemError::Format(_)));
        assert!(err
            .to_string()
            .contains("only primitive values are supported"));
    }

    // ---- escaped braces render as literal braces ----

    #[test]
    fn test_render_format_call_escaped_braces_render_literally() {
        assert_eq!(render_format_call("{{}}", &[]).unwrap(), "{}");
        assert_eq!(render_format_call("a{{b}}c", &[]).unwrap(), "a{b}c");
    }

    // ---- deref_view pass-through: a Reference referent is rendered ----

    #[test]
    fn test_render_format_call_reference_is_dereffed() {
        let make_ref = || Value::Reference {
            addr: Address::new(AllocId(0), 0),
            mutability: Mutability::Shared,
            lifetime: Lifetime::Static,
            referent: Some(Box::new(Value::u32(99))),
        };
        // The reference transparently formats as its referent.
        assert_eq!(render_format_call("{}", &[make_ref()]).unwrap(), "99");
        assert_eq!(render_format_call("{:?}", &[make_ref()]).unwrap(), "99");
    }
}
