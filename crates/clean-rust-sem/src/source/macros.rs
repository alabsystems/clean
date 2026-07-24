// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Macro invocation parsing for source ingestion.
//!
//! Handles both expression-position macros (`syn::Expr::Macro`) and
//! statement-position macros (`syn::Stmt::Macro`) by parsing `syn::Macro`
//! token streams and desugaring into core expression types.

#[path = "macros/asm.rs"]
mod asm;
#[path = "macros/assertions.rs"]
mod assertions;
#[path = "macros/collections.rs"]
mod collections;
#[path = "macros/compile_env.rs"]
mod compile_env;
#[path = "macros/formatting.rs"]
mod formatting;

use super::{parser::Parser, SourceError};
use crate::expr::{EnumVariantPayload, Expr};
use crate::values::{BinOp, Value};

impl Parser {
    /// Parse a macro invocation shared by both expression and statement positions.
    pub(super) fn parse_macro_invocation(&mut self, mac: &syn::Macro) -> Result<Expr, SourceError> {
        let path_name = Self::path_to_string(&mac.path);
        let dispatch_name =
            Self::builtin_macro_dispatch_name(&mac.path).unwrap_or_else(|| path_name.clone());
        match dispatch_name.as_str() {
            "asm" => self.parse_inline_asm_macro(&mac.tokens),
            "panic" | "unreachable" | "todo" | "unimplemented" => Ok(Expr::Panic {
                message: Box::new(Expr::Literal(Value::Unit)),
            }),
            // debug_assert family: identical to assert in the semantic model
            // (we do not model build profiles / cfg(debug_assertions))
            "debug_assert" => self.parse_assert_macro(&mac.tokens),
            "debug_assert_eq" => self.parse_assert_cmp_macro(&mac.tokens, BinOp::Ne),
            "debug_assert_ne" => self.parse_assert_cmp_macro(&mac.tokens, BinOp::Eq),
            "println" | "eprintln" | "print" | "eprint" | "write" | "writeln"
            // Logging crate macros (log, tracing, etc.) are no-ops
            | "trace" | "debug" | "info" | "warn" | "error" | "log" => {
                // I/O and logging macros are no-ops in the semantic model
                Ok(Expr::Literal(Value::Unit))
            }
            "vec" => self.parse_vec_macro(&mac.tokens),
            "assert" => self.parse_assert_macro(&mac.tokens),
            "assert_eq" => self.parse_assert_cmp_macro(&mac.tokens, BinOp::Ne),
            "assert_ne" => self.parse_assert_cmp_macro(&mac.tokens, BinOp::Eq),
            "dbg" => self.parse_dbg_macro(&mac.tokens),
            "matches" => self.parse_matches_macro(&mac.tokens),
            "format" | "format_args" => self.parse_format_macro(&mac.tokens),
            "cfg" => {
                // cfg! evaluates compile-time configuration predicates.
                // Without access to the actual build config, default to false.
                Ok(Expr::Literal(Value::Bool(false)))
            }
            "env" => {
                // env!("VAR") returns the value of an environment variable at compile time.
                // Without access to the build environment, preserve the string type but
                // return an empty placeholder after validating the supported macro forms.
                Self::validate_env_macro_args(&mac.tokens)?;
                Ok(Expr::Literal(Value::Str(String::new())))
            }
            "option_env" => {
                // option_env!("VAR") returns Option<&'static str>. Without access to the
                // build environment, preserve the macro's Option shape and return None.
                Self::validate_single_string_literal_macro_arg(&mac.tokens, "option_env")?;
                Ok(Expr::EnumVariant {
                    enum_name: "Option".to_string(),
                    variant: "None".to_string(),
                    payload: EnumVariantPayload::Unit,
                    type_args: vec![],
                    const_args: vec![],
                })
            }
            "stringify" => {
                // stringify! converts its argument tokens to a string literal.
                Ok(Expr::Literal(Value::Str(mac.tokens.to_string())))
            }
            "concat" => self.parse_concat_macro(&mac.tokens),
            "include_str" => {
                // File inclusion macro. Preserve the string placeholder shape after
                // validating the compile-time file path argument.
                Self::validate_single_string_literal_macro_arg(&mac.tokens, "include_str")?;
                Ok(Expr::Literal(Value::Str(String::new())))
            }
            "include_bytes" => {
                // File inclusion macro. Preserve the byte-array placeholder shape instead
                // of lowering to a string.
                Self::validate_single_string_literal_macro_arg(&mac.tokens, "include_bytes")?;
                Ok(Expr::Literal(Value::Array(Vec::new())))
            }
            "compile_error" => {
                // compile_error! causes a compilation failure. Model as panic.
                Ok(Expr::Panic {
                    message: Box::new(Expr::Literal(Value::Unit)),
                })
            }
            "column" | "line" => {
                // Source location macros. Return 0 as placeholder.
                Self::validate_zero_arg_macro(&mac.tokens, dispatch_name.as_str())?;
                Ok(Expr::Literal(Value::u32(0)))
            }
            "file" | "module_path" => {
                // Source location string macros.
                Self::validate_zero_arg_macro(&mac.tokens, dispatch_name.as_str())?;
                Ok(Expr::Literal(Value::Str(String::new())))
            }
            _ => Err(Self::unsupported(
                "macro",
                format!("unsupported macro `{path_name}!`"),
            )),
        }
    }

    pub(super) fn builtin_item_macro_dispatch_name(path: &syn::Path) -> Option<String> {
        match path.segments.len() {
            1 => {
                let name = path.segments.first()?.ident.to_string();
                matches!(name.as_str(), "global_asm").then_some(name)
            }
            3 => {
                let mut segments = path.segments.iter();
                let prefix = segments.next()?.ident.to_string();
                let arch = segments.next()?.ident.to_string();
                let name = segments.next()?.ident.to_string();
                match (prefix.as_str(), arch.as_str(), name.as_str()) {
                    ("std", "arch", "global_asm") | ("core", "arch", "global_asm") => Some(name),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    // Keep qualified dispatch aligned with Rust's actual crate exports so
    // unsupported paths still fail closed instead of normalizing blindly.
    pub(super) fn builtin_macro_dispatch_name(path: &syn::Path) -> Option<String> {
        match path.segments.len() {
            1 => {
                let name = path.segments.first()?.ident.to_string();
                Self::is_supported_macro_name(&name).then_some(name)
            }
            2 => {
                let mut segments = path.segments.iter();
                let prefix = segments.next()?.ident.to_string();
                let name = segments.next()?.ident.to_string();
                match prefix.as_str() {
                    "std" if Self::is_supported_macro_name(&name) => Some(name),
                    "core" if Self::is_core_supported_macro_name(&name) => Some(name),
                    "alloc" if Self::is_alloc_supported_macro_name(&name) => Some(name),
                    "log" | "tracing" if Self::is_logging_macro_name(&name) => Some(name),
                    _ => None,
                }
            }
            3 => {
                let mut segments = path.segments.iter();
                let prefix = segments.next()?.ident.to_string();
                let arch = segments.next()?.ident.to_string();
                let name = segments.next()?.ident.to_string();
                match (prefix.as_str(), arch.as_str(), name.as_str()) {
                    ("std", "arch", _) | ("core", "arch", _) if Self::is_arch_macro_name(&name) => {
                        Some(name)
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn is_supported_macro_name(name: &str) -> bool {
        matches!(
            name,
            "panic"
                | "unreachable"
                | "todo"
                | "unimplemented"
                | "debug_assert"
                | "debug_assert_eq"
                | "debug_assert_ne"
                | "println"
                | "eprintln"
                | "print"
                | "eprint"
                | "write"
                | "writeln"
                | "vec"
                | "assert"
                | "assert_eq"
                | "assert_ne"
                | "dbg"
                | "matches"
                | "format"
                | "format_args"
                | "cfg"
                | "env"
                | "option_env"
                | "stringify"
                | "concat"
                | "include_str"
                | "include_bytes"
                | "compile_error"
                | "column"
                | "line"
                | "file"
                | "module_path"
                | "asm"
                | "trace"
                | "debug"
                | "info"
                | "warn"
                | "error"
                | "log"
        )
    }

    fn is_core_supported_macro_name(name: &str) -> bool {
        matches!(
            name,
            "panic"
                | "unreachable"
                | "todo"
                | "unimplemented"
                | "debug_assert"
                | "debug_assert_eq"
                | "debug_assert_ne"
                | "write"
                | "writeln"
                | "assert"
                | "assert_eq"
                | "assert_ne"
                | "matches"
                | "format_args"
                | "cfg"
                | "env"
                | "option_env"
                | "stringify"
                | "concat"
                | "include_str"
                | "include_bytes"
                | "compile_error"
                | "column"
                | "line"
                | "file"
                | "module_path"
                | "asm"
        )
    }

    fn is_alloc_supported_macro_name(name: &str) -> bool {
        matches!(name, "vec" | "format")
    }

    fn is_logging_macro_name(name: &str) -> bool {
        matches!(name, "trace" | "debug" | "info" | "warn" | "error" | "log")
    }

    fn is_arch_macro_name(name: &str) -> bool {
        matches!(name, "asm")
    }
}
