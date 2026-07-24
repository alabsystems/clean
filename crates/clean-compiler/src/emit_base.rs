// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared emitter infrastructure for code generation backends.
//!
//! `EmitterBase` encapsulates the output buffering, indentation management,
//! and common IR-to-string conversions that are identical across the C and
//! Rust backends. Each backend wraps an `EmitterBase` and adds only the
//! language-specific emission logic.
//!
//! Part of #1922 - Extract shared EmitterBase.

use crate::ir::{FnId, IRArg, VarId};
use crate::mangle::mangle_name;
use clean_kernel::Name;

/// Shared emitter state for output buffering and indentation.
///
/// Both `CEmitter` and `RustEmitter` embed this struct and delegate
/// common operations to it.
pub(crate) struct EmitterBase {
    /// Accumulated output text.
    output: String,
    /// Current indentation depth (number of indent units).
    indent_level: usize,
    /// Indent string per level (e.g., "  " or "    ").
    indent_str: String,
}

impl EmitterBase {
    /// Create a new emitter base with the given indent string.
    pub(crate) fn new(indent_str: String) -> Self {
        Self {
            output: String::new(),
            indent_level: 0,
            indent_str,
        }
    }

    /// Consume the emitter and return the accumulated output.
    pub(crate) fn finish(self) -> String {
        self.output
    }

    /// Write a line with current indentation.
    pub(crate) fn writeln(&mut self, s: &str) {
        for _ in 0..self.indent_level {
            self.output.push_str(&self.indent_str);
        }
        self.output.push_str(s);
        self.output.push('\n');
    }

    /// Increase indentation by one level.
    pub(crate) fn indent(&mut self) {
        self.indent_level += 1;
    }

    /// Decrease indentation by one level.
    pub(crate) fn dedent(&mut self) {
        self.indent_level = self.indent_level.saturating_sub(1);
    }

    /// Emit a variable reference: `_xN`.
    pub(crate) fn emit_var(&self, var: VarId) -> String {
        format!("_x{}", var.0)
    }

    /// Emit a mangled function name from a `FnId`.
    pub(crate) fn emit_fn_id(&self, fn_id: &FnId) -> String {
        mangle_name(&fn_id.0)
    }

    /// Emit a mangled name from a `Name`.
    pub(crate) fn emit_name(&self, name: &Name) -> String {
        mangle_name(name)
    }

    /// Emit an IR argument (variable or erased unit).
    pub(crate) fn emit_arg(&self, arg: &IRArg) -> String {
        match arg {
            IRArg::Var(v) => self.emit_var(*v),
            IRArg::Erased => "clean_box(0)".to_string(),
        }
    }

    /// Emit a comma-separated list of IR arguments.
    pub(crate) fn emit_args_joined(&self, args: &[IRArg]) -> String {
        args.iter()
            .map(|a| self.emit_arg(a))
            .collect::<Vec<_>>()
            .join(", ")
    }
}
