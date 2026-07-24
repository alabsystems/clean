// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pretty printer for L5IR (Low-Level Intermediate Representation).
//!
//! Produces human-readable textual output for IR declarations and bodies,
//! useful for debugging compiler passes and inspecting generated IR.
//!
//! Part of #3084 - IO/FFI/Native.

use crate::ir::{
    CtorInfo, FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, JoinPointId, VarId,
};

/// Configuration for IR pretty printing.
pub(crate) struct PrettyConfig {
    pub indent_size: usize,
    pub show_types: bool,
    pub show_var_ids: bool,
    pub use_unicode: bool,
    pub show_metadata: bool,
}

impl Default for PrettyConfig {
    fn default() -> Self {
        Self {
            indent_size: 2,
            show_types: true,
            show_var_ids: false,
            use_unicode: true,
            show_metadata: false,
        }
    }
}

impl PrettyConfig {
    /// Compact config: no types, no metadata, minimal output.
    pub(crate) fn compact() -> Self {
        Self {
            show_types: false,
            ..Self::default()
        }
    }

    /// Verbose config: show everything.
    pub(crate) fn verbose() -> Self {
        Self {
            show_var_ids: true,
            show_metadata: true,
            ..Self::default()
        }
    }
}

/// Pretty printer state for IR nodes.
pub(crate) struct IrPrinter {
    config: PrettyConfig,
    output: String,
    indent_level: usize,
}

impl IrPrinter {
    pub(crate) fn new(config: PrettyConfig) -> Self {
        Self {
            config,
            output: String::with_capacity(1024),
            indent_level: 0,
        }
    }

    fn indent(&mut self) {
        self.indent_level += 1;
    }
    fn dedent(&mut self) {
        self.indent_level = self.indent_level.saturating_sub(1);
    }

    fn newline(&mut self) {
        self.output.push('\n');
        for _ in 0..self.indent_level * self.config.indent_size {
            self.output.push(' ');
        }
    }

    fn emit(&mut self, s: &str) {
        self.output.push_str(s);
    }

    pub(crate) fn into_string(self) -> String {
        self.output
    }

    // --- Type printing ---

    pub(crate) fn format_type(&self, ty: &IRType) -> String {
        match ty {
            IRType::Bool => "Bool".into(),
            IRType::UInt8 => "UInt8".into(),
            IRType::UInt16 => "UInt16".into(),
            IRType::UInt32 => "UInt32".into(),
            IRType::UInt64 => "UInt64".into(),
            IRType::USize => "USize".into(),
            IRType::Float32 => "Float32".into(),
            IRType::Float64 => "Float64".into(),
            IRType::Object => "Object".into(),
            IRType::TObject => "TObject".into(),
            IRType::Struct(fs) => {
                let inner: Vec<String> = fs.iter().map(|f| self.format_type(f)).collect();
                format!("Struct({})", inner.join(", "))
            }
            IRType::Union(vs) => {
                let inner: Vec<String> = vs.iter().map(|v| self.format_type(v)).collect();
                format!("Union({})", inner.join(", "))
            }
            IRType::Erased => "\u{25C7}".into(),
            IRType::Void => "Void".into(),
        }
    }

    // --- Identifier formatting ---

    fn format_var(&self, var: &VarId) -> String {
        if self.config.show_var_ids {
            format!("x_{}", var.0)
        } else {
            format!("x{}", var.0)
        }
    }

    fn format_jp(&self, jp: &JoinPointId) -> String {
        format!("jp{}", jp.0)
    }
    fn format_fn_id(&self, fn_id: &FnId) -> String {
        fn_id.0.to_string()
    }

    fn format_arg(&self, arg: &IRArg) -> String {
        match arg {
            IRArg::Var(v) => self.format_var(v),
            IRArg::Erased => "\u{25C7}".into(),
        }
    }

    fn format_args(&self, args: &[IRArg]) -> String {
        args.iter()
            .map(|a| self.format_arg(a))
            .collect::<Vec<_>>()
            .join(" ")
    }

    fn emit_type_annotation(&mut self, ty: &IRType) {
        if self.config.show_types {
            let ty_str = self.format_type(ty);
            self.emit(" : ");
            self.emit(&ty_str);
        }
    }

    fn emit_ctor_info(&mut self, info: &CtorInfo) {
        self.emit(&info.name.to_string());
        if self.config.show_metadata {
            self.emit(&format!(
                " [tag={}, scalars={}, objects={}]",
                info.tag, info.num_scalars, info.num_objects
            ));
        }
    }

    fn format_params(&self, params: &[(VarId, IRType)]) -> String {
        params
            .iter()
            .map(|(v, ty)| {
                let v_str = self.format_var(v);
                if self.config.show_types {
                    format!("{} : {}", v_str, self.format_type(ty))
                } else {
                    v_str
                }
            })
            .collect::<Vec<_>>()
            .join(", ")
    }

    // --- Expression printing ---

    pub(crate) fn format_expr(&self, expr: &IRExpr) -> String {
        match expr {
            IRExpr::Ctor { info, args } if args.is_empty() => format!("ctor {}", info.name),
            IRExpr::Ctor { info, args } => format!("ctor {} {}", info.name, self.format_args(args)),
            IRExpr::Proj { idx, ty, arg } if self.config.show_types => {
                format!(
                    "proj[{}] {} : {}",
                    idx,
                    self.format_arg(arg),
                    self.format_type(ty)
                )
            }
            IRExpr::Proj { idx, arg, .. } => format!("proj[{}] {}", idx, self.format_arg(arg)),
            IRExpr::Tag(arg) => format!("tag {}", self.format_arg(arg)),
            IRExpr::Box { ty, arg } => {
                format!("box[{}] {}", self.format_type(ty), self.format_arg(arg))
            }
            IRExpr::Unbox { ty, arg } => {
                format!("unbox[{}] {}", self.format_type(ty), self.format_arg(arg))
            }
            IRExpr::Lit(lit) => self.format_literal(lit),
            IRExpr::Apply { fn_id, args } if args.is_empty() => {
                format!("{} ()", self.format_fn_id(fn_id))
            }
            IRExpr::Apply { fn_id, args } => {
                format!("{} {}", self.format_fn_id(fn_id), self.format_args(args))
            }
            IRExpr::PartialApply { fn_id, arity, args } if self.config.show_metadata => {
                format!(
                    "papp[arity={}] {} {}",
                    arity,
                    self.format_fn_id(fn_id),
                    self.format_args(args)
                )
            }
            IRExpr::PartialApply { fn_id, args, .. } => {
                format!(
                    "papp {} {}",
                    self.format_fn_id(fn_id),
                    self.format_args(args)
                )
            }
            IRExpr::ClosureApply { closure, args } => {
                format!("ap {} {}", self.format_arg(closure), self.format_args(args))
            }
            IRExpr::UProj { idx, var } => format!("uproj[{}] {}", idx, self.format_var(var)),
            IRExpr::SProj { n, offset, var, ty } if self.config.show_types => {
                format!(
                    "sproj[{}, {}] {} : {}",
                    n,
                    offset,
                    self.format_var(var),
                    self.format_type(ty)
                )
            }
            IRExpr::SProj { n, offset, var, .. } => {
                format!("sproj[{}, {}] {}", n, offset, self.format_var(var))
            }
            IRExpr::IsShared(var) => format!("isShared {}", self.format_var(var)),
            IRExpr::String(s) => format!("{:?}", s),
            IRExpr::Reset(var) => format!("reset {}", self.format_var(var)),
            IRExpr::Reuse { var, ctor, args } if args.is_empty() => {
                format!("reuse {} in ctor {}", self.format_var(var), ctor.name)
            }
            IRExpr::Reuse { var, ctor, args } => {
                format!(
                    "reuse {} in ctor {} {}",
                    self.format_var(var),
                    ctor.name,
                    self.format_args(args)
                )
            }
        }
    }

    fn format_literal(&self, lit: &IRLiteral) -> String {
        match lit {
            IRLiteral::Bool(b) => b.to_string(),
            IRLiteral::UInt8(n) => format!("{}u8", n),
            IRLiteral::UInt16(n) => format!("{}u16", n),
            IRLiteral::UInt32(n) => format!("{}u32", n),
            IRLiteral::UInt64(n) => format!("{}u64", n),
            IRLiteral::USize(n) => format!("{}usize", n),
            IRLiteral::NatBig(n) => format!("{}nat", n),
            IRLiteral::Float32(f) => format!("{:.1}f32", f),
            IRLiteral::Float64(f) => format!("{:.1}f64", f),
        }
    }

    // --- Body (control flow) printing ---

    /// Print an IR body. Each statement is on its own line at the current indent.
    pub(crate) fn print_body(&mut self, body: &IRBody) {
        match body {
            IRBody::VDecl {
                var,
                ty,
                value,
                rest,
            } => {
                self.print_vdecl(var, ty, value);
                self.newline();
                self.print_body(rest);
            }
            IRBody::JDecl {
                jp,
                params,
                body: jp_body,
                rest,
            } => {
                self.print_jdecl(jp, params, jp_body);
                self.newline();
                self.print_body(rest);
            }
            IRBody::Inc { var, n, rest } => {
                self.print_inc(var, *n);
                self.newline();
                self.print_body(rest);
            }
            IRBody::Dec { var, rest } => {
                self.emit("dec ");
                self.emit(&self.format_var(var));
                self.newline();
                self.print_body(rest);
            }
            IRBody::Set {
                var,
                idx,
                value,
                rest,
            } => {
                self.emit(&format!(
                    "{}[{}] := {}",
                    self.format_var(var),
                    idx,
                    self.format_var(value)
                ));
                self.newline();
                self.print_body(rest);
            }
            IRBody::SetTag { var, tag, rest } => {
                self.emit(&format!("setTag {} {}", self.format_var(var), tag));
                self.newline();
                self.print_body(rest);
            }
            IRBody::USet {
                var,
                idx,
                value,
                rest,
            } => {
                self.emit(&format!(
                    "uset {}[{}] := {}",
                    self.format_var(var),
                    idx,
                    self.format_var(value)
                ));
                self.newline();
                self.print_body(rest);
            }
            IRBody::SSet {
                var,
                n,
                offset,
                value,
                ty,
                rest,
            } => {
                self.print_sset(var, *n, *offset, value, ty);
                self.newline();
                self.print_body(rest);
            }
            IRBody::Case {
                scrutinee,
                alts,
                default,
            } => self.print_case(scrutinee, alts, default),
            IRBody::Jmp { jp, args } => self.print_jmp(jp, args),
            IRBody::Ret(arg) => {
                self.emit("ret ");
                self.emit(&self.format_arg(arg));
            }
            IRBody::Unreachable => self.emit("unreachable"),
        }
    }

    fn print_vdecl(&mut self, var: &VarId, ty: &IRType, value: &IRExpr) {
        let var_str = self.format_var(var);
        let val_str = self.format_expr(value);
        self.emit("let ");
        self.emit(&var_str);
        self.emit_type_annotation(ty);
        self.emit(" := ");
        self.emit(&val_str);
    }

    fn print_jdecl(&mut self, jp: &JoinPointId, params: &[(VarId, IRType)], jp_body: &IRBody) {
        let jp_str = self.format_jp(jp);
        self.emit("jp ");
        self.emit(&jp_str);
        if !params.is_empty() {
            self.emit(" (");
            self.emit(&self.format_params(params));
            self.emit(")");
        }
        self.emit(" :=");
        self.indent();
        self.newline();
        self.print_body(jp_body);
        self.dedent();
    }

    fn print_inc(&mut self, var: &VarId, n: u32) {
        let var_str = self.format_var(var);
        if n == 1 {
            self.emit("inc ");
            self.emit(&var_str);
        } else {
            self.emit(&format!("inc {} {}", var_str, n));
        }
    }

    fn print_sset(&mut self, var: &VarId, n: u32, offset: u32, value: &VarId, ty: &IRType) {
        let var_s = self.format_var(var);
        let val_s = self.format_var(value);
        if self.config.show_types {
            self.emit(&format!(
                "sset {}[{}, {}] := {} : {}",
                var_s,
                n,
                offset,
                val_s,
                self.format_type(ty)
            ));
        } else {
            self.emit(&format!("sset {}[{}, {}] := {}", var_s, n, offset, val_s));
        }
    }

    fn print_case(&mut self, scrutinee: &VarId, alts: &[IRAlt], default: &Option<Box<IRBody>>) {
        self.emit("case ");
        self.emit(&self.format_var(scrutinee));
        self.emit(" of");
        self.indent();
        for alt in alts {
            self.newline();
            self.print_alt(alt);
        }
        if let Some(def) = default {
            self.newline();
            self.emit("| _ =>");
            self.indent();
            self.newline();
            self.print_body(def);
            self.dedent();
        }
        self.dedent();
    }

    fn print_jmp(&mut self, jp: &JoinPointId, args: &[IRArg]) {
        self.emit("goto ");
        self.emit(&self.format_jp(jp));
        if !args.is_empty() {
            self.emit(" ");
            self.emit(&self.format_args(args));
        }
    }

    fn print_alt(&mut self, alt: &IRAlt) {
        self.emit("| ");
        self.emit_ctor_info(&alt.ctor);
        self.emit(" =>");
        self.indent();
        self.newline();
        self.print_body(&alt.body);
        self.dedent();
    }

    // --- Declaration printing ---

    pub(crate) fn print_decl(&mut self, decl: &IRDecl) {
        self.emit("def ");
        self.emit(&decl.name.to_string());
        if !decl.params.is_empty() {
            self.emit(" (");
            self.emit(&self.format_params(&decl.params));
            self.emit(")");
        }
        if self.config.show_types {
            let ret = self.format_type(&decl.return_type);
            let arrow = if self.config.use_unicode {
                " \u{2192} "
            } else {
                " -> "
            };
            self.emit(arrow);
            self.emit(&ret);
        }
        self.emit(" :=");
        self.indent();
        self.newline();
        self.print_body(&decl.body);
        self.dedent();
    }
}

// --- Convenience functions ---

/// Pretty print an IR body with default configuration.
#[must_use]
pub(crate) fn pretty_print_body(body: &IRBody) -> String {
    let mut printer = IrPrinter::new(PrettyConfig::default());
    printer.print_body(body);
    printer.into_string()
}

/// Pretty print an IR declaration with default configuration.
#[must_use]
pub(crate) fn pretty_print_decl(decl: &IRDecl) -> String {
    let mut printer = IrPrinter::new(PrettyConfig::default());
    printer.print_decl(decl);
    printer.into_string()
}
