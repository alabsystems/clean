// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//! Extended IR pretty-printing: configurable format (compact/verbose/debug),
//! ANSI highlighting, type annotations, DOT CFG, RC annotations, indentation
//! control, declaration summaries, IR diff, stats tables, and HTML output.
//! Part of #3083 - Extensibility.

use crate::ir::{CtorInfo, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, VarId};
use crate::ir_pretty_ext::{ir_body_depth, ir_body_node_count, ir_rc_ops_count};
use std::fmt::Write as FmtWrite;

/// Output format mode.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum OutputFormat {
    Compact,
    Verbose,
    Debug,
}

const ANSI_RESET: &str = "\x1b[0m";
const ANSI_KW: &str = "\x1b[1;34m";
const ANSI_TYPE: &str = "\x1b[32m";
const ANSI_RC: &str = "\x1b[1;31m";
const ANSI_LIT: &str = "\x1b[36m";
const ANSI_CTOR: &str = "\x1b[33m";
const ANSI_VAR: &str = "\x1b[35m";

/// Extended pretty-printer configuration.
#[derive(Clone, Debug)]
pub(crate) struct Ext2Config {
    pub(crate) format: OutputFormat,
    pub(crate) ansi_color: bool,
    pub(crate) show_types: bool,
    pub(crate) show_rc_annotations: bool,
    pub(crate) indent_width: usize,
    pub(crate) max_depth: Option<usize>,
    pub(crate) html_mode: bool,
}

impl Default for Ext2Config {
    fn default() -> Self {
        Self {
            format: OutputFormat::Verbose,
            ansi_color: false,
            show_types: true,
            show_rc_annotations: false,
            indent_width: 2,
            max_depth: None,
            html_mode: false,
        }
    }
}

impl Ext2Config {
    pub(crate) fn compact() -> Self {
        Self {
            format: OutputFormat::Compact,
            show_types: false,
            ..Self::default()
        }
    }
    pub(crate) fn debug() -> Self {
        Self {
            format: OutputFormat::Debug,
            show_rc_annotations: true,
            ..Self::default()
        }
    }
}

pub(crate) struct Ext2Printer {
    cfg: Ext2Config,
    buf: String,
    depth: usize,
    body_depth: usize,
}

impl Ext2Printer {
    pub(crate) fn new(cfg: Ext2Config) -> Self {
        Self {
            cfg,
            buf: String::with_capacity(2048),
            depth: 0,
            body_depth: 0,
        }
    }
    pub(crate) fn into_string(self) -> String {
        self.buf
    }

    fn styled(&self, ansi: &str, cls: &str, text: &str) -> String {
        if self.cfg.html_mode {
            format!("<span class=\"ir-{cls}\">{}</span>", html_escape(text))
        } else if self.cfg.ansi_color {
            format!("{ansi}{text}{ANSI_RESET}")
        } else {
            text.to_owned()
        }
    }
    fn kw(&self, s: &str) -> String {
        self.styled(ANSI_KW, "kw", s)
    }
    fn ty_s(&self, s: &str) -> String {
        self.styled(ANSI_TYPE, "type", s)
    }
    fn rc_s(&self, s: &str) -> String {
        self.styled(ANSI_RC, "rc", s)
    }
    fn lit_s(&self, s: &str) -> String {
        self.styled(ANSI_LIT, "lit", s)
    }
    fn ctor_s(&self, s: &str) -> String {
        self.styled(ANSI_CTOR, "ctor", s)
    }
    fn var_s(&self, s: &str) -> String {
        self.styled(ANSI_VAR, "var", s)
    }

    fn indent(&mut self) {
        self.depth += 1;
    }
    fn dedent(&mut self) {
        self.depth = self.depth.saturating_sub(1);
    }
    fn newline(&mut self) {
        self.buf.push('\n');
        for _ in 0..self.depth * self.cfg.indent_width {
            self.buf.push(' ');
        }
    }
    fn emit(&mut self, s: &str) {
        self.buf.push_str(s);
    }
    fn at_max_depth(&self) -> bool {
        self.cfg.max_depth.is_some_and(|m| self.body_depth >= m)
    }
    fn print_child_body(&mut self, body: &IRBody) {
        self.body_depth += 1;
        self.print_body(body);
        self.body_depth = self.body_depth.saturating_sub(1);
    }

    pub(crate) fn format_type(&self, ty: &IRType) -> String {
        let raw = match ty {
            IRType::Bool => "Bool",
            IRType::UInt8 => "UInt8",
            IRType::UInt16 => "UInt16",
            IRType::UInt32 => "UInt32",
            IRType::UInt64 => "UInt64",
            IRType::USize => "USize",
            IRType::Float32 => "Float32",
            IRType::Float64 => "Float64",
            IRType::Object => "Object",
            IRType::TObject => "TObject",
            IRType::Erased => "Erased",
            IRType::Void => "Void",
            IRType::Struct(fs) => {
                return self.ty_s(&format!(
                    "Struct({})",
                    fs.iter()
                        .map(|f| self.format_type(f))
                        .collect::<Vec<_>>()
                        .join(", ")
                ))
            }
            IRType::Union(vs) => {
                return self.ty_s(&format!(
                    "Union({})",
                    vs.iter()
                        .map(|v| self.format_type(v))
                        .collect::<Vec<_>>()
                        .join(", ")
                ))
            }
        };
        self.ty_s(raw)
    }
    fn format_var(&self, v: VarId) -> String {
        let s = if self.cfg.format == OutputFormat::Debug {
            format!("x_{}", v.0)
        } else {
            format!("x{}", v.0)
        };
        self.var_s(&s)
    }
    fn format_arg(&self, a: &IRArg) -> String {
        match a {
            IRArg::Var(v) => self.format_var(*v),
            IRArg::Erased => self.kw("erased"),
        }
    }
    fn format_args(&self, args: &[IRArg]) -> String {
        args.iter()
            .map(|a| self.format_arg(a))
            .collect::<Vec<_>>()
            .join(", ")
    }
    fn format_ctor(&self, info: &CtorInfo) -> String {
        let name = self.ctor_s(&info.name.to_string());
        if self.cfg.format == OutputFormat::Debug {
            format!(
                "{name}[tag={}, s={}, o={}]",
                info.tag, info.num_scalars, info.num_objects
            )
        } else {
            name
        }
    }
    fn format_literal(&self, lit: &IRLiteral) -> String {
        self.lit_s(&match lit {
            IRLiteral::Bool(b) => b.to_string(),
            IRLiteral::UInt8(n) => format!("{n}u8"),
            IRLiteral::UInt16(n) => format!("{n}u16"),
            IRLiteral::UInt32(n) => format!("{n}u32"),
            IRLiteral::UInt64(n) => format!("{n}u64"),
            IRLiteral::USize(n) => format!("{n}usize"),
            IRLiteral::NatBig(n) => format!("{n}nat"),
            IRLiteral::Float32(f) => format!("{f:.1}f32"),
            IRLiteral::Float64(f) => format!("{f:.1}f64"),
        })
    }
    fn format_params(&self, params: &[(VarId, IRType)]) -> String {
        params
            .iter()
            .map(|(v, ty)| {
                let vs = self.format_var(*v);
                if self.cfg.show_types {
                    format!("{vs}: {}", self.format_type(ty))
                } else {
                    vs
                }
            })
            .collect::<Vec<_>>()
            .join(", ")
    }
    fn call_fmt(&self, head: String, args: &[IRArg]) -> String {
        if args.is_empty() {
            head
        } else {
            format!("{head}({})", self.format_args(args))
        }
    }
    fn type_ann(&self, ty: &IRType) -> String {
        if self.cfg.show_types {
            format!(": {}", self.format_type(ty))
        } else {
            String::new()
        }
    }

    fn format_expr(&self, expr: &IRExpr) -> String {
        match expr {
            IRExpr::Ctor { info, args } => self.call_fmt(
                format!("{} {}", self.kw("ctor"), self.format_ctor(info)),
                args,
            ),
            IRExpr::Proj { idx, ty, arg } => format!(
                "{}[{}]({}){}",
                self.kw("proj"),
                idx,
                self.format_arg(arg),
                self.type_ann(ty)
            ),
            IRExpr::Tag(a) => format!("{}({})", self.kw("tag"), self.format_arg(a)),
            IRExpr::Box { ty, arg } => format!(
                "{}[{}]({})",
                self.kw("box"),
                self.format_type(ty),
                self.format_arg(arg)
            ),
            IRExpr::Unbox { ty, arg } => format!(
                "{}[{}]({})",
                self.kw("unbox"),
                self.format_type(ty),
                self.format_arg(arg)
            ),
            IRExpr::Lit(l) => self.format_literal(l),
            IRExpr::Apply { fn_id, args } => {
                self.call_fmt(format!("{} {}", self.kw("apply"), fn_id.0), args)
            }
            IRExpr::PartialApply { fn_id, arity, args } => {
                self.call_fmt(format!("{} {}/{arity}", self.kw("papp"), fn_id.0), args)
            }
            IRExpr::ClosureApply { closure, args } => self.call_fmt(
                format!("{} {}", self.kw("ap"), self.format_arg(closure)),
                args,
            ),
            IRExpr::UProj { idx, var } => {
                format!("{}[{}]({})", self.kw("uproj"), idx, self.format_var(*var))
            }
            IRExpr::SProj { n, offset, var, ty } => format!(
                "{}[{}+{}]({}){}",
                self.kw("sproj"),
                n,
                offset,
                self.format_var(*var),
                self.type_ann(ty)
            ),
            IRExpr::IsShared(v) => format!("{}({})", self.kw("isShared"), self.format_var(*v)),
            IRExpr::String(s) => self.lit_s(&format!("{s:?}")),
            IRExpr::Reset(v) => format!("{}({})", self.kw("reset"), self.format_var(*v)),
            IRExpr::Reuse { var, ctor, args } => self.call_fmt(
                format!(
                    "{} {} as {}",
                    self.kw("reuse"),
                    self.format_var(*var),
                    self.format_ctor(ctor)
                ),
                args,
            ),
        }
    }

    pub(crate) fn print_body(&mut self, body: &IRBody) {
        if self.at_max_depth() {
            self.emit(&self.kw("..."));
            return;
        }
        match body {
            IRBody::VDecl {
                var,
                ty,
                value,
                rest,
            } => {
                let s = format!(
                    "{} {}{} = {}",
                    self.kw("let"),
                    self.format_var(*var),
                    self.type_ann(ty),
                    self.format_expr(value)
                );
                self.emit(&s);
                self.newline();
                self.print_child_body(rest);
            }
            IRBody::JDecl {
                jp,
                params,
                body: jb,
                rest,
            } => {
                self.emit(&format!(
                    "{} jp{}({}) {{",
                    self.kw("jp"),
                    jp.0,
                    self.format_params(params)
                ));
                self.indent();
                self.newline();
                self.print_child_body(jb);
                self.dedent();
                self.newline();
                self.emit("}");
                self.newline();
                self.print_child_body(rest);
            }
            IRBody::Inc { var, n, rest } => {
                self.emit_rc("inc", *var, Some(*n));
                self.newline();
                self.print_child_body(rest);
            }
            IRBody::Dec { var, rest } => {
                self.emit_rc("dec", *var, None);
                self.newline();
                self.print_child_body(rest);
            }
            IRBody::Set {
                var,
                idx,
                value,
                rest,
            } => {
                self.emit(&format!(
                    "{} {}[{idx}] = {}",
                    self.kw("set"),
                    self.format_var(*var),
                    self.format_var(*value)
                ));
                self.newline();
                self.print_child_body(rest);
            }
            IRBody::SetTag { var, tag, rest } => {
                self.emit(&format!(
                    "{} {} {tag}",
                    self.kw("setTag"),
                    self.format_var(*var)
                ));
                self.newline();
                self.print_child_body(rest);
            }
            IRBody::USet {
                var,
                idx,
                value,
                rest,
            } => {
                self.emit(&format!(
                    "{} {}[{idx}] = {}",
                    self.kw("uset"),
                    self.format_var(*var),
                    self.format_var(*value)
                ));
                self.newline();
                self.print_child_body(rest);
            }
            IRBody::SSet {
                var,
                n,
                offset,
                value,
                ty,
                rest,
            } => {
                self.emit(&format!(
                    "{} {}[{n}+{offset}]{} = {}",
                    self.kw("sset"),
                    self.format_var(*var),
                    self.type_ann(ty),
                    self.format_var(*value)
                ));
                self.newline();
                self.print_child_body(rest);
            }
            IRBody::Case {
                scrutinee,
                alts,
                default,
            } => {
                self.emit(&format!(
                    "{} {} {{",
                    self.kw("case"),
                    self.format_var(*scrutinee)
                ));
                self.indent();
                for alt in alts {
                    self.newline();
                    self.emit(&format!("| {} =>", self.format_ctor(&alt.ctor)));
                    self.indent();
                    self.newline();
                    self.print_child_body(&alt.body);
                    self.dedent();
                }
                if let Some(def) = default {
                    self.newline();
                    self.emit("| _ =>");
                    self.indent();
                    self.newline();
                    self.print_child_body(def);
                    self.dedent();
                }
                self.dedent();
                self.newline();
                self.emit("}");
            }
            IRBody::Jmp { jp, args } => {
                if args.is_empty() {
                    self.emit(&format!("{} jp{}", self.kw("jmp"), jp.0));
                } else {
                    self.emit(&format!(
                        "{} jp{}({})",
                        self.kw("jmp"),
                        jp.0,
                        self.format_args(args)
                    ));
                }
            }
            IRBody::Ret(arg) => self.emit(&format!("{} {}", self.kw("ret"), self.format_arg(arg))),
            IRBody::Unreachable => self.emit(&self.kw("unreachable")),
        }
    }

    fn emit_rc(&mut self, op: &str, var: VarId, n: Option<u32>) {
        let kw = if self.cfg.show_rc_annotations {
            self.rc_s(op)
        } else {
            self.kw(op)
        };
        let prefix = if self.cfg.show_rc_annotations {
            "[RC] "
        } else {
            ""
        };
        let vs = self.format_var(var);
        match n {
            Some(1) | None => self.emit(&format!("{prefix}{kw} {vs}")),
            Some(cnt) => self.emit(&format!("{prefix}{kw} {vs} {cnt}")),
        }
    }

    pub(crate) fn print_decl(&mut self, decl: &IRDecl) {
        let ret = if self.cfg.show_types {
            format!(" -> {}", self.format_type(&decl.return_type))
        } else {
            String::new()
        };
        self.emit(&format!(
            "{} {}({}){ret} {{",
            self.kw("def"),
            decl.name,
            self.format_params(&decl.params)
        ));
        self.indent();
        self.newline();
        self.print_body(&decl.body);
        self.dedent();
        self.newline();
        self.emit("}");
    }
}

// ── Declaration summary ────────────────────────────────────────────

/// Compact one-line summary: name, params, body size, RC ops.
#[must_use]
pub(crate) fn decl_summary(decl: &IRDecl) -> String {
    let (incs, decs) = ir_rc_ops_count(&decl.body);
    format!(
        "{}: {} params, {} nodes, depth {}, rc {}/{}",
        decl.name,
        decl.params.len(),
        ir_body_node_count(&decl.body),
        ir_body_depth(&decl.body),
        incs,
        decs
    )
}

#[must_use]
pub(crate) fn decl_summaries(decls: &[IRDecl]) -> String {
    decls
        .iter()
        .map(decl_summary)
        .collect::<Vec<_>>()
        .join("\n")
}

// ── DOT/Graphviz CFG output ────────────────────────────────────────

/// Emit DOT format for the control flow graph of a function body.
#[must_use]
pub(crate) fn cfg_to_dot(decl: &IRDecl) -> String {
    let mut dot = String::with_capacity(512);
    let _ = writeln!(dot, "digraph \"{}\" {{", decl.name);
    let _ = writeln!(
        dot,
        "  node [shape=box fontname=\"monospace\" fontsize=10];"
    );
    let _ = writeln!(dot, "  n0 [label=\"entry: {}\"];", decl.name);
    let mut id = 1u32;
    cfg_walk(&decl.body, &mut dot, &mut id, Some(0));
    let _ = writeln!(dot, "}}");
    dot
}

fn cfg_walk(body: &IRBody, dot: &mut String, id: &mut u32, parent: Option<u32>) {
    let my_id = *id;
    *id += 1;
    let _ = writeln!(dot, "  n{my_id} [label={:?}];", cfg_label(body));
    if let Some(p) = parent {
        let _ = writeln!(dot, "  n{p} -> n{my_id};");
    }
    match body {
        IRBody::VDecl { rest, .. }
        | IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => cfg_walk(rest, dot, id, Some(my_id)),
        IRBody::JDecl { body: jb, rest, .. } => {
            cfg_walk(jb, dot, id, Some(my_id));
            cfg_walk(rest, dot, id, Some(my_id));
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                cfg_walk(&alt.body, dot, id, Some(my_id));
            }
            if let Some(def) = default {
                cfg_walk(def, dot, id, Some(my_id));
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

fn cfg_label(body: &IRBody) -> String {
    match body {
        IRBody::VDecl { var, .. } => format!("let x{}", var.0),
        IRBody::JDecl { jp, .. } => format!("jp jp{}", jp.0),
        IRBody::Inc { var, n, .. } => format!("inc x{} {n}", var.0),
        IRBody::Dec { var, .. } => format!("dec x{}", var.0),
        IRBody::Set { var, idx, .. } => format!("set x{}[{idx}]", var.0),
        IRBody::SetTag { var, tag, .. } => format!("setTag x{} {tag}", var.0),
        IRBody::USet { var, idx, .. } => format!("uset x{}[{idx}]", var.0),
        IRBody::SSet { var, n, offset, .. } => format!("sset x{}[{n}+{offset}]", var.0),
        IRBody::Case { scrutinee, .. } => format!("case x{}", scrutinee.0),
        IRBody::Jmp { jp, .. } => format!("jmp jp{}", jp.0),
        IRBody::Ret(_) => "ret".into(),
        IRBody::Unreachable => "unreachable".into(),
    }
}

// ── IR diff display ────────────────────────────────────────────────

/// Show differences between two IR trees with +/- markers (line-by-line).
#[must_use]
pub(crate) fn ir_diff(old: &IRDecl, new: &IRDecl) -> String {
    let old_text = print_with_cfg(old, Ext2Config::default());
    let new_text = print_with_cfg(new, Ext2Config::default());
    let old_lines: Vec<&str> = old_text.lines().collect();
    let new_lines: Vec<&str> = new_text.lines().collect();
    let mut out = String::new();
    for i in 0..old_lines.len().max(new_lines.len()) {
        match (old_lines.get(i).copied(), new_lines.get(i).copied()) {
            (Some(o), Some(n)) if o == n => {
                let _ = writeln!(out, "  {o}");
            }
            (Some(o), Some(n)) => {
                let _ = writeln!(out, "- {o}");
                let _ = writeln!(out, "+ {n}");
            }
            (Some(o), None) => {
                let _ = writeln!(out, "- {o}");
            }
            (None, Some(n)) => {
                let _ = writeln!(out, "+ {n}");
            }
            (None, None) => {}
        }
    }
    out
}

fn print_with_cfg(decl: &IRDecl, cfg: Ext2Config) -> String {
    let mut p = Ext2Printer::new(cfg);
    p.print_decl(decl);
    p.into_string()
}

// ── Statistics table ───────────────────────────────────────────────

/// Format pass statistics as an aligned table.
#[must_use]
pub(crate) fn format_stats_table(entries: &[(&str, &[(&str, usize)])]) -> String {
    if entries.is_empty() {
        return String::new();
    }
    let name_w = entries
        .iter()
        .map(|(n, _)| n.len())
        .max()
        .unwrap_or(4)
        .max(4);
    let mut all_keys: Vec<&str> = Vec::new();
    for (_, kvs) in entries {
        for (k, _) in *kvs {
            if !all_keys.contains(k) {
                all_keys.push(k);
            }
        }
    }
    let col_w: Vec<usize> = all_keys.iter().map(|k| k.len().max(6)).collect();
    let mut out = String::new();
    let _ = write!(out, "{:<width$}", "Pass", width = name_w);
    for (i, k) in all_keys.iter().enumerate() {
        let _ = write!(out, "  {:>width$}", k, width = col_w[i]);
    }
    out.push('\n');
    for _ in 0..name_w {
        out.push('-');
    }
    for w in &col_w {
        out.push_str("  ");
        for _ in 0..*w {
            out.push('-');
        }
    }
    out.push('\n');
    for (name, kvs) in entries {
        let _ = write!(out, "{:<width$}", name, width = name_w);
        for (i, key) in all_keys.iter().enumerate() {
            let val = kvs
                .iter()
                .find(|(k, _)| k == key)
                .map(|(_, v)| *v)
                .unwrap_or(0);
            let _ = write!(out, "  {:>width$}", val, width = col_w[i]);
        }
        out.push('\n');
    }
    out
}

// ── HTML output ────────────────────────────────────────────────────

/// Emit syntax-highlighted HTML for a declaration.
#[must_use]
pub(crate) fn decl_to_html(decl: &IRDecl) -> String {
    let mut p = Ext2Printer::new(Ext2Config {
        html_mode: true,
        ansi_color: false,
        ..Ext2Config::default()
    });
    p.print_decl(decl);
    let body = p.into_string();
    format!("<pre class=\"ir-code\">\n{body}\n</pre>")
}

fn html_escape(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}

// ── Convenience ────────────────────────────────────────────────────

#[must_use]
pub(crate) fn pretty_ext2(decl: &IRDecl, format: OutputFormat) -> String {
    print_with_cfg(
        decl,
        match format {
            OutputFormat::Compact => Ext2Config::compact(),
            OutputFormat::Verbose => Ext2Config::default(),
            OutputFormat::Debug => Ext2Config::debug(),
        },
    )
}

#[must_use]
pub(crate) fn pretty_ext2_body(body: &IRBody, cfg: Ext2Config) -> String {
    let mut p = Ext2Printer::new(cfg);
    p.print_body(body);
    p.into_string()
}
