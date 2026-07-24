// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//! Enhanced IR pretty printing with LCNF support

use crate::ir::{
    CtorInfo, FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, JoinPointId, VarId,
};
use crate::lcnf::{
    self, Alt as LcnfAlt, Arg as LcnfArg, Cases, Code, Decl as LcnfDecl, DeclValue, LetValue,
    Param as LcnfParam,
};
use clean_kernel::{BigNat, Expr, FVarId, Level, Literal, Name};
use std::collections::HashMap;

const RESET: &str = "\x1b[0m";
const KW: &str = "\x1b[1;34m";
const RC: &str = "\x1b[1;31m";
const TY: &str = "\x1b[32m";
const CTOR: &str = "\x1b[33m";

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ExtPrettyConfig {
    pub(crate) indent_size: usize,
    pub(crate) show_types: bool,
    pub(crate) highlight_rc: bool,
    pub(crate) color: bool,
    pub(crate) summary_mode: bool,
    pub(crate) stable_ordering: bool,
}

impl Default for ExtPrettyConfig {
    fn default() -> Self {
        Self {
            indent_size: 2,
            show_types: true,
            highlight_rc: false,
            color: false,
            summary_mode: false,
            stable_ordering: false,
        }
    }
}

pub(crate) struct ExtIrPrinter {
    config: ExtPrettyConfig,
    output: String,
    indent_level: usize,
}

impl ExtIrPrinter {
    pub(crate) fn new(config: ExtPrettyConfig) -> Self {
        Self {
            config,
            output: String::new(),
            indent_level: 0,
        }
    }
    pub(crate) fn into_string(mut self) -> String {
        while self.output.ends_with('\n') {
            self.output.pop();
        }
        self.output
    }

    pub(crate) fn print_ir_decl(&mut self, decl: &IRDecl) {
        if self.config.summary_mode {
            self.summary_ir_decl(decl);
            return;
        }
        let sig = if self.config.show_types {
            format!(
                "{} {}({}) -> {} {{",
                self.kw("def"),
                decl.name,
                self.ir_params(&decl.params),
                self.ir_type(&decl.return_type)
            )
        } else {
            format!(
                "{} {}({}) {{",
                self.kw("def"),
                decl.name,
                self.ir_params(&decl.params)
            )
        };
        self.line(sig);
        self.indent_level += 1;
        self.print_ir_body(&decl.body);
        self.indent_level -= 1;
        self.line("}");
    }

    pub(crate) fn print_ir_body(&mut self, body: &IRBody) {
        match body {
            IRBody::VDecl {
                var,
                ty,
                value,
                rest,
            } => {
                let s = if self.config.show_types {
                    format!(
                        "{} {}: {} = {}",
                        self.kw("let"),
                        self.v(*var),
                        self.ir_type(ty),
                        self.ir_expr(value)
                    )
                } else {
                    format!(
                        "{} {} = {}",
                        self.kw("let"),
                        self.v(*var),
                        self.ir_expr(value)
                    )
                };
                self.line(s);
                self.print_ir_body(rest);
            }
            IRBody::JDecl {
                jp,
                params,
                body,
                rest,
            } => {
                self.line(format!(
                    "{} {}({}) {{",
                    self.kw("jp"),
                    self.jp(*jp),
                    self.ir_params(params)
                ));
                self.indent_level += 1;
                self.print_ir_body(body);
                self.indent_level -= 1;
                self.line("}");
                self.print_ir_body(rest);
            }
            IRBody::Inc { var, n, rest } => {
                self.line(format!(
                    "{}{} {} {}",
                    self.rc_prefix(),
                    self.rc_kw("inc"),
                    self.v(*var),
                    n
                ));
                self.print_ir_body(rest);
            }
            IRBody::Dec { var, rest } => {
                self.line(format!(
                    "{}{} {}",
                    self.rc_prefix(),
                    self.rc_kw("dec"),
                    self.v(*var)
                ));
                self.print_ir_body(rest);
            }
            IRBody::Set {
                var,
                idx,
                value,
                rest,
            } => {
                self.line(format!(
                    "{} {}[{}] = {}",
                    self.kw("set"),
                    self.v(*var),
                    idx,
                    self.v(*value)
                ));
                self.print_ir_body(rest);
            }
            IRBody::SetTag { var, tag, rest } => {
                self.line(format!("{} {} {}", self.kw("set_tag"), self.v(*var), tag));
                self.print_ir_body(rest);
            }
            IRBody::USet {
                var,
                idx,
                value,
                rest,
            } => {
                self.line(format!(
                    "{} {}[{}] = {}",
                    self.kw("uset"),
                    self.v(*var),
                    idx,
                    self.v(*value)
                ));
                self.print_ir_body(rest);
            }
            IRBody::SSet {
                var,
                n,
                offset,
                value,
                ty,
                rest,
            } => {
                let ann = if self.config.show_types {
                    format!(": {}", self.ir_type(ty))
                } else {
                    String::new()
                };
                self.line(format!(
                    "{} {}[{}+{}]{} = {}",
                    self.kw("sset"),
                    self.v(*var),
                    n,
                    offset,
                    ann,
                    self.v(*value)
                ));
                self.print_ir_body(rest);
            }
            IRBody::Case {
                scrutinee,
                alts,
                default,
            } => {
                self.line(format!("{} {} {{", self.kw("case"), self.v(*scrutinee)));
                self.indent_level += 1;
                for alt in alts {
                    self.print_ir_alt(alt);
                }
                if let Some(body) = default {
                    self.line("| _ =>");
                    self.indent_level += 1;
                    self.print_ir_body(body);
                    self.indent_level -= 1;
                }
                self.indent_level -= 1;
                self.line("}");
            }
            IRBody::Jmp { jp, args } => self.line(format!(
                "{} {}({})",
                self.kw("jmp"),
                self.jp(*jp),
                self.ir_args(args)
            )),
            IRBody::Ret(arg) => self.line(format!("{} {}", self.kw("ret"), self.ir_arg(arg))),
            IRBody::Unreachable => self.line(self.kw("unreachable")),
        }
    }

    pub(crate) fn print_ir_decls(&mut self, decls: &[IRDecl]) {
        let mut items: Vec<_> = decls.iter().collect();
        if self.config.stable_ordering {
            items.sort_by_key(|d| d.name.to_string());
        }
        for (i, decl) in items.iter().enumerate() {
            self.print_ir_decl(decl);
            if i + 1 != items.len() && !self.config.summary_mode {
                self.output.push('\n');
            }
        }
    }

    pub(crate) fn print_lcnf_code(&mut self, code: &Code) {
        match code {
            Code::Let(decl, body) => {
                let s = if self.config.show_types {
                    format!(
                        "{} {}: {} = {}",
                        self.kw("let"),
                        self.nf(&decl.name, decl.fvar_id),
                        self.kty(&decl.ty),
                        self.lval(&decl.value)
                    )
                } else {
                    format!(
                        "{} {} = {}",
                        self.kw("let"),
                        self.nf(&decl.name, decl.fvar_id),
                        self.lval(&decl.value)
                    )
                };
                self.line(s);
                self.print_lcnf_code(body);
            }
            Code::Fun(decl, body) => {
                let s = if self.config.show_types {
                    format!(
                        "{} {}({}) : {} {{",
                        self.kw("fun"),
                        self.nf(&decl.name, decl.fvar_id),
                        self.lparams(&decl.params),
                        self.kty(&decl.ty)
                    )
                } else {
                    format!(
                        "{} {}({}) {{",
                        self.kw("fun"),
                        self.nf(&decl.name, decl.fvar_id),
                        self.lparams(&decl.params)
                    )
                };
                self.line(s);
                self.indent_level += 1;
                self.print_lcnf_code(&decl.body);
                self.indent_level -= 1;
                self.line("}");
                self.print_lcnf_code(body);
            }
            Code::JoinPoint(decl, body) => {
                let s = if self.config.show_types {
                    format!(
                        "{} {}({}) : {} {{",
                        self.kw("jp"),
                        self.nf(&decl.name, decl.fvar_id),
                        self.lparams(&decl.params),
                        self.kty(&decl.ty)
                    )
                } else {
                    format!(
                        "{} {}({}) {{",
                        self.kw("jp"),
                        self.nf(&decl.name, decl.fvar_id),
                        self.lparams(&decl.params)
                    )
                };
                self.line(s);
                self.indent_level += 1;
                self.print_lcnf_code(&decl.body);
                self.indent_level -= 1;
                self.line("}");
                self.print_lcnf_code(body);
            }
            Code::Cases(cases) => self.print_lcnf_cases(cases),
            Code::Jmp { jp, args } => self.line(format!(
                "{} {}({})",
                self.kw("jmp"),
                self.fv(*jp),
                self.largs(args)
            )),
            Code::Return(fvar) => self.line(format!("{} {}", self.kw("return"), self.fv(*fvar))),
            Code::Unreachable(ty) => {
                let s = if self.config.show_types {
                    format!("{} : {}", self.kw("unreachable"), self.kty(ty))
                } else {
                    self.kw("unreachable")
                };
                self.line(s);
            }
        }
    }

    pub(crate) fn print_lcnf_decl(&mut self, decl: &LcnfDecl) {
        if self.config.summary_mode {
            self.summary_lcnf_decl(decl);
            return;
        }
        let s = if self.config.show_types {
            format!(
                "{} {}{}({}) : {} {{",
                self.kw("def"),
                decl.name,
                self.lparams_names(&decl.level_params),
                self.lparams(&decl.params),
                self.kty(&decl.ty)
            )
        } else {
            format!(
                "{} {}{}({}) {{",
                self.kw("def"),
                decl.name,
                self.lparams_names(&decl.level_params),
                self.lparams(&decl.params)
            )
        };
        self.line(s);
        self.indent_level += 1;
        match &decl.body {
            DeclValue::Code(code) => self.print_lcnf_code(code),
            DeclValue::Extern(attr) => {
                let es = attr
                    .entries
                    .iter()
                    .map(|e| format!("[{}:{}]", e.backend, e.name))
                    .collect::<Vec<_>>()
                    .join(" ");
                self.line(format!("{} {}", self.kw("extern"), es));
            }
        }
        self.indent_level -= 1;
        self.line("}");
    }

    pub(crate) fn print_lcnf_decls(&mut self, decls: &[LcnfDecl]) {
        let mut items: Vec<_> = decls.iter().collect();
        if self.config.stable_ordering {
            items.sort_by_key(|d| d.name.to_string());
        }
        for (i, decl) in items.iter().enumerate() {
            self.print_lcnf_decl(decl);
            if i + 1 != items.len() && !self.config.summary_mode {
                self.output.push('\n');
            }
        }
    }

    pub(crate) fn summary_ir_decl(&mut self, decl: &IRDecl) {
        let ty = if self.config.show_types {
            format!(" -> {}", self.ir_type(&decl.return_type))
        } else {
            String::new()
        };
        self.line(format!(
            "{} {}({} params){} [{} nodes]",
            self.kw("def"),
            decl.name,
            decl.params.len(),
            ty,
            ir_body_node_count(&decl.body)
        ));
    }

    pub(crate) fn summary_lcnf_decl(&mut self, decl: &LcnfDecl) {
        let ty = if self.config.show_types {
            format!(" : {}", self.kty(&decl.ty))
        } else {
            String::new()
        };
        let tail = match &decl.body {
            DeclValue::Code(code) => format!("[{} nodes]", lcnf_nodes(code)),
            DeclValue::Extern(a) => format!("[extern {} entries]", a.entries.len()),
        };
        self.line(format!(
            "{} {}({} params){} {}",
            self.kw("def"),
            decl.name,
            decl.params.len(),
            ty,
            tail
        ));
    }

    fn print_ir_alt(&mut self, alt: &IRAlt) {
        self.line(format!("| {} =>", self.ctor_info(&alt.ctor)));
        self.indent_level += 1;
        self.print_ir_body(&alt.body);
        self.indent_level -= 1;
    }
    fn print_lcnf_cases(&mut self, cases: &Cases) {
        let s = if self.config.show_types {
            format!(
                "{} {} of {} -> {} {{",
                self.kw("case"),
                self.fv(cases.scrutinee),
                cases.type_name,
                self.kty(&cases.result_type)
            )
        } else {
            format!(
                "{} {} of {} {{",
                self.kw("case"),
                self.fv(cases.scrutinee),
                cases.type_name
            )
        };
        self.line(s);
        self.indent_level += 1;
        for alt in &cases.alts {
            match alt {
                LcnfAlt::Ctor {
                    ctor_name,
                    params,
                    body,
                } => {
                    self.line(format!(
                        "| {}({}) =>",
                        self.ctor(ctor_name),
                        self.lparams(params)
                    ));
                    self.indent_level += 1;
                    self.print_lcnf_code(body);
                    self.indent_level -= 1;
                }
                LcnfAlt::Default(body) => {
                    self.line("| _ =>");
                    self.indent_level += 1;
                    self.print_lcnf_code(body);
                    self.indent_level -= 1;
                }
            }
        }
        self.indent_level -= 1;
        self.line("}");
    }

    fn line<S: AsRef<str>>(&mut self, s: S) {
        for _ in 0..self.indent_level * self.config.indent_size {
            self.output.push(' ');
        }
        self.output.push_str(s.as_ref());
        self.output.push('\n');
    }
    fn paint<T: ToString>(&self, code: &str, s: T) -> String {
        let s = s.to_string();
        if self.config.color {
            format!("{code}{s}{RESET}")
        } else {
            s
        }
    }
    fn kw(&self, s: &str) -> String {
        self.paint(KW, s)
    }
    fn rc_kw(&self, s: &str) -> String {
        self.paint(RC, s)
    }
    fn t(&self, s: String) -> String {
        self.paint(TY, s)
    }
    fn ctor(&self, n: &Name) -> String {
        self.paint(CTOR, n)
    }
    fn rc_prefix(&self) -> &'static str {
        if self.config.highlight_rc {
            "[RC] "
        } else {
            ""
        }
    }
    fn v(&self, v: VarId) -> String {
        format!("x{}", v.0)
    }
    fn jp(&self, jp: JoinPointId) -> String {
        format!("jp{}", jp.0)
    }
    fn fv(&self, fv: FVarId) -> String {
        format!("_x{}", fv.as_u64())
    }
    fn nf(&self, name: &Name, fv: FVarId) -> String {
        let n = name.to_string();
        if n.is_empty() || n == "_" {
            self.fv(fv)
        } else {
            format!("{n}@{}", fv.as_u64())
        }
    }
    fn fmt_nat(&self, n: &BigNat) -> String {
        n.to_string()
    }
    fn fmt_levels(&self, levels: &[Level]) -> String {
        if levels.is_empty() {
            String::new()
        } else {
            format!(
                ".{{{}}}",
                levels
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        }
    }
    fn lparams_names(&self, ns: &[Name]) -> String {
        if ns.is_empty() {
            String::new()
        } else {
            format!(
                ".{{{}}}",
                ns.iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        }
    }
    fn ir_type(&self, ty: &IRType) -> String {
        self.t(self.ir_type_raw(ty))
    }
    fn ir_type_raw(&self, ty: &IRType) -> String {
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
            IRType::Struct(xs) => format!(
                "Struct({})",
                xs.iter()
                    .map(|x| self.ir_type_raw(x))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            IRType::Union(xs) => format!(
                "Union({})",
                xs.iter()
                    .map(|x| self.ir_type_raw(x))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            IRType::Erased => "Erased".into(),
            IRType::Void => "Void".into(),
        }
    }
    fn kty(&self, e: &Expr) -> String {
        self.t(e.to_string())
    }
    fn ir_arg(&self, a: &IRArg) -> String {
        match a {
            IRArg::Var(v) => self.v(*v),
            IRArg::Erased => "erased".into(),
        }
    }
    fn ir_args(&self, xs: &[IRArg]) -> String {
        xs.iter()
            .map(|x| self.ir_arg(x))
            .collect::<Vec<_>>()
            .join(", ")
    }
    fn ir_params(&self, xs: &[(VarId, IRType)]) -> String {
        xs.iter()
            .map(|(v, ty)| {
                if self.config.show_types {
                    format!("{}: {}", self.v(*v), self.ir_type(ty))
                } else {
                    self.v(*v)
                }
            })
            .collect::<Vec<_>>()
            .join(", ")
    }
    fn ctor_info(&self, c: &CtorInfo) -> String {
        self.ctor(&c.name)
    }
    fn ir_lit(&self, l: &IRLiteral) -> String {
        match l {
            IRLiteral::Bool(v) => v.to_string(),
            IRLiteral::UInt8(v) => format!("{v}u8"),
            IRLiteral::UInt16(v) => format!("{v}u16"),
            IRLiteral::UInt32(v) => format!("{v}u32"),
            IRLiteral::UInt64(v) => format!("{v}u64"),
            IRLiteral::USize(v) => format!("{v}usize"),
            IRLiteral::NatBig(v) => format!("{v}nat"),
            IRLiteral::Float32(v) => format!("{v}f32"),
            IRLiteral::Float64(v) => format!("{v}f64"),
        }
    }
    fn ir_call(&self, h: String, xs: &[IRArg]) -> String {
        if xs.is_empty() {
            h
        } else {
            format!("{h}({})", self.ir_args(xs))
        }
    }
    fn fn_id(&self, f: &FnId) -> String {
        f.0.to_string()
    }
    fn ir_expr(&self, e: &IRExpr) -> String {
        match e {
            IRExpr::Ctor { info, args } => self.ir_call(
                format!("{} {}", self.kw("ctor"), self.ctor_info(info)),
                args,
            ),
            IRExpr::Proj { idx, ty, arg } => format!(
                "{}[{}]({}){}",
                self.kw("proj"),
                idx,
                self.ir_arg(arg),
                if self.config.show_types {
                    format!(": {}", self.ir_type(ty))
                } else {
                    String::new()
                }
            ),
            IRExpr::Tag(a) => format!("{}({})", self.kw("tag"), self.ir_arg(a)),
            IRExpr::Box { ty, arg } => format!(
                "{}[{}]({})",
                self.kw("box"),
                self.ir_type(ty),
                self.ir_arg(arg)
            ),
            IRExpr::Unbox { ty, arg } => format!(
                "{}[{}]({})",
                self.kw("unbox"),
                self.ir_type(ty),
                self.ir_arg(arg)
            ),
            IRExpr::Lit(l) => self.ir_lit(l),
            IRExpr::Apply { fn_id, args } => {
                self.ir_call(format!("{} {}", self.kw("apply"), self.fn_id(fn_id)), args)
            }
            IRExpr::PartialApply { fn_id, arity, args } => self.ir_call(
                format!(
                    "{} {}/{}",
                    self.kw("partial_apply"),
                    self.fn_id(fn_id),
                    arity
                ),
                args,
            ),
            IRExpr::ClosureApply { closure, args } => self.ir_call(
                format!("{} {}", self.kw("closure_apply"), self.ir_arg(closure)),
                args,
            ),
            IRExpr::UProj { idx, var } => {
                format!("{}[{}]({})", self.kw("uproj"), idx, self.v(*var))
            }
            IRExpr::SProj { n, offset, var, ty } => format!(
                "{}[{}+{}]({}){}",
                self.kw("sproj"),
                n,
                offset,
                self.v(*var),
                if self.config.show_types {
                    format!(": {}", self.ir_type(ty))
                } else {
                    String::new()
                }
            ),
            IRExpr::IsShared(v) => format!("{}({})", self.kw("is_shared"), self.v(*v)),
            IRExpr::String(s) => format!("{s:?}"),
            IRExpr::Reset(v) => format!("{}({})", self.kw("reset"), self.v(*v)),
            IRExpr::Reuse { var, ctor, args } => self.ir_call(
                format!(
                    "{} {} as {}",
                    self.kw("reuse"),
                    self.v(*var),
                    self.ctor_info(ctor)
                ),
                args,
            ),
        }
    }
    fn lparam(&self, p: &LcnfParam) -> String {
        let h = if p.borrow {
            format!("{} {}", self.kw("borrow"), self.nf(&p.name, p.fvar_id))
        } else {
            self.nf(&p.name, p.fvar_id)
        };
        if self.config.show_types {
            format!("{h}: {}", self.kty(&p.ty))
        } else {
            h
        }
    }
    fn lparams(&self, xs: &[LcnfParam]) -> String {
        xs.iter()
            .map(|x| self.lparam(x))
            .collect::<Vec<_>>()
            .join(", ")
    }
    fn larg(&self, a: &LcnfArg) -> String {
        match a {
            LcnfArg::Erased => "erased".into(),
            LcnfArg::FVar(v) => self.fv(*v),
            LcnfArg::Type(e) => format!("@{}", self.kty(e)),
            LcnfArg::Index(i) => format!("#{i}"),
        }
    }
    fn largs(&self, xs: &[LcnfArg]) -> String {
        xs.iter()
            .map(|x| self.larg(x))
            .collect::<Vec<_>>()
            .join(", ")
    }
    fn llit(&self, l: &Literal) -> String {
        match l {
            Literal::Nat(n) => self.fmt_nat(n),
            Literal::String(s) => format!("{s:?}"),
        }
    }
    fn lcall(&self, h: String, xs: &[LcnfArg]) -> String {
        if xs.is_empty() {
            h
        } else {
            format!("{h}({})", self.largs(xs))
        }
    }
    fn lval(&self, v: &LetValue) -> String {
        match v {
            LetValue::Lit(l) => self.llit(l),
            LetValue::Erased => "erased".into(),
            LetValue::Proj {
                type_name,
                idx,
                structure,
            } => format!(
                "{} {}.{}({})",
                self.kw("proj"),
                type_name,
                idx,
                self.fv(*structure)
            ),
            LetValue::Const { name, levels, args } => {
                self.lcall(format!("{name}{}", self.fmt_levels(levels)), args)
            }
            LetValue::FVar { fvar, args } => self.lcall(self.fv(*fvar), args),
            LetValue::Ctor { name, levels, args } => self.lcall(
                format!("{}{}", self.ctor(name), self.fmt_levels(levels)),
                args,
            ),
            LetValue::Reuse {
                slot,
                ctor_name,
                levels,
                args,
            } => self.lcall(
                format!(
                    "{} {} as {}{}",
                    self.kw("reuse"),
                    self.fv(*slot),
                    self.ctor(ctor_name),
                    self.fmt_levels(levels)
                ),
                args,
            ),
        }
    }
}

pub(crate) fn ir_body_depth(body: &IRBody) -> usize {
    match body {
        IRBody::VDecl { rest, .. }
        | IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => 1 + ir_body_depth(rest),
        IRBody::JDecl { body, rest, .. } => 1 + ir_body_depth(body).max(ir_body_depth(rest)),
        IRBody::Case { alts, default, .. } => {
            1 + alts
                .iter()
                .map(|a| ir_body_depth(&a.body))
                .max()
                .unwrap_or(0)
                .max(default.as_deref().map(ir_body_depth).unwrap_or(0))
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => 1,
    }
}

pub(crate) fn ir_body_node_count(body: &IRBody) -> usize {
    match body {
        IRBody::VDecl { rest, .. }
        | IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => 1 + ir_body_node_count(rest),
        IRBody::JDecl { body, rest, .. } => 1 + ir_body_node_count(body) + ir_body_node_count(rest),
        IRBody::Case { alts, default, .. } => {
            1 + alts
                .iter()
                .map(|a| ir_body_node_count(&a.body))
                .sum::<usize>()
                + default.as_deref().map(ir_body_node_count).unwrap_or(0)
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => 1,
    }
}

pub(crate) fn ir_var_usage(body: &IRBody) -> HashMap<VarId, usize> {
    let mut out = HashMap::new();
    walk_body(body, &mut out);
    out
}

pub(crate) fn ir_rc_ops_count(body: &IRBody) -> (usize, usize) {
    match body {
        IRBody::VDecl { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => ir_rc_ops_count(rest),
        IRBody::JDecl { body, rest, .. } => {
            let (i1, d1) = ir_rc_ops_count(body);
            let (i2, d2) = ir_rc_ops_count(rest);
            (i1 + i2, d1 + d2)
        }
        IRBody::Inc { rest, .. } => {
            let (i, d) = ir_rc_ops_count(rest);
            (i + 1, d)
        }
        IRBody::Dec { rest, .. } => {
            let (i, d) = ir_rc_ops_count(rest);
            (i, d + 1)
        }
        IRBody::Case { alts, default, .. } => {
            let mut out = (0, 0);
            for alt in alts {
                let (i, d) = ir_rc_ops_count(&alt.body);
                out.0 += i;
                out.1 += d;
            }
            if let Some(b) = default {
                let (i, d) = ir_rc_ops_count(b);
                out.0 += i;
                out.1 += d;
            }
            out
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => (0, 0),
    }
}

pub(crate) fn pretty_print_ir_ext(decl: &IRDecl) -> String {
    let mut p = ExtIrPrinter::new(ExtPrettyConfig::default());
    p.print_ir_decl(decl);
    p.into_string()
}
pub(crate) fn pretty_print_lcnf(decl: &lcnf::Decl) -> String {
    let mut p = ExtIrPrinter::new(ExtPrettyConfig::default());
    p.print_lcnf_decl(decl);
    p.into_string()
}
pub(crate) fn pretty_print_ir_stats(decl: &IRDecl) -> String {
    let (incs, decs) = ir_rc_ops_count(&decl.body);
    let mut vars: Vec<_> = ir_var_usage(&decl.body).into_iter().collect();
    vars.sort_by_key(|(v, _)| v.0);
    let usage = if vars.is_empty() {
        "none".into()
    } else {
        vars.iter()
            .map(|(v, n)| format!("x{}={}", v.0, n))
            .collect::<Vec<_>>()
            .join(", ")
    };
    format!(
        "def {}: nodes={}, depth={}, incs={}, decs={}, vars=[{}]",
        decl.name,
        ir_body_node_count(&decl.body),
        ir_body_depth(&decl.body),
        incs,
        decs,
        usage
    )
}

fn lcnf_nodes(code: &Code) -> usize {
    match code {
        Code::Let(_, b) | Code::Fun(_, b) | Code::JoinPoint(_, b) => 1 + lcnf_nodes(b),
        Code::Cases(c) => {
            1 + c
                .alts
                .iter()
                .map(|a| match a {
                    LcnfAlt::Ctor { body, .. } | LcnfAlt::Default(body) => lcnf_nodes(body),
                })
                .sum::<usize>()
        }
        Code::Jmp { .. } | Code::Return(_) | Code::Unreachable(_) => 1,
    }
}

fn walk_body(body: &IRBody, out: &mut HashMap<VarId, usize>) {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            walk_expr(value, out);
            walk_body(rest, out);
        }
        IRBody::JDecl { body, rest, .. } => {
            walk_body(body, out);
            walk_body(rest, out);
        }
        IRBody::Inc { var, rest, .. }
        | IRBody::Dec { var, rest }
        | IRBody::SetTag { var, rest, .. } => {
            bump(out, *var);
            walk_body(rest, out);
        }
        IRBody::Set {
            var, value, rest, ..
        }
        | IRBody::USet {
            var, value, rest, ..
        }
        | IRBody::SSet {
            var, value, rest, ..
        } => {
            bump(out, *var);
            bump(out, *value);
            walk_body(rest, out);
        }
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            bump(out, *scrutinee);
            for alt in alts {
                walk_body(&alt.body, out);
            }
            if let Some(b) = default {
                walk_body(b, out);
            }
        }
        IRBody::Jmp { args, .. } => {
            for a in args {
                walk_arg(a, out);
            }
        }
        IRBody::Ret(arg) => walk_arg(arg, out),
        IRBody::Unreachable => {}
    }
}

fn walk_expr(expr: &IRExpr, out: &mut HashMap<VarId, usize>) {
    match expr {
        IRExpr::Ctor { args, .. }
        | IRExpr::Apply { args, .. }
        | IRExpr::PartialApply { args, .. } => {
            for a in args {
                walk_arg(a, out);
            }
        }
        IRExpr::Proj { arg, .. }
        | IRExpr::Tag(arg)
        | IRExpr::Box { arg, .. }
        | IRExpr::Unbox { arg, .. } => walk_arg(arg, out),
        IRExpr::ClosureApply { closure, args } => {
            walk_arg(closure, out);
            for a in args {
                walk_arg(a, out);
            }
        }
        IRExpr::UProj { var, .. }
        | IRExpr::SProj { var, .. }
        | IRExpr::IsShared(var)
        | IRExpr::Reset(var) => bump(out, *var),
        IRExpr::Reuse { var, args, .. } => {
            bump(out, *var);
            for a in args {
                walk_arg(a, out);
            }
        }
        IRExpr::Lit(_) | IRExpr::String(_) => {}
    }
}

fn walk_arg(arg: &IRArg, out: &mut HashMap<VarId, usize>) {
    if let IRArg::Var(v) = arg {
        bump(out, *v);
    }
}
fn bump(out: &mut HashMap<VarId, usize>, var: VarId) {
    *out.entry(var).or_insert(0) += 1;
}
