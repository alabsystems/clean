// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended IR back-translation: reconstruct Lean kernel `Expr` from compiler IR.
//!
//! Converts `IRBody`/`IRExpr`/`IRType` back into kernel `Expr` for debugging,
//! diagnostics, and round-trip validation. Erased information produces placeholder
//! expressions tracked by [`BackTranslateStats`].
//!
//! Part of #3083 — Extensibility.

use crate::ir::{CtorInfo, FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, VarId};
use clean_kernel::{BinderInfo, Expr, ExprKind, Level, Name};
use std::collections::HashMap;
use std::fmt;

/// Registry mapping IR identifiers back to human-readable names.
#[derive(Clone, Debug, Default)]
pub(crate) struct NameRegistry {
    var_names: HashMap<VarId, Name>,
    ctor_names: HashMap<u32, Name>,
    fn_names: HashMap<String, Name>,
}

impl NameRegistry {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn register_var(&mut self, var: VarId, name: Name) {
        self.var_names.insert(var, name);
    }
    pub(crate) fn register_ctor(&mut self, tag: u32, name: Name) {
        self.ctor_names.insert(tag, name);
    }
    pub(crate) fn register_fn(&mut self, fn_id: &str, name: Name) {
        self.fn_names.insert(fn_id.to_owned(), name);
    }

    #[must_use]
    pub(crate) fn var_name(&self, var: VarId) -> Name {
        self.var_names
            .get(&var)
            .cloned()
            .unwrap_or_else(|| Name::from_string(&format!("_x{}", var.0)))
    }
    #[must_use]
    pub(crate) fn ctor_name(&self, tag: u32) -> Option<&Name> {
        self.ctor_names.get(&tag)
    }
    #[must_use]
    pub(crate) fn fn_name(&self, key: &str) -> Option<&Name> {
        self.fn_names.get(key)
    }
    #[must_use]
    pub(crate) fn var_count(&self) -> usize {
        self.var_names.len()
    }
}

/// Reconstruction quality metrics.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct BackTranslateStats {
    pub(crate) terms_reconstructed: u64,
    pub(crate) names_recovered: u64,
    pub(crate) partial_reconstructions: u64,
    pub(crate) ctors_recovered: u64,
}

impl fmt::Display for BackTranslateStats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "reconstructed={}, names={}, partial={}, ctors={}",
            self.terms_reconstructed,
            self.names_recovered,
            self.partial_reconstructions,
            self.ctors_recovered,
        )
    }
}

/// Translates compiler IR back to kernel-level Lean `Expr`.
#[derive(Clone, Debug)]
pub(crate) struct BackTranslator {
    registry: NameRegistry,
    stats: BackTranslateStats,
}

impl BackTranslator {
    #[must_use]
    pub(crate) fn new(registry: NameRegistry) -> Self {
        Self {
            registry,
            stats: BackTranslateStats::default(),
        }
    }
    #[must_use]
    pub(crate) fn stats(&self) -> &BackTranslateStats {
        &self.stats
    }
    #[must_use]
    pub(crate) fn registry(&self) -> &NameRegistry {
        &self.registry
    }
    pub(crate) fn registry_mut(&mut self) -> &mut NameRegistry {
        &mut self.registry
    }

    // ----- Type reconstruction -----

    pub(crate) fn translate_type(&mut self, ty: &IRType) -> Expr {
        self.stats.terms_reconstructed += 1;
        match ty {
            IRType::Bool => Expr::const_str("Bool"),
            IRType::UInt8 => Expr::const_str("UInt8"),
            IRType::UInt16 => Expr::const_str("UInt16"),
            IRType::UInt32 => Expr::const_str("UInt32"),
            IRType::UInt64 => Expr::const_str("UInt64"),
            IRType::USize => Expr::const_str("USize"),
            IRType::Float32 => Expr::const_str("Float32"),
            IRType::Float64 => Expr::const_str("Float"),
            IRType::Object => Expr::const_str("Object"),
            IRType::TObject => Expr::const_str("TObject"),
            IRType::Struct(fs) => {
                let es: Vec<Expr> = fs.iter().map(|f| self.translate_type(f)).collect();
                es.into_iter().fold(Expr::const_str("Struct"), Expr::app)
            }
            IRType::Union(vs) => {
                let es: Vec<Expr> = vs.iter().map(|v| self.translate_type(v)).collect();
                es.into_iter().fold(Expr::const_str("Union"), Expr::app)
            }
            IRType::Erased => {
                self.stats.partial_reconstructions += 1;
                Expr::const_str("_erased")
            }
            IRType::Void => Expr::const_str("Unit"),
        }
    }

    // ----- Literal reconstruction -----

    pub(crate) fn translate_literal(&mut self, lit: &IRLiteral) -> Expr {
        self.stats.terms_reconstructed += 1;
        match lit {
            IRLiteral::Bool(true) => Expr::const_str("Bool.true"),
            IRLiteral::Bool(false) => Expr::const_str("Bool.false"),
            IRLiteral::UInt8(v) => Expr::nat_lit(u64::from(*v)),
            IRLiteral::UInt16(v) => Expr::nat_lit(u64::from(*v)),
            IRLiteral::UInt32(v) => Expr::nat_lit(u64::from(*v)),
            IRLiteral::UInt64(v) => Expr::nat_lit(*v),
            IRLiteral::USize(v) => Expr::nat_lit(*v as u64),
            IRLiteral::NatBig(v) => Expr::nat_lit_u128(*v),
            IRLiteral::Float32(_) | IRLiteral::Float64(_) => {
                self.stats.partial_reconstructions += 1;
                Expr::const_str("_float_literal")
            }
        }
    }

    // ----- Arg reconstruction -----

    pub(crate) fn translate_arg(&mut self, arg: &IRArg) -> Expr {
        match arg {
            IRArg::Var(v) => {
                let name = self.registry.var_name(*v);
                if self.registry.var_names.contains_key(v) {
                    self.stats.names_recovered += 1;
                }
                Expr::const_(name, Vec::<Level>::new())
            }
            IRArg::Erased => {
                self.stats.partial_reconstructions += 1;
                self.stats.terms_reconstructed += 1;
                Expr::const_str("_erased_arg")
            }
        }
    }

    fn recover_ctor_name(&mut self, info: &CtorInfo) -> Name {
        self.stats.ctors_recovered += 1;
        self.registry
            .ctor_name(info.tag)
            .cloned()
            .unwrap_or_else(|| info.name.clone())
    }

    fn var_expr(&self, var: VarId) -> Expr {
        Expr::const_(self.registry.var_name(var), Vec::<Level>::new())
    }

    // ----- IRExpr reconstruction -----

    pub(crate) fn translate_expr(&mut self, expr: &IRExpr) -> Expr {
        self.stats.terms_reconstructed += 1;
        match expr {
            IRExpr::Ctor { info, args } => {
                let name = self.recover_ctor_name(info);
                let base = Expr::const_(name, Vec::<Level>::new());
                args.iter()
                    .map(|a| self.translate_arg(a))
                    .fold(base, Expr::app)
            }
            IRExpr::Proj { idx, arg, .. } => {
                let a = self.translate_arg(arg);
                let n = Name::from_string(&format!("_proj{idx}"));
                Expr::from_kind(ExprKind::Proj(n, *idx, std::sync::Arc::new(a)))
            }
            IRExpr::Tag(arg) => Expr::app(Expr::const_str("_tag"), self.translate_arg(arg)),
            IRExpr::Box { arg, .. } => Expr::app(Expr::const_str("_box"), self.translate_arg(arg)),
            IRExpr::Unbox { arg, .. } => {
                Expr::app(Expr::const_str("_unbox"), self.translate_arg(arg))
            }
            IRExpr::Lit(lit) => self.translate_literal(lit),
            IRExpr::Apply { fn_id, args } | IRExpr::PartialApply { fn_id, args, .. } => {
                let f = self.translate_fn_id(fn_id);
                args.iter()
                    .map(|a| self.translate_arg(a))
                    .fold(f, Expr::app)
            }
            IRExpr::ClosureApply { closure, args } => {
                let cl = self.translate_arg(closure);
                args.iter()
                    .map(|a| self.translate_arg(a))
                    .fold(cl, Expr::app)
            }
            IRExpr::UProj { idx, var } => Expr::app(
                Expr::const_str(&format!("_uproj{idx}")),
                self.var_expr(*var),
            ),
            IRExpr::SProj { n, offset, var, .. } => Expr::app(
                Expr::const_str(&format!("_sproj{n}_{offset}")),
                self.var_expr(*var),
            ),
            IRExpr::IsShared(var) => Expr::app(Expr::const_str("_isShared"), self.var_expr(*var)),
            IRExpr::String(s) => Expr::str_lit(s),
            IRExpr::Reset(var) => Expr::app(Expr::const_str("_reset"), self.var_expr(*var)),
            IRExpr::Reuse { var, ctor, args } => {
                let cn = self.recover_ctor_name(ctor);
                let base = Expr::app(
                    Expr::const_str("_reuse"),
                    Expr::app(self.var_expr(*var), Expr::const_(cn, Vec::<Level>::new())),
                );
                args.iter()
                    .map(|a| self.translate_arg(a))
                    .fold(base, Expr::app)
            }
        }
    }

    fn translate_fn_id(&mut self, fn_id: &FnId) -> Expr {
        let key = fn_id.0.to_string();
        if let Some(n) = self.registry.fn_name(&key) {
            self.stats.names_recovered += 1;
            Expr::const_(n.clone(), Vec::<Level>::new())
        } else {
            Expr::const_(fn_id.0.clone(), Vec::<Level>::new())
        }
    }

    // ----- IRBody reconstruction -----

    pub(crate) fn translate_body(&mut self, body: &IRBody) -> Expr {
        self.stats.terms_reconstructed += 1;
        match body {
            IRBody::VDecl {
                var,
                ty,
                value,
                rest,
            } => {
                let name = self.registry.var_name(*var);
                Expr::let_named(
                    name,
                    self.translate_type(ty),
                    self.translate_expr(value),
                    self.translate_body(rest),
                    false,
                )
            }
            IRBody::JDecl { body: jb, rest, .. } => {
                self.stats.partial_reconstructions += 1;
                let jb = self.translate_body(jb);
                let rest = self.translate_body(rest);
                Expr::let_named(
                    Name::from_string("_jp"),
                    Expr::const_str("_JoinPoint"),
                    jb,
                    rest,
                    false,
                )
            }
            IRBody::Inc { rest, .. }
            | IRBody::Dec { rest, .. }
            | IRBody::Set { rest, .. }
            | IRBody::SetTag { rest, .. }
            | IRBody::USet { rest, .. }
            | IRBody::SSet { rest, .. } => self.translate_body(rest),
            IRBody::Case {
                scrutinee,
                alts,
                default,
            } => self.translate_case(*scrutinee, alts, default.as_deref()),
            IRBody::Jmp { jp, args } => {
                self.stats.partial_reconstructions += 1;
                let base = Expr::const_(
                    Name::from_string(&format!("_jp{}", jp.0)),
                    Vec::<Level>::new(),
                );
                args.iter()
                    .map(|a| self.translate_arg(a))
                    .fold(base, Expr::app)
            }
            IRBody::Ret(arg) => self.translate_arg(arg),
            IRBody::Unreachable => {
                self.stats.partial_reconstructions += 1;
                Expr::const_str("_unreachable")
            }
        }
    }

    fn translate_case(&mut self, scrut: VarId, alts: &[IRAlt], default: Option<&IRBody>) -> Expr {
        let se = self.var_expr(scrut);
        let mut result = default.map_or_else(
            || Expr::const_str("_no_default"),
            |d| self.translate_body(d),
        );
        for alt in alts.iter().rev() {
            let cn = self.recover_ctor_name(&alt.ctor);
            let ab = self.translate_body(&alt.body);
            result = Expr::apps(
                Expr::const_str("_match"),
                [
                    se.clone(),
                    Expr::const_(cn, Vec::<Level>::new()),
                    ab,
                    result,
                ],
            );
        }
        result
    }

    // ----- Function signature reconstruction -----

    pub(crate) fn translate_decl_signature(&mut self, decl: &IRDecl) -> Expr {
        let ret = self.translate_type(&decl.return_type);
        decl.params.iter().rev().fold(ret, |body, (_var, ty)| {
            let ty_expr = self.translate_type(ty);
            self.stats.terms_reconstructed += 1;
            Expr::pi(BinderInfo::Default, ty_expr, body)
        })
    }

    pub(crate) fn translate_decl(&mut self, decl: &IRDecl) -> Expr {
        for (var, _ty) in &decl.params {
            if !self.registry.var_names.contains_key(var) {
                self.registry
                    .register_var(*var, Name::from_string(&format!("_a{}", var.0)));
            }
        }
        let sig = self.translate_decl_signature(decl);
        let body_expr = self.translate_body(&decl.body);
        Expr::let_named(
            decl.name.clone(),
            sig,
            body_expr,
            Expr::const_str("_decl_end"),
            true,
        )
    }
}

// ---------------------------------------------------------------------------
// Pretty-printing
// ---------------------------------------------------------------------------

/// Pretty-print a reconstructed `Expr` in human-readable Lean-like notation.
#[must_use]
pub(crate) fn pretty_print(expr: &Expr) -> String {
    let mut buf = String::with_capacity(256);
    pp_expr(expr, &mut buf, 0);
    buf
}

fn pp_expr(expr: &Expr, buf: &mut String, depth: usize) {
    if depth > 200 {
        buf.push_str("...");
        return;
    }
    match expr.kind() {
        ExprKind::Const(name, _) => buf.push_str(&name.to_string()),
        ExprKind::Lit(lit) => match lit {
            clean_kernel::Literal::Nat(n) => buf.push_str(&n.to_string()),
            clean_kernel::Literal::String(s) => {
                buf.push('"');
                buf.push_str(s);
                buf.push('"');
            }
        },
        ExprKind::App(f, a) => {
            buf.push('(');
            pp_expr(f, buf, depth + 1);
            buf.push(' ');
            pp_expr(a, buf, depth + 1);
            buf.push(')');
        }
        ExprKind::Let(name, ty, val, body, _) => {
            buf.push_str("let ");
            buf.push_str(&name.to_string());
            buf.push_str(" : ");
            pp_expr(ty, buf, depth + 1);
            buf.push_str(" := ");
            pp_expr(val, buf, depth + 1);
            buf.push_str("; ");
            pp_expr(body, buf, depth + 1);
        }
        ExprKind::Pi(_, ty, body) => {
            buf.push_str("(_ : ");
            pp_expr(ty, buf, depth + 1);
            buf.push_str(") -> ");
            pp_expr(body, buf, depth + 1);
        }
        ExprKind::Lam(_, ty, body) => {
            buf.push_str("fun (_ : ");
            pp_expr(ty, buf, depth + 1);
            buf.push_str(") => ");
            pp_expr(body, buf, depth + 1);
        }
        ExprKind::Proj(_, idx, e) => {
            pp_expr(e, buf, depth + 1);
            buf.push('.');
            buf.push_str(&idx.to_string());
        }
        ExprKind::BVar(idx) => {
            buf.push('#');
            buf.push_str(&idx.to_string());
        }
        _ => buf.push_str("<expr>"),
    }
}

// ---------------------------------------------------------------------------
// Round-trip validation
// ---------------------------------------------------------------------------

/// Result of a round-trip comparison.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum RoundTripResult {
    ExactMatch,
    PartialMatch { reason: String },
    Mismatch { expected: String, actual: String },
}

/// Compare two `Expr`s for structural similarity, tolerating erased placeholders.
#[must_use]
pub(crate) fn round_trip_compare(original: &Expr, reconstructed: &Expr) -> RoundTripResult {
    cmp_inner(original, reconstructed, 0)
}

fn is_placeholder(expr: &Expr) -> bool {
    if let ExprKind::Const(name, _) = expr.kind() {
        let s = name.to_string();
        s.starts_with("_erased") || s.starts_with("_float") || s.starts_with("_unreachable")
    } else {
        false
    }
}

fn cmp_inner(a: &Expr, b: &Expr, d: usize) -> RoundTripResult {
    if d > 200 {
        return RoundTripResult::PartialMatch {
            reason: "depth limit".into(),
        };
    }
    if is_placeholder(b) {
        return RoundTripResult::PartialMatch {
            reason: format!("placeholder: {}", pretty_print(b)),
        };
    }
    match (a.kind(), b.kind()) {
        (ExprKind::Const(n1, _), ExprKind::Const(n2, _)) if n1 == n2 => RoundTripResult::ExactMatch,
        (ExprKind::Lit(l1), ExprKind::Lit(l2)) if l1 == l2 => RoundTripResult::ExactMatch,
        (ExprKind::BVar(i), ExprKind::BVar(j)) if i == j => RoundTripResult::ExactMatch,
        (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
            merge_rr(cmp_inner(f1, f2, d + 1), cmp_inner(a1, a2, d + 1))
        }
        (ExprKind::Let(n1, t1, v1, b1, _), ExprKind::Let(n2, t2, v2, b2, _)) => {
            let c = merge_rr(
                merge_rr(cmp_inner(t1, t2, d + 1), cmp_inner(v1, v2, d + 1)),
                cmp_inner(b1, b2, d + 1),
            );
            if n1 != n2 {
                merge_rr(
                    c,
                    RoundTripResult::PartialMatch {
                        reason: format!("name: {n1} vs {n2}"),
                    },
                )
            } else {
                c
            }
        }
        (ExprKind::Pi(_, t1, b1), ExprKind::Pi(_, t2, b2))
        | (ExprKind::Lam(_, t1, b1), ExprKind::Lam(_, t2, b2)) => {
            merge_rr(cmp_inner(t1, t2, d + 1), cmp_inner(b1, b2, d + 1))
        }
        _ => RoundTripResult::Mismatch {
            expected: pretty_print(a),
            actual: pretty_print(b),
        },
    }
}

fn merge_rr(a: RoundTripResult, b: RoundTripResult) -> RoundTripResult {
    match (&a, &b) {
        (RoundTripResult::ExactMatch, RoundTripResult::ExactMatch) => RoundTripResult::ExactMatch,
        (RoundTripResult::Mismatch { .. }, _) => a,
        (_, RoundTripResult::Mismatch { .. }) => b,
        (RoundTripResult::PartialMatch { reason }, _) => RoundTripResult::PartialMatch {
            reason: reason.clone(),
        },
        (_, RoundTripResult::PartialMatch { reason }) => RoundTripResult::PartialMatch {
            reason: reason.clone(),
        },
    }
}
