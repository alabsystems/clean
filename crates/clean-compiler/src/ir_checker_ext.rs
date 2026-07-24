// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended IR validation and checking for L5IR.
//!
//! Extends the base `ir_checker` with deeper semantic checks:
//! - **E1**: Type consistency (expressions well-typed in IR)
//! - **E2**: Variable scope validation (VarIds in scope when used)
//! - **E3**: Function signature validation (call args match declared params)
//! - **E4**: Control flow graph validation (all paths terminate)
//! - **E5**: Reference counting balance (inc/dec pairing analysis)
//! - **E6**: Closure environment validation (captured vars exist)
//! - **E7**: Dead code detection (unreachable declarations)
//! - **E8**: IR invariant checking (case completeness, duplicate tags)
//!
//! Part of #3083 - Extensibility.

use crate::ir::{IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, VarId};
use clean_kernel::Name;
use std::collections::{HashMap, HashSet};

/// Severity of a diagnostic finding.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Severity {
    Info,
    Warning,
    Error,
}

/// Location in the IR for diagnostic reporting.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DiagLocation {
    pub(crate) function: Name,
    pub(crate) context: String,
}

/// A single diagnostic finding from extended IR checking.
#[derive(Debug, Clone)]
pub(crate) struct Diagnostic {
    pub(crate) severity: Severity,
    pub(crate) location: DiagLocation,
    pub(crate) message: String,
}

/// Configuration for the extended IR checker.
#[derive(Debug, Clone)]
pub(crate) struct ExtCheckerConfig {
    pub(crate) check_types: bool,
    pub(crate) check_scopes: bool,
    pub(crate) check_signatures: bool,
    pub(crate) check_control_flow: bool,
    pub(crate) check_rc_balance: bool,
    pub(crate) check_closures: bool,
    pub(crate) check_dead_code: bool,
    pub(crate) check_case_invariants: bool,
}

impl Default for ExtCheckerConfig {
    fn default() -> Self {
        Self {
            check_types: true,
            check_scopes: true,
            check_signatures: true,
            check_control_flow: true,
            check_rc_balance: true,
            check_closures: true,
            check_dead_code: true,
            check_case_invariants: true,
        }
    }
}

/// Result of extended IR checking.
#[derive(Debug, Clone, Default)]
pub(crate) struct ExtCheckerResult {
    pub(crate) diagnostics: Vec<Diagnostic>,
}

impl ExtCheckerResult {
    pub(crate) fn has_errors(&self) -> bool {
        self.diagnostics
            .iter()
            .any(|d| d.severity == Severity::Error)
    }

    pub(crate) fn has_warnings(&self) -> bool {
        self.diagnostics
            .iter()
            .any(|d| d.severity >= Severity::Warning)
    }

    pub(crate) fn count(&self, severity: Severity) -> usize {
        self.diagnostics
            .iter()
            .filter(|d| d.severity == severity)
            .count()
    }
}

/// Helper: get the continuation (`rest`) and optional variables from an IRBody node.
/// Returns None for terminal nodes (Ret, Unreachable, Jmp, Case).
fn body_rest(body: &IRBody) -> Option<&IRBody> {
    match body {
        IRBody::VDecl { rest, .. }
        | IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => Some(rest),
        _ => None,
    }
}

/// Extended IR checker.
struct ExtChecker<'a> {
    config: &'a ExtCheckerConfig,
    decls: &'a [IRDecl],
    decl_index: HashMap<&'a Name, usize>,
    diagnostics: Vec<Diagnostic>,
}

impl<'a> ExtChecker<'a> {
    fn new(decls: &'a [IRDecl], config: &'a ExtCheckerConfig) -> Self {
        let decl_index = decls
            .iter()
            .enumerate()
            .map(|(i, d)| (&d.name, i))
            .collect();
        Self {
            config,
            decls,
            decl_index,
            diagnostics: Vec::new(),
        }
    }

    fn emit(&mut self, severity: Severity, function: &Name, context: &str, message: String) {
        self.diagnostics.push(Diagnostic {
            severity,
            location: DiagLocation {
                function: function.clone(),
                context: context.to_string(),
            },
            message,
        });
    }

    fn get_decl(&self, name: &Name) -> Option<&'a IRDecl> {
        self.decl_index.get(name).map(|&i| &self.decls[i])
    }

    // ── E1: Type consistency ──────────────────────────────────────────
    fn check_type_consistency_expr(&mut self, expr: &IRExpr, ty: &IRType, f: &Name) {
        match expr {
            IRExpr::Lit(lit) => {
                let ok = matches!(
                    (lit, ty),
                    (IRLiteral::Bool(_), IRType::Bool)
                        | (IRLiteral::UInt8(_), IRType::UInt8)
                        | (IRLiteral::UInt16(_), IRType::UInt16)
                        | (IRLiteral::UInt32(_), IRType::UInt32)
                        | (IRLiteral::UInt64(_), IRType::UInt64)
                        | (IRLiteral::USize(_), IRType::USize)
                        | (IRLiteral::Float32(_), IRType::Float32)
                        | (IRLiteral::Float64(_), IRType::Float64)
                );
                if !ok {
                    self.emit(
                        Severity::Error,
                        f,
                        "literal type",
                        format!("literal {lit:?} does not match declared type {ty:?}"),
                    );
                }
            }
            IRExpr::Box { ty: box_ty, .. } if !box_ty.is_scalar() => {
                self.emit(
                    Severity::Error,
                    f,
                    "box",
                    format!("Box expects scalar type, got {box_ty:?}"),
                );
            }
            IRExpr::Unbox { ty: unbox_ty, .. } if !unbox_ty.is_scalar() => {
                self.emit(
                    Severity::Error,
                    f,
                    "unbox",
                    format!("Unbox expects scalar result type, got {unbox_ty:?}"),
                );
            }
            IRExpr::Ctor { .. } | IRExpr::Reuse { .. }
                if !ty.is_object() && *ty != IRType::Erased =>
            {
                self.emit(
                    Severity::Error,
                    f,
                    "ctor result",
                    format!("constructor result bound to non-object type {ty:?}"),
                );
            }
            IRExpr::String(_) if !ty.is_object() => {
                self.emit(
                    Severity::Error,
                    f,
                    "string literal",
                    format!("string literal bound to non-object type {ty:?}"),
                );
            }
            _ => {}
        }
    }

    // ── E2: Variable scope ────────────────────────────────────────────
    fn check_var_scope(&mut self, scope: &HashSet<u32>, v: VarId, f: &Name, ctx: &str) {
        if !scope.contains(&v.0) {
            self.emit(
                Severity::Error,
                f,
                ctx,
                format!("variable x{} used out of scope", v.0),
            );
        }
    }

    fn check_arg_scope(&mut self, scope: &HashSet<u32>, arg: &IRArg, f: &Name, ctx: &str) {
        if let IRArg::Var(v) = arg {
            self.check_var_scope(scope, *v, f, ctx);
        }
    }

    fn check_args_scope(&mut self, scope: &HashSet<u32>, args: &[IRArg], f: &Name, ctx: &str) {
        for arg in args {
            self.check_arg_scope(scope, arg, f, ctx);
        }
    }

    fn check_expr_scope(&mut self, scope: &HashSet<u32>, expr: &IRExpr, f: &Name) {
        match expr {
            IRExpr::Ctor { args, .. } | IRExpr::Apply { args, .. } => {
                self.check_args_scope(scope, args, f, "expr")
            }
            IRExpr::PartialApply { args, .. } => {
                self.check_args_scope(scope, args, f, "partial_apply")
            }
            IRExpr::Proj { arg, .. }
            | IRExpr::Tag(arg)
            | IRExpr::Box { arg, .. }
            | IRExpr::Unbox { arg, .. } => self.check_arg_scope(scope, arg, f, "expr"),
            IRExpr::ClosureApply { closure, args } => {
                self.check_arg_scope(scope, closure, f, "closure_apply");
                self.check_args_scope(scope, args, f, "closure_apply");
            }
            IRExpr::UProj { var, .. }
            | IRExpr::SProj { var, .. }
            | IRExpr::IsShared(var)
            | IRExpr::Reset(var) => self.check_var_scope(scope, *var, f, "expr"),
            IRExpr::Reuse { var, args, .. } => {
                self.check_var_scope(scope, *var, f, "reuse");
                self.check_args_scope(scope, args, f, "reuse");
            }
            IRExpr::Lit(_) | IRExpr::String(_) => {}
        }
    }

    // ── E3: Function signature validation ─────────────────────────────
    fn check_signatures_in_expr(&mut self, expr: &IRExpr, f: &Name) {
        match expr {
            IRExpr::Apply { fn_id, args } => {
                if let Some(tgt) = self.get_decl(&fn_id.0) {
                    if args.len() != tgt.params.len() {
                        self.emit(
                            Severity::Error,
                            f,
                            "apply",
                            format!(
                                "call to {} with {} args, expected {}",
                                fn_id.0,
                                args.len(),
                                tgt.params.len()
                            ),
                        );
                    }
                }
            }
            IRExpr::PartialApply { fn_id, arity, args } => {
                if let Some(tgt) = self.get_decl(&fn_id.0) {
                    if *arity as usize != tgt.params.len() {
                        self.emit(
                            Severity::Error,
                            f,
                            "partial_apply",
                            format!(
                                "partial apply to {} with arity {}, function has {} params",
                                fn_id.0,
                                arity,
                                tgt.params.len()
                            ),
                        );
                    }
                }
                if args.len() >= *arity as usize {
                    self.emit(
                        Severity::Error,
                        f,
                        "partial_apply",
                        format!(
                            "partial apply captures {} args but arity is {}",
                            args.len(),
                            arity
                        ),
                    );
                }
            }
            _ => {}
        }
    }

    // ── E4: Control flow termination ──────────────────────────────────
    fn body_terminates(&self, body: &IRBody) -> bool {
        match body {
            IRBody::Ret(_) | IRBody::Unreachable | IRBody::Jmp { .. } => true,
            IRBody::JDecl { body: jp, rest, .. } => {
                self.body_terminates(jp) && self.body_terminates(rest)
            }
            IRBody::Case { alts, default, .. } => {
                alts.iter().all(|a| self.body_terminates(&a.body))
                    && default.as_ref().is_none_or(|d| self.body_terminates(d))
            }
            _ => body_rest(body).is_some_and(|r| self.body_terminates(r)),
        }
    }

    // ── E5: RC balance checking ───────────────────────────────────────
    fn collect_rc_ops(&self, body: &IRBody, bal: &mut HashMap<u32, i64>) {
        match body {
            IRBody::Inc { var, n, rest } => {
                *bal.entry(var.0).or_insert(0) += *n as i64;
                self.collect_rc_ops(rest, bal);
            }
            IRBody::Dec { var, rest } => {
                *bal.entry(var.0).or_insert(0) -= 1;
                self.collect_rc_ops(rest, bal);
            }
            IRBody::JDecl { body: jp, rest, .. } => {
                self.collect_rc_ops(jp, bal);
                self.collect_rc_ops(rest, bal);
            }
            IRBody::Case { alts, default, .. } => {
                for a in alts {
                    self.collect_rc_ops(&a.body, bal);
                }
                if let Some(d) = default {
                    self.collect_rc_ops(d, bal);
                }
            }
            _ => {
                if let Some(r) = body_rest(body) {
                    self.collect_rc_ops(r, bal);
                }
            }
        }
    }

    fn check_rc_balance(&mut self, decl: &IRDecl) {
        let mut bal: HashMap<u32, i64> = HashMap::new();
        self.collect_rc_ops(&decl.body, &mut bal);
        for (&vid, &net) in &bal {
            if net < -1 {
                self.emit(
                    Severity::Warning,
                    &decl.name,
                    "rc_balance",
                    format!("variable x{vid} has RC balance {net} (potential double-free)"),
                );
            }
        }
    }

    // ── E6: Closure environment validation ────────────────────────────
    fn check_closure_env(&mut self, scope: &HashSet<u32>, expr: &IRExpr, f: &Name) {
        if let IRExpr::PartialApply { args, .. } = expr {
            for arg in args {
                if let IRArg::Var(v) = arg {
                    if !scope.contains(&v.0) {
                        self.emit(
                            Severity::Error,
                            f,
                            "closure_env",
                            format!("captured variable x{} not in enclosing scope", v.0),
                        );
                    }
                }
            }
        }
    }

    // ── E7: Dead code detection ───────────────────────────────────────
    fn collect_called(body: &IRBody, called: &mut HashSet<Name>) {
        match body {
            IRBody::VDecl { value, rest, .. } => {
                if let IRExpr::Apply { fn_id, .. } | IRExpr::PartialApply { fn_id, .. } = value {
                    called.insert(fn_id.0.clone());
                }
                Self::collect_called(rest, called);
            }
            IRBody::JDecl { body: jp, rest, .. } => {
                Self::collect_called(jp, called);
                Self::collect_called(rest, called);
            }
            IRBody::Case { alts, default, .. } => {
                for a in alts {
                    Self::collect_called(&a.body, called);
                }
                if let Some(d) = default {
                    Self::collect_called(d, called);
                }
            }
            _ => {
                if let Some(r) = body_rest(body) {
                    Self::collect_called(r, called);
                }
            }
        }
    }

    fn check_dead_code(&mut self) {
        if self.decls.is_empty() {
            return;
        }
        let mut called: HashSet<Name> = HashSet::new();
        for d in self.decls {
            Self::collect_called(&d.body, &mut called);
        }
        let mut roots: HashSet<Name> = HashSet::from([self.decls[0].name.clone()]);
        roots.insert(Name::from_string("main"));
        for d in self.decls {
            if !called.contains(&d.name) && !roots.contains(&d.name) {
                self.emit(
                    Severity::Info,
                    &d.name,
                    "dead_code",
                    format!("function {} is never called", d.name),
                );
            }
        }
    }

    // ── E8: Case completeness ─────────────────────────────────────────
    fn check_cases(&mut self, body: &IRBody, f: &Name) {
        match body {
            IRBody::Case { alts, default, .. } => {
                if alts.is_empty() && default.is_none() {
                    self.emit(
                        Severity::Error,
                        f,
                        "case",
                        "case expression has no alternatives and no default".into(),
                    );
                }
                let mut seen: HashSet<u32> = HashSet::new();
                for a in alts {
                    if !seen.insert(a.ctor.tag) {
                        self.emit(
                            Severity::Error,
                            f,
                            "case",
                            format!("duplicate constructor tag {} in case", a.ctor.tag),
                        );
                    }
                    self.check_cases(&a.body, f);
                }
                if let Some(d) = default {
                    self.check_cases(d, f);
                }
            }
            IRBody::JDecl { body: jp, rest, .. } => {
                self.check_cases(jp, f);
                self.check_cases(rest, f);
            }
            _ => {
                if let Some(r) = body_rest(body) {
                    self.check_cases(r, f);
                }
            }
        }
    }

    // ── Per-declaration walk ──────────────────────────────────────────
    fn walk_body(&mut self, body: &IRBody, scope: &mut HashSet<u32>, f: &Name) {
        match body {
            IRBody::VDecl {
                var,
                ty,
                value,
                rest,
            } => {
                if self.config.check_scopes {
                    self.check_expr_scope(scope, value, f);
                }
                if self.config.check_types {
                    self.check_type_consistency_expr(value, ty, f);
                }
                if self.config.check_signatures {
                    self.check_signatures_in_expr(value, f);
                }
                if self.config.check_closures {
                    self.check_closure_env(scope, value, f);
                }
                scope.insert(var.0);
                self.walk_body(rest, scope, f);
            }
            IRBody::JDecl {
                params,
                body: jp,
                rest,
                ..
            } => {
                let mut jp_scope = scope.clone();
                for (v, _) in params {
                    jp_scope.insert(v.0);
                }
                self.walk_body(jp, &mut jp_scope, f);
                self.walk_body(rest, scope, f);
            }
            IRBody::Inc { var, rest, .. } | IRBody::Dec { var, rest } => {
                if self.config.check_scopes {
                    self.check_var_scope(scope, *var, f, "rc_op");
                }
                self.walk_body(rest, scope, f);
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
                if self.config.check_scopes {
                    self.check_var_scope(scope, *var, f, "mutation");
                    self.check_var_scope(scope, *value, f, "mutation_value");
                }
                self.walk_body(rest, scope, f);
            }
            IRBody::SetTag { var, rest, .. } => {
                if self.config.check_scopes {
                    self.check_var_scope(scope, *var, f, "set_tag");
                }
                self.walk_body(rest, scope, f);
            }
            IRBody::Case {
                scrutinee,
                alts,
                default,
            } => {
                if self.config.check_scopes {
                    self.check_var_scope(scope, *scrutinee, f, "case");
                }
                for a in alts {
                    self.walk_body(&a.body, &mut scope.clone(), f);
                }
                if let Some(d) = default {
                    self.walk_body(d, &mut scope.clone(), f);
                }
            }
            IRBody::Jmp { args, .. } => {
                if self.config.check_scopes {
                    self.check_args_scope(scope, args, f, "jmp");
                }
            }
            IRBody::Ret(arg) => {
                if self.config.check_scopes {
                    self.check_arg_scope(scope, arg, f, "ret");
                }
            }
            IRBody::Unreachable => {}
        }
    }

    fn check_decl(&mut self, decl: &IRDecl) {
        let mut scope: HashSet<u32> = decl.params.iter().map(|(v, _)| v.0).collect();
        self.walk_body(&decl.body, &mut scope, &decl.name);
        if self.config.check_control_flow && !self.body_terminates(&decl.body) {
            self.emit(
                Severity::Error,
                &decl.name,
                "control_flow",
                "function body does not terminate on all paths".into(),
            );
        }
        if self.config.check_rc_balance {
            self.check_rc_balance(decl);
        }
        if self.config.check_case_invariants {
            self.check_cases(&decl.body, &decl.name);
        }
    }

    fn run(&mut self) {
        for d in self.decls {
            self.check_decl(d);
        }
        if self.config.check_dead_code {
            self.check_dead_code();
        }
    }
}

/// Run extended IR checking on a set of declarations.
pub(crate) fn check_decls_ext(decls: &[IRDecl], config: &ExtCheckerConfig) -> ExtCheckerResult {
    let mut checker = ExtChecker::new(decls, config);
    checker.run();
    ExtCheckerResult {
        diagnostics: checker.diagnostics,
    }
}

/// Run extended IR checking with default configuration.
pub(crate) fn check_decls_ext_default(decls: &[IRDecl]) -> ExtCheckerResult {
    check_decls_ext(decls, &ExtCheckerConfig::default())
}
