// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Name-mention checking for L5CNF code.
//!
//! Used for recursion detection: checks if an LCNF code tree references
//! a given constant name.
//!
//! Uses `CodeVisitor` trait for structural recursion. Override methods add
//! name-checking at each Code variant; the trait handles recursive descent.

use super::lower::is_erasable;
#[cfg(test)]
use crate::lcnf::{Alt, Param};
use crate::lcnf::{Arg, Cases, Code, FunDecl, LetDecl, LetValue};
use crate::CodeVisitor;
#[cfg(test)]
use clean_kernel::inductive::mentions_name as expr_mentions_name;
use clean_kernel::{Environment, Expr, ExprKind, FVarId, Name};
use std::collections::HashSet;

/// Check if an LCNF code tree references a given constant name.
#[cfg(test)]
pub(crate) fn code_mentions_name(code: &Code, target: &Name) -> bool {
    NameMentionChecker { target }.visit_code(code)
}

/// Collect runtime-relevant constant names from an LCNF code tree.
///
/// This intentionally ignores type annotations, constructor names, and other
/// metadata-only references. Lean 4's `Decl.recursive` bit is driven by
/// executable references inside a declaration block, not by type mentions.
pub(crate) fn code_called_constant_names(code: &Code) -> HashSet<Name> {
    let mut collector = CallNameCollector::default();
    collector.visit_code(code);
    collector.names
}

/// Collect runtime-relevant constant names from a kernel expression.
///
/// This includes direct application heads and non-erased arguments, since
/// higher-order constants may flow through arguments and later participate in a
/// recursive SCC after lowering. Binder types and erased arguments are skipped
/// so recursion detection follows value-flow edges rather than metadata
/// dependencies.
pub(crate) fn expr_called_constant_names(env: &Environment, expr: &Expr) -> HashSet<Name> {
    let mut names = HashSet::new();
    collect_expr_call_names(env, expr, &mut names);
    names
}

#[cfg(test)]
struct NameMentionChecker<'a> {
    target: &'a Name,
}

#[derive(Default)]
struct CallNameCollector {
    names: HashSet<Name>,
}

#[cfg(test)]
impl CodeVisitor for NameMentionChecker<'_> {
    type Result = bool;

    fn combine(&self, a: bool, b: bool) -> bool {
        a || b
    }

    fn visit_let(&mut self, decl: &LetDecl, body: &Code) -> bool {
        expr_mentions_name(&decl.ty, self.target)
            || let_value_mentions_name(&decl.value, self.target)
            || self.visit_code(body)
    }

    fn visit_fun(&mut self, decl: &FunDecl, body: &Code) -> bool {
        params_mentions_name(&decl.params, self.target)
            || expr_mentions_name(&decl.ty, self.target)
            || self.visit_code(&decl.body)
            || self.visit_code(body)
    }

    fn visit_join_point(&mut self, decl: &FunDecl, body: &Code) -> bool {
        params_mentions_name(&decl.params, self.target)
            || expr_mentions_name(&decl.ty, self.target)
            || self.visit_code(&decl.body)
            || self.visit_code(body)
    }

    fn visit_cases(&mut self, cases: &Cases) -> bool {
        expr_mentions_name(&cases.result_type, self.target)
            || cases.alts.iter().any(|alt| alt_mentions_name(alt, self))
    }

    fn visit_jmp(&mut self, _jp: FVarId, args: &[Arg]) -> bool {
        args_mentions_name(args, self.target)
    }

    // visit_return uses default (false) — Return nodes contain no names.

    fn visit_unreachable(&mut self, ty: &Expr) -> bool {
        expr_mentions_name(ty, self.target)
    }
}

impl CodeVisitor for CallNameCollector {
    type Result = ();

    fn combine(&self, (): (), (): ()) {}

    fn visit_let(&mut self, decl: &LetDecl, body: &Code) {
        if let LetValue::Const { name, .. } = &decl.value {
            self.names.insert(name.clone());
        }
        self.visit_code(body);
    }

    fn visit_fun(&mut self, decl: &FunDecl, body: &Code) {
        self.visit_code(&decl.body);
        self.visit_code(body);
    }

    fn visit_join_point(&mut self, decl: &FunDecl, body: &Code) {
        self.visit_code(&decl.body);
        self.visit_code(body);
    }

    fn visit_cases(&mut self, cases: &Cases) {
        for alt in &cases.alts {
            self.visit_code(alt.body());
        }
    }

    fn visit_jmp(&mut self, _jp: FVarId, _args: &[Arg]) {}

    fn visit_unreachable(&mut self, _ty: &Expr) {}
}

#[cfg(test)]
fn alt_mentions_name(alt: &Alt, checker: &mut NameMentionChecker<'_>) -> bool {
    match alt {
        Alt::Ctor {
            ctor_name,
            params,
            body,
        } => {
            ctor_name == checker.target
                || params_mentions_name(params, checker.target)
                || checker.visit_code(body)
        }
        Alt::Default(body) => checker.visit_code(body),
    }
}

#[cfg(test)]
fn let_value_mentions_name(value: &LetValue, target: &Name) -> bool {
    match value {
        LetValue::Const { name, args, .. } => name == target || args_mentions_name(args, target),
        LetValue::Ctor { name, args, .. } => name == target || args_mentions_name(args, target),
        LetValue::Proj { type_name, .. } => type_name == target,
        LetValue::FVar { args, .. } => args_mentions_name(args, target),
        LetValue::Reuse {
            ctor_name, args, ..
        } => ctor_name == target || args_mentions_name(args, target),
        LetValue::Lit(_) | LetValue::Erased => false,
    }
}

#[cfg(test)]
fn params_mentions_name(params: &[Param], target: &Name) -> bool {
    params
        .iter()
        .any(|param| expr_mentions_name(&param.ty, target))
}

#[cfg(test)]
fn args_mentions_name(args: &[Arg], target: &Name) -> bool {
    args.iter().any(|arg| match arg {
        Arg::Type(expr) => expr_mentions_name(expr, target),
        Arg::Erased | Arg::FVar(_) | Arg::Index(_) => false,
    })
}

fn collect_expr_call_names(env: &Environment, expr: &Expr, names: &mut HashSet<Name>) {
    match expr.kind() {
        ExprKind::Const(name, _) => {
            names.insert(name.clone());
        }
        ExprKind::App(_, _) => collect_app_call_names(env, expr, names),
        ExprKind::Lam(_, _, body) => collect_expr_call_names(env, body, names),
        ExprKind::Let(_, _, value, body, _) => {
            collect_expr_call_names(env, value, names);
            collect_expr_call_names(env, body, names);
        }
        ExprKind::Proj(_, _, inner)
        | ExprKind::MData(_, inner)
        | ExprKind::Squash(inner)
        | ExprKind::CubicalPathLam { body: inner } => collect_expr_call_names(env, inner, names),
        ExprKind::CubicalPath { left, right, .. } => {
            collect_expr_call_names(env, left, names);
            collect_expr_call_names(env, right, names);
        }
        ExprKind::CubicalPathApp { path, arg } => {
            collect_expr_call_names(env, path, names);
            collect_non_erased_arg_call_names(env, arg, names);
        }
        ExprKind::CubicalHComp { u, base, .. } => {
            collect_expr_call_names(env, u, names);
            collect_expr_call_names(env, base, names);
        }
        ExprKind::CubicalTransp { base, .. } => collect_expr_call_names(env, base, names),
        ExprKind::CubicalCoe { base, .. } => collect_expr_call_names(env, base, names),
        ExprKind::ZFCMem { element, set } => {
            collect_expr_call_names(env, element, names);
            collect_expr_call_names(env, set, names);
        }
        ExprKind::ZFCComprehension { domain, pred } => {
            collect_expr_call_names(env, domain, names);
            collect_expr_call_names(env, pred, names);
        }
        ExprKind::BVar(_)
        | ExprKind::FVar(_)
        | ExprKind::Sort(_)
        | ExprKind::Pi(_, _, _)
        | ExprKind::Lit(_)
        | ExprKind::SProp
        | ExprKind::CubicalInterval
        | ExprKind::CubicalI0
        | ExprKind::CubicalI1
        | ExprKind::ZFCSet(_) => {}
    }
}

fn collect_app_call_names(env: &Environment, expr: &Expr, names: &mut HashSet<Name>) {
    let head = expr.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        names.insert(name.clone());
    } else {
        collect_expr_call_names(env, head, names);
    }

    for arg in expr.get_app_args() {
        collect_non_erased_arg_call_names(env, arg, names);
    }
}

fn collect_non_erased_arg_call_names(env: &Environment, expr: &Expr, names: &mut HashSet<Name>) {
    if !is_erasable(env, expr) {
        collect_expr_call_names(env, expr, names);
    }
}
