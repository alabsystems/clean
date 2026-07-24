// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pretty-printing for Expr.
//!
//! Contains Display impl and all display helper functions.

use super::*;
use crate::level::Level;

// ── Display (pretty-printing) ───────────────────────────────────────────────

fn display_level_as_nat(level: &Level) -> Option<u32> {
    // Iterative with checked_add: total on all inputs. The previous recursive
    // `.map(|n| n + 1)` carried a panicking add (Trust ledger 2026-06-10,
    // assertion: arithmetic overflow (Add) @ expr/display.rs:17) and was not
    // stack-safe on deep Succ chains.
    let mut n: u32 = 0;
    let mut current = level;
    loop {
        match current {
            Level::Zero => return Some(n),
            Level::Succ(inner) => {
                n = n.checked_add(1)?;
                current = inner;
            }
            _ => return None,
        }
    }
}

fn display_level(level: &Level) -> String {
    if let Some(n) = display_level_as_nat(level) {
        return n.to_string();
    }
    level.to_string()
}

fn display_sort(level: &Level) -> String {
    match display_level_as_nat(level) {
        Some(0) => "Prop".to_string(),
        Some(1) => "Type".to_string(),
        Some(n) => format!("Type {}", n - 1),
        None => format!("Sort {}", display_level(level)),
    }
}

/// Check whether the expression uses the bound variable at `param_depth`.
/// Stack-safe to prevent overflow on deeply nested expressions.
fn display_uses_param(kind: &ExprKind, param_depth: u32) -> bool {
    stack_safe(|| display_uses_param_impl(kind, param_depth))
}

fn display_uses_param_impl(kind: &ExprKind, param_depth: u32) -> bool {
    match kind {
        ExprKind::BVar(idx) => *idx == param_depth,
        ExprKind::FVar(_) | ExprKind::Sort(_) | ExprKind::Const(_, _) | ExprKind::Lit(_) => false,
        ExprKind::App(f, a) => {
            display_uses_param(&f.kind, param_depth) || display_uses_param(&a.kind, param_depth)
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            display_uses_param(&ty.kind, param_depth)
                || display_uses_param(&body.kind, param_depth + 1)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            display_uses_param(&ty.kind, param_depth)
                || display_uses_param(&val.kind, param_depth)
                || display_uses_param(&body.kind, param_depth + 1)
        }
        ExprKind::Proj(_, _, e) => display_uses_param(&e.kind, param_depth),
        ExprKind::MData(_, inner) => display_uses_param(&inner.kind, param_depth),
        ExprKind::CubicalInterval | ExprKind::CubicalI0 | ExprKind::CubicalI1 => false,
        ExprKind::CubicalPath { ty, left, right } => {
            display_uses_param(&ty.kind, param_depth)
                || display_uses_param(&left.kind, param_depth)
                || display_uses_param(&right.kind, param_depth)
        }
        ExprKind::CubicalPathLam { body } => display_uses_param(&body.kind, param_depth + 1),
        ExprKind::CubicalPathApp { path, arg } => {
            display_uses_param(&path.kind, param_depth)
                || display_uses_param(&arg.kind, param_depth)
        }
        ExprKind::CubicalHComp { ty, phi, u, base } => {
            display_uses_param(&ty.kind, param_depth)
                || display_uses_param(&phi.kind, param_depth)
                || display_uses_param(&u.kind, param_depth)
                || display_uses_param(&base.kind, param_depth)
        }
        ExprKind::CubicalTransp { ty, phi, base } => {
            display_uses_param(&ty.kind, param_depth)
                || display_uses_param(&phi.kind, param_depth)
                || display_uses_param(&base.kind, param_depth)
        }
        ExprKind::CubicalCoe { ty, r, s, base } => {
            display_uses_param(&ty.kind, param_depth)
                || display_uses_param(&r.kind, param_depth)
                || display_uses_param(&s.kind, param_depth)
                || display_uses_param(&base.kind, param_depth)
        }
        ExprKind::ZFCSet(_) => false,
        ExprKind::ZFCMem { element, set } => {
            display_uses_param(&element.kind, param_depth)
                || display_uses_param(&set.kind, param_depth)
        }
        ExprKind::ZFCComprehension { domain, pred } => {
            display_uses_param(&domain.kind, param_depth)
                || display_uses_param(&pred.kind, param_depth + 1)
        }
        ExprKind::SProp => false,
        ExprKind::Squash(inner) => display_uses_param(&inner.kind, param_depth),
    }
}

/// Generate a binder name based on the domain type.
fn display_binder_name(kind: &ExprKind, used: &[String]) -> String {
    let base: String = match kind {
        ExprKind::Sort(level) => match display_level_as_nat(level) {
            Some(0) => "P".to_string(),
            Some(1) => "A".to_string(),
            _ => "u".to_string(),
        },
        ExprKind::Const(name, _) => {
            let s = name.to_string();
            if let Some(c) = s.chars().next() {
                if c.is_alphabetic() {
                    c.to_string()
                } else {
                    "x".to_string()
                }
            } else {
                "x".to_string()
            }
        }
        ExprKind::Pi(_, _, _) => "f".to_string(),
        _ => "x".to_string(),
    };
    let base = base.to_lowercase();
    if !used.contains(&base) {
        return base;
    }
    for i in 1..100 {
        let name = format!("{base}{i}");
        if !used.contains(&name) {
            return name;
        }
    }
    format!("{}_{}", base, used.len())
}

/// Helper: format an ExprKind to a String (used for recursive sub-expressions).
/// Stack-safe to prevent overflow on deeply nested expressions during Display.
fn display_expr_to_string(kind: &ExprKind, prec: u8, binders: &[String]) -> String {
    stack_safe(|| display_expr_to_string_impl(kind, prec, binders))
}

fn display_expr_to_string_impl(kind: &ExprKind, prec: u8, binders: &[String]) -> String {
    struct Helper<'a> {
        kind: &'a ExprKind,
        prec: u8,
        binders: &'a [String],
    }
    impl<'a> std::fmt::Display for Helper<'a> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            display_expr_ctx(self.kind, self.prec, self.binders, f)
        }
    }
    Helper {
        kind,
        prec,
        binders,
    }
    .to_string()
}

/// Stack-safe wrapper for display_expr_ctx_impl.
/// Prevents stack overflow on deeply nested expressions during Display::fmt.
fn display_expr_ctx(
    kind: &ExprKind,
    prec: u8,
    binders: &[String],
    f: &mut std::fmt::Formatter<'_>,
) -> std::fmt::Result {
    stack_safe(|| display_expr_ctx_impl(kind, prec, binders, f))
}

fn display_expr_ctx_impl(
    kind: &ExprKind,
    prec: u8,
    binders: &[String],
    f: &mut std::fmt::Formatter<'_>,
) -> std::fmt::Result {
    match kind {
        ExprKind::Sort(level) => write!(f, "{}", display_sort(level)),
        ExprKind::Const(name, levels) => {
            if levels.is_empty() {
                write!(f, "{name}")
            } else {
                let lvl_strs: Vec<String> = levels.iter().map(display_level).collect();
                write!(f, "{name} {{{}}}", lvl_strs.join(", "))
            }
        }
        ExprKind::Pi(bd, dom, body)
            if bd.info == BinderInfo::Default && !display_uses_param(&body.kind, 0) =>
        {
            let left = display_expr_to_string(&dom.kind, 1, binders);
            let mut new_binders = binders.to_vec();
            new_binders.push("_".to_string());
            let right = display_expr_to_string(&body.kind, 0, &new_binders);
            if prec > 0 {
                write!(f, "({left} -> {right})")
            } else {
                write!(f, "{left} -> {right}")
            }
        }
        ExprKind::Pi(_, dom, body) => {
            let name = display_binder_name(&dom.kind, binders);
            let dom_str = display_expr_to_string(&dom.kind, 0, binders);
            let mut new_binders = binders.to_vec();
            new_binders.push(name.clone());
            let body_str = display_expr_to_string(&body.kind, 0, &new_binders);
            if prec > 0 {
                write!(f, "(({name} : {dom_str}) -> {body_str})")
            } else {
                write!(f, "({name} : {dom_str}) -> {body_str}")
            }
        }
        ExprKind::Lam(_, ty, body) => {
            let name = display_binder_name(&ty.kind, binders);
            let ty_str = display_expr_to_string(&ty.kind, 0, binders);
            let mut new_binders = binders.to_vec();
            new_binders.push(name.clone());
            let body_str = display_expr_to_string(&body.kind, 0, &new_binders);
            if prec > 1 {
                write!(f, "(fun ({name} : {ty_str}) => {body_str})")
            } else {
                write!(f, "fun ({name} : {ty_str}) => {body_str}")
            }
        }
        ExprKind::App(func, arg) => {
            let func_str = display_expr_to_string(&func.kind, 2, binders);
            let arg_str = display_expr_to_string(&arg.kind, 3, binders);
            if prec > 2 {
                write!(f, "({func_str} {arg_str})")
            } else {
                write!(f, "{func_str} {arg_str}")
            }
        }
        ExprKind::Let(_, ty, val, body, _) => {
            let name = display_binder_name(&ty.kind, binders);
            let ty_str = display_expr_to_string(&ty.kind, 0, binders);
            let val_str = display_expr_to_string(&val.kind, 0, binders);
            let mut new_binders = binders.to_vec();
            new_binders.push(name.clone());
            let body_str = display_expr_to_string(&body.kind, 0, &new_binders);
            write!(f, "let ({name} : {ty_str}) := {val_str} in {body_str}")
        }
        ExprKind::Lit(lit) => write!(f, "{lit:?}"),
        ExprKind::Proj(name, idx, e) => {
            let e_str = display_expr_to_string(&e.kind, 3, binders);
            write!(f, "{name}.{idx}.{e_str}")
        }
        ExprKind::FVar(id) => write!(f, "fvar#{id:?}"),
        ExprKind::BVar(idx) => {
            let idx = *idx as usize;
            if idx < binders.len() {
                write!(f, "{}", binders[binders.len() - 1 - idx])
            } else {
                write!(f, "bvar#{idx}")
            }
        }
        ExprKind::MData(_, inner) => {
            write!(f, "@[mdata] ")?;
            display_expr_ctx(&inner.kind, prec, binders, f)
        }
        ExprKind::CubicalInterval => write!(f, "\u{1d540}"),
        ExprKind::CubicalI0 => write!(f, "i0"),
        ExprKind::CubicalI1 => write!(f, "i1"),
        ExprKind::CubicalPath { ty, left, right } => {
            let ty_s = display_expr_to_string(&ty.kind, 3, binders);
            let l_s = display_expr_to_string(&left.kind, 3, binders);
            let r_s = display_expr_to_string(&right.kind, 3, binders);
            write!(f, "Path {ty_s} {l_s} {r_s}")
        }
        ExprKind::CubicalPathLam { body } => {
            let name = "i".to_string();
            let mut new_binders = binders.to_vec();
            new_binders.push(name.clone());
            let body_str = display_expr_to_string(&body.kind, 0, &new_binders);
            write!(f, "pathLam ({name} : \u{1d540}) => {body_str}")
        }
        ExprKind::CubicalPathApp { path, arg } => {
            let p_s = display_expr_to_string(&path.kind, 2, binders);
            let a_s = display_expr_to_string(&arg.kind, 3, binders);
            write!(f, "{p_s} @ {a_s}")
        }
        ExprKind::CubicalHComp { ty, phi, u, base } => {
            let ty_s = display_expr_to_string(&ty.kind, 3, binders);
            let phi_s = display_expr_to_string(&phi.kind, 3, binders);
            let u_s = display_expr_to_string(&u.kind, 3, binders);
            let b_s = display_expr_to_string(&base.kind, 3, binders);
            write!(f, "hcomp {ty_s} {phi_s} {u_s} {b_s}")
        }
        ExprKind::CubicalTransp { ty, phi, base } => {
            let ty_s = display_expr_to_string(&ty.kind, 3, binders);
            let phi_s = display_expr_to_string(&phi.kind, 3, binders);
            let b_s = display_expr_to_string(&base.kind, 3, binders);
            write!(f, "transp {ty_s} {phi_s} {b_s}")
        }
        ExprKind::CubicalCoe { ty, r, s, base } => {
            let ty_s = display_expr_to_string(&ty.kind, 3, binders);
            let r_s = display_expr_to_string(&r.kind, 3, binders);
            let s_s = display_expr_to_string(&s.kind, 3, binders);
            let b_s = display_expr_to_string(&base.kind, 3, binders);
            write!(f, "coe {ty_s} {r_s} {s_s} {b_s}")
        }
        ExprKind::ZFCSet(set_expr) => write!(f, "{set_expr:?}"),
        ExprKind::ZFCMem { element, set } => {
            let el_s = display_expr_to_string(&element.kind, 3, binders);
            let s_s = display_expr_to_string(&set.kind, 3, binders);
            write!(f, "{el_s} \u{2208} {s_s}")
        }
        ExprKind::ZFCComprehension { domain, pred } => {
            let name = "x".to_string();
            let mut new_binders = binders.to_vec();
            new_binders.push(name.clone());
            let dom_s = display_expr_to_string(&domain.kind, 0, binders);
            let pred_s = display_expr_to_string(&pred.kind, 0, &new_binders);
            write!(f, "{{ {name} \u{2208} {dom_s} | {pred_s} }}")
        }
        ExprKind::SProp => write!(f, "SProp"),
        ExprKind::Squash(inner) => {
            let inner_s = display_expr_to_string(&inner.kind, 0, binders);
            write!(f, "\u{2308}{inner_s}\u{2309}")
        }
    }
}

impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        display_expr_ctx(&self.kind, 0, &[], f)
    }
}
