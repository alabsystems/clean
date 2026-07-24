// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean 4 parity test — compares clean type inference against Lean 4 baseline.
//!
//! Renamed from `differential.rs` to avoid collision with `differential_equations`
//! topology tests when running `cargo test -- differential`. (Part of #1567)
//!
//! Run: `cargo test --test lean4_parity`
//! Regen baseline: `REGEN_BASELINE=1 cargo test --test lean4_parity -- lean4_parity_check`

use anyhow::{anyhow, Result};
use clean_elab::ElabCtx;
use clean_kernel::differential_baseline::{load_expressions, load_lean4_types, normalize_type_str};
use clean_kernel::expr::{BinderInfo, Expr, ExprKind};
use clean_kernel::level::Level;
use clean_kernel::Environment;
use clean_parser::parse_expr;
use std::path::Path;

#[derive(serde::Serialize)]
struct ParitySummary {
    total_expressions: usize,
    matched: usize,
    mismatched: usize,
    errors: usize,
    agreement_rate: f64,
    commit: String,
    timestamp: String,
}

#[test]
fn lean4_parity_check() -> Result<()> {
    let expressions = load_expressions()?;
    let lean4_types = load_lean4_types(&expressions)?;

    if lean4_types.len() != expressions.len() {
        return Err(anyhow!(
            "Lean4 produced {} results for {} expressions",
            lean4_types.len(),
            expressions.len()
        ));
    }

    let mut matched = 0usize;
    let mut mismatches = Vec::new();
    let mut errors = Vec::new();

    for (idx, (expr, l4)) in expressions.iter().zip(lean4_types.iter()).enumerate() {
        match infer_single(expr) {
            Ok(l5) => {
                if &l5 == l4 {
                    matched += 1;
                } else {
                    mismatches.push((idx, expr.clone(), l4.clone(), l5));
                }
            }
            Err(e) => errors.push((idx, expr.clone(), format!("{e:#}"))),
        }
    }

    let total = expressions.len();
    let rate = if total > 0 {
        matched as f64 / total as f64
    } else {
        0.0
    };
    write_parity_summary(total, matched, mismatches.len(), errors.len(), rate);
    eprintln!(
        "Lean4 parity: {matched}/{total} ({:.1}%), {} mismatches, {} errors",
        rate * 100.0,
        mismatches.len(),
        errors.len()
    );

    if mismatches.is_empty() && errors.is_empty() {
        return Ok(());
    }
    Err(anyhow!(format_parity_failures(
        matched,
        total,
        rate,
        &mismatches,
        &errors
    )))
}

fn format_parity_failures(
    matched: usize,
    total: usize,
    rate: f64,
    mismatches: &[(usize, String, String, String)],
    errors: &[(usize, String, String)],
) -> String {
    let mut msg = format!(
        "Lean4 parity: {matched}/{total} ({:.1}%) — {} mismatches, {} errors\n",
        rate * 100.0,
        mismatches.len(),
        errors.len()
    );
    for (idx, expr, l4, l5) in mismatches.iter().take(10) {
        msg.push_str(&format!(
            "  MISMATCH #{idx}: `{expr}`\n    lean4: {l4}\n    clean: {l5}\n"
        ));
    }
    if mismatches.len() > 10 {
        msg.push_str(&format!(
            "  ... and {} more mismatches\n",
            mismatches.len() - 10
        ));
    }
    for (idx, expr, err) in errors.iter().take(5) {
        msg.push_str(&format!("  ERROR #{idx}: `{expr}`\n    {err}\n"));
    }
    if errors.len() > 5 {
        msg.push_str(&format!("  ... and {} more errors\n", errors.len() - 5));
    }
    msg
}

fn write_parity_summary(
    total: usize,
    matched: usize,
    mismatched: usize,
    errors: usize,
    agreement_rate: f64,
) {
    let commit = std::process::Command::new("git")
        .args(["rev-parse", "--short", "HEAD"])
        .output()
        .ok()
        .and_then(|o| {
            o.status
                .success()
                .then(|| String::from_utf8_lossy(&o.stdout).trim().to_string())
        })
        .unwrap_or_else(|| "unknown".to_string());

    let timestamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| format!("unix:{}", d.as_secs()))
        .unwrap_or_else(|_| "unknown".to_string());

    let summary = ParitySummary {
        total_expressions: total,
        matched,
        mismatched,
        errors,
        agreement_rate,
        commit,
        timestamp,
    };

    let metrics_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../metrics");
    if std::fs::create_dir_all(&metrics_dir).is_err() {
        return;
    }
    let path = metrics_dir.join("lean4_parity.json");
    if let Ok(json) = serde_json::to_string_pretty(&summary) {
        let _ = std::fs::write(&path, json);
        eprintln!("Parity summary written to {}", path.display());
    }
}

fn infer_single(expr_str: &str) -> Result<String> {
    let surface = parse_expr(expr_str)?;
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);
    let kernel_expr = ctx.elaborate(&surface)?;
    let tc = clean_kernel::TypeChecker::new(&env);
    let ty = tc.infer_type(&kernel_expr)?;
    Ok(normalize_type_str(&format_expr(&ty)))
}

fn level_as_nat(level: &Level) -> Option<u32> {
    match level {
        Level::Zero => Some(0),
        Level::Succ(inner) => level_as_nat(inner).map(|n| n + 1),
        _ => None,
    }
}

fn format_level(level: &Level) -> String {
    level_as_nat(level).map_or_else(|| level.to_string(), |n| n.to_string())
}

fn format_sort(level: &Level) -> String {
    match level_as_nat(level) {
        Some(0) => "Prop".to_string(),
        Some(1) => "Type".to_string(),
        Some(n) => format!("Type {}", n - 1),
        None => format!("Sort {}", format_level(level)),
    }
}

fn uses_param(expr: &Expr, d: u32) -> bool {
    match expr.kind() {
        ExprKind::BVar(idx) => *idx == d,
        ExprKind::FVar(_) | ExprKind::Sort(_) | ExprKind::Const(_, _) | ExprKind::Lit(_) => false,
        ExprKind::App(f, a) => uses_param(f, d) || uses_param(a, d),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            uses_param(ty, d) || uses_param(body, d + 1)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            uses_param(ty, d) || uses_param(val, d) || uses_param(body, d + 1)
        }
        ExprKind::Proj(_, _, e) | ExprKind::MData(_, e) | ExprKind::Squash(e) => uses_param(e, d),
        ExprKind::CubicalPathLam { body } => uses_param(body, d + 1),
        ExprKind::CubicalPath { ty, left, right } => {
            uses_param(ty, d) || uses_param(left, d) || uses_param(right, d)
        }
        ExprKind::CubicalPathApp { path, arg }
        | ExprKind::ZFCMem {
            element: path,
            set: arg,
        } => uses_param(path, d) || uses_param(arg, d),
        ExprKind::CubicalHComp { ty, phi, u, base } => {
            uses_param(ty, d) || uses_param(phi, d) || uses_param(u, d) || uses_param(base, d)
        }
        ExprKind::CubicalTransp { ty, phi, base } => {
            uses_param(ty, d) || uses_param(phi, d) || uses_param(base, d)
        }
        ExprKind::CubicalCoe { ty, r, s, base } => {
            uses_param(ty, d) || uses_param(r, d) || uses_param(s, d) || uses_param(base, d)
        }
        ExprKind::ZFCComprehension { domain, pred } => {
            uses_param(domain, d) || uses_param(pred, d + 1)
        }
        ExprKind::CubicalInterval
        | ExprKind::CubicalI0
        | ExprKind::CubicalI1
        | ExprKind::ZFCSet(_)
        | ExprKind::SProp => false,
    }
}

fn format_expr(expr: &Expr) -> String {
    format_expr_ctx(expr, 0, &[])
}

fn binder_name_for_type(ty: &Expr, used: &[String]) -> String {
    let base: String = match ty.kind() {
        ExprKind::Sort(level) => match level_as_nat(level) {
            Some(0) => "P".to_string(),
            Some(1) => "A".to_string(),
            _ => "u".to_string(),
        },
        ExprKind::Const(name, _) => {
            let s = name.to_string();
            s.chars()
                .next()
                .filter(|c| c.is_alphabetic())
                .map_or("x".to_string(), |c| c.to_string())
        }
        ExprKind::Pi(_, _, _) => "f".to_string(),
        _ => "x".to_string(),
    };
    let base = base.to_lowercase();
    if !used.contains(&base) {
        return base;
    }
    (1..100)
        .map(|i| format!("{base}{i}"))
        .find(|name| !used.contains(name))
        .unwrap_or_else(|| format!("{}_{}", base, used.len()))
}

fn wrap_prec(s: String, prec: u8, threshold: u8) -> String {
    if prec > threshold {
        format!("({s})")
    } else {
        s
    }
}

fn format_binder_body(dom: &Expr, body: &Expr, prec: u8, binders: &[String]) -> String {
    let name = binder_name_for_type(dom, binders);
    let dom_str = format_expr_ctx(dom, 0, binders);
    let mut new_binders = binders.to_vec();
    new_binders.push(name.clone());
    let body_str = format_expr_ctx(body, 0, &new_binders);
    wrap_prec(format!("({name} : {dom_str}) -> {body_str}"), prec, 0)
}

fn format_expr_ctx(expr: &Expr, prec: u8, binders: &[String]) -> String {
    match expr.kind() {
        ExprKind::Sort(level) => format_sort(level),
        ExprKind::Const(name, levels) if levels.is_empty() => name.to_string(),
        ExprKind::Const(name, levels) => {
            let lvls: Vec<String> = levels.iter().map(format_level).collect();
            format!("{} {{{}}}", name, lvls.join(", "))
        }
        ExprKind::Pi(bi, dom, body)
            if *bi == BinderInfo::Default.into() && !uses_param(body, 0) =>
        {
            let left = format_expr_ctx(dom, 1, binders);
            let mut nb = binders.to_vec();
            nb.push("_".to_string());
            wrap_prec(
                format!("{left} -> {}", format_expr_ctx(body, 0, &nb)),
                prec,
                0,
            )
        }
        ExprKind::Pi(_, dom, body) => format_binder_body(dom, body, prec, binders),
        ExprKind::Lam(_, ty, body) => {
            let name = binder_name_for_type(ty, binders);
            let ty_str = format_expr_ctx(ty, 0, binders);
            let mut nb = binders.to_vec();
            nb.push(name.clone());
            wrap_prec(
                format!(
                    "fun ({name} : {ty_str}) => {}",
                    format_expr_ctx(body, 0, &nb)
                ),
                prec,
                1,
            )
        }
        ExprKind::App(f, a) => wrap_prec(
            format!(
                "{} {}",
                format_expr_ctx(f, 2, binders),
                format_expr_ctx(a, 3, binders)
            ),
            prec,
            2,
        ),
        ExprKind::Let(_, ty, val, body, _) => {
            let name = binder_name_for_type(ty, binders);
            let mut nb = binders.to_vec();
            nb.push(name.clone());
            format!(
                "let ({name} : {}) := {} in {}",
                format_expr_ctx(ty, 0, binders),
                format_expr_ctx(val, 0, binders),
                format_expr_ctx(body, 0, &nb)
            )
        }
        ExprKind::Lit(lit) => format!("{lit:?}"),
        ExprKind::Proj(name, idx, e) => format!("{name}.{idx}.{}", format_expr_ctx(e, 3, binders)),
        ExprKind::FVar(id) => format!("fvar#{id:?}"),
        ExprKind::BVar(idx) => {
            let i = *idx as usize;
            if i < binders.len() {
                binders[binders.len() - 1 - i].clone()
            } else {
                format!("bvar#{i}")
            }
        }
        ExprKind::MData(_, inner) => format!("@[mdata] {}", format_expr_ctx(inner, prec, binders)),
        _ => format_expr_ext(expr, prec, binders),
    }
}

fn format_expr_ext(expr: &Expr, _prec: u8, binders: &[String]) -> String {
    match expr.kind() {
        ExprKind::CubicalInterval => "\u{1d540}".to_string(),
        ExprKind::CubicalI0 => "i0".to_string(),
        ExprKind::CubicalI1 => "i1".to_string(),
        ExprKind::CubicalPath { ty, left, right } => format!(
            "Path {} {} {}",
            format_expr_ctx(ty, 3, binders),
            format_expr_ctx(left, 3, binders),
            format_expr_ctx(right, 3, binders)
        ),
        ExprKind::CubicalPathLam { body } => {
            let mut nb = binders.to_vec();
            nb.push("i".to_string());
            format!(
                "pathLam (i : \u{1d540}) => {}",
                format_expr_ctx(body, 0, &nb)
            )
        }
        ExprKind::CubicalPathApp { path, arg } => format!(
            "{} @ {}",
            format_expr_ctx(path, 2, binders),
            format_expr_ctx(arg, 3, binders)
        ),
        ExprKind::CubicalHComp { ty, phi, u, base } => format!(
            "hcomp {} {} {} {}",
            format_expr_ctx(ty, 3, binders),
            format_expr_ctx(phi, 3, binders),
            format_expr_ctx(u, 3, binders),
            format_expr_ctx(base, 3, binders)
        ),
        ExprKind::CubicalTransp { ty, phi, base } => format!(
            "transp {} {} {}",
            format_expr_ctx(ty, 3, binders),
            format_expr_ctx(phi, 3, binders),
            format_expr_ctx(base, 3, binders)
        ),
        ExprKind::ZFCSet(s) => format!("{s:?}"),
        ExprKind::ZFCMem { element, set } => format!(
            "{} \u{2208} {}",
            format_expr_ctx(element, 3, binders),
            format_expr_ctx(set, 3, binders)
        ),
        ExprKind::ZFCComprehension { domain, pred } => {
            let mut nb = binders.to_vec();
            nb.push("x".to_string());
            format!(
                "{{ x \u{2208} {} | {} }}",
                format_expr_ctx(domain, 0, binders),
                format_expr_ctx(pred, 0, &nb)
            )
        }
        ExprKind::SProp => "SProp".to_string(),
        ExprKind::Squash(inner) => {
            format!("\u{2308}{}\u{2309}", format_expr_ctx(inner, 0, binders))
        }
        _ => format!("{expr:?}"),
    }
}
