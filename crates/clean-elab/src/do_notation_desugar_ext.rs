// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended analysis and optimization for kernel-level do-notation desugaring.
//!
//! Provides static analysis over `DoStmt` sequences: statement classification,
//! complexity metrics, dependency analysis, optimization hints, monad detection,
//! bind chain analysis, and desugar preview — all without mutating state.

use crate::do_notation_desugar::{desugar_do_block, DoDesugarConfig, DoStmt};
use clean_kernel::Name;
use std::collections::{HashMap, HashSet};

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// Errors specific to do-notation analysis and preview.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub(crate) enum DoDesugarExtError {
    #[error("empty do-block: nothing to analyze")]
    EmptyBlock,
    #[error("statement index {0} out of range (block has {1} statements)")]
    IndexOutOfRange(usize, usize),
    #[error("desugar preview failed: {0}")]
    PreviewFailed(String),
}

impl From<DoDesugarExtError> for crate::ElabError {
    fn from(err: DoDesugarExtError) -> Self {
        crate::ElabError::NotImplemented(err.to_string())
    }
}

// ---------------------------------------------------------------------------
// Statement classification
// ---------------------------------------------------------------------------

/// Classification tag for a single `DoStmt`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum StmtKind {
    Bind,
    LetBind,
    LetMut,
    Assign,
    Action,
    Return,
    If,
    For,
    TryCatch,
    Unless,
    Repeat,
}

/// Classify a single statement.
#[must_use]
pub(crate) fn classify_stmt(stmt: &DoStmt) -> StmtKind {
    match stmt {
        DoStmt::Bind { .. } => StmtKind::Bind,
        DoStmt::Let { .. } => StmtKind::LetBind,
        DoStmt::LetMut { .. } => StmtKind::LetMut,
        DoStmt::Assign { .. } => StmtKind::Assign,
        DoStmt::Action(_) => StmtKind::Action,
        DoStmt::Return(_) => StmtKind::Return,
        DoStmt::If { .. } => StmtKind::If,
        DoStmt::For { .. } => StmtKind::For,
        DoStmt::TryCatch { .. } => StmtKind::TryCatch,
        DoStmt::Unless { .. } => StmtKind::Unless,
        DoStmt::Repeat { .. } => StmtKind::Repeat,
    }
}

/// Classify every statement in a block.
#[must_use]
pub(crate) fn classify_block(stmts: &[DoStmt]) -> Vec<StmtKind> {
    stmts.iter().map(classify_stmt).collect()
}

// ---------------------------------------------------------------------------
// Complexity metrics
// ---------------------------------------------------------------------------

/// Complexity metrics for a do-block.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DoBlockMetrics {
    pub(crate) statement_count: usize,
    pub(crate) max_nesting_depth: usize,
    pub(crate) bind_count: usize,
    pub(crate) let_count: usize,
    pub(crate) mut_var_count: usize,
    pub(crate) has_control_flow: bool,
}

/// Compute complexity metrics for a do-block.
#[must_use]
pub(crate) fn compute_metrics(stmts: &[DoStmt]) -> DoBlockMetrics {
    let (mut bind_count, mut let_count, mut mut_var_count, mut has_cf) = (0, 0, 0, false);
    for (i, stmt) in stmts.iter().enumerate() {
        let terminal = i == stmts.len() - 1;
        match stmt {
            DoStmt::Bind { .. } | DoStmt::Action(_) if !terminal => bind_count += 1,
            DoStmt::Let { .. } => let_count += 1,
            DoStmt::LetMut { .. } => {
                let_count += 1;
                mut_var_count += 1;
            }
            DoStmt::If { .. }
            | DoStmt::For { .. }
            | DoStmt::TryCatch { .. }
            | DoStmt::Unless { .. }
            | DoStmt::Repeat { .. } => {
                has_cf = true;
                if !terminal {
                    bind_count += 1;
                }
            }
            _ => {}
        }
    }
    DoBlockMetrics {
        statement_count: stmts.len(),
        max_nesting_depth: max_depth(stmts, 0),
        bind_count,
        let_count,
        mut_var_count,
        has_control_flow: has_cf,
    }
}

fn max_depth(stmts: &[DoStmt], cur: usize) -> usize {
    stmts.iter().fold(cur, |deepest, stmt| {
        deepest.max(match stmt {
            DoStmt::If { then_, else_, .. } => {
                max_depth(then_, cur + 1).max(max_depth(else_, cur + 1))
            }
            DoStmt::For { body, .. }
            | DoStmt::Unless { body, .. }
            | DoStmt::Repeat { body, .. } => max_depth(body, cur + 1),
            DoStmt::TryCatch {
                try_body,
                catch_body,
                ..
            } => max_depth(try_body, cur + 1).max(max_depth(catch_body, cur + 1)),
            _ => cur,
        })
    })
}

// ---------------------------------------------------------------------------
// Dependency analysis
// ---------------------------------------------------------------------------

/// Per-statement dependency info: which earlier indices each statement depends on.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DependencyInfo {
    pub(crate) deps: Vec<HashSet<usize>>,
    pub(crate) defs: Vec<Option<Name>>,
}

/// Compute inter-statement data-flow dependencies (conservative over-approximation).
#[must_use]
pub(crate) fn compute_dependencies(stmts: &[DoStmt]) -> DependencyInfo {
    let defs: Vec<Option<Name>> = stmts
        .iter()
        .map(|s| match s {
            DoStmt::Bind { pat, .. } => Some(pat.clone()),
            DoStmt::Let { name, .. }
            | DoStmt::LetMut { name, .. }
            | DoStmt::Assign { name, .. } => Some(name.clone()),
            _ => None,
        })
        .collect();

    let mut name_to_idx: HashMap<Name, usize> = HashMap::new();
    let mut deps = Vec::with_capacity(stmts.len());

    for (i, def) in defs.iter().enumerate() {
        let mut my_deps = HashSet::new();
        // Sub-block statements conservatively depend on all prior definitions.
        if has_sub_blocks(&stmts[i]) {
            my_deps.extend(name_to_idx.values().copied());
        }
        // Monadic sequential dependency (pure let-to-let chains are independent).
        if i > 0 {
            let prev = classify_stmt(&stmts[i - 1]);
            let cur = classify_stmt(&stmts[i]);
            let both_let = matches!(
                (prev, cur),
                (
                    StmtKind::LetBind | StmtKind::LetMut,
                    StmtKind::LetBind | StmtKind::LetMut
                )
            );
            if !both_let && matches!(cur, StmtKind::Bind | StmtKind::Action | StmtKind::Return) {
                my_deps.insert(i - 1);
            }
        }
        deps.push(my_deps);
        if let Some(ref n) = def {
            name_to_idx.insert(n.clone(), i);
        }
    }
    DependencyInfo { deps, defs }
}

fn has_sub_blocks(stmt: &DoStmt) -> bool {
    matches!(
        stmt,
        DoStmt::If { .. }
            | DoStmt::For { .. }
            | DoStmt::TryCatch { .. }
            | DoStmt::Unless { .. }
            | DoStmt::Repeat { .. }
    )
}

/// Group consecutive statements with no inter-dependencies (Applicative candidates).
#[must_use]
pub(crate) fn find_independent_stmts(dep_info: &DependencyInfo) -> Vec<Vec<usize>> {
    let n = dep_info.deps.len();
    if n == 0 {
        return vec![];
    }
    let mut groups: Vec<Vec<usize>> = Vec::new();
    let mut grp: Vec<usize> = vec![0];
    for i in 1..n {
        if dep_info.deps[i].iter().any(|d| grp.contains(d)) {
            groups.push(std::mem::take(&mut grp));
        }
        grp.push(i);
    }
    if !grp.is_empty() {
        groups.push(grp);
    }
    groups
}

// ---------------------------------------------------------------------------
// Optimization hints
// ---------------------------------------------------------------------------

/// A suggested optimization for a do-block.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum OptimizationHint {
    /// `x <- action; return x` can be replaced with just `action`.
    PureBindFusion { bind_index: usize },
    /// Discarded bind (`_ <- pure_expr`) is unnecessary.
    // Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
    // keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
    #[allow(dead_code)]
    UnnecessaryBind { action_index: usize },
    /// Consecutive independent `let` bindings could be reordered / Applicative-lifted.
    IndependentLetBindings { indices: Vec<usize> },
    /// Single-statement block that needs no monadic machinery.
    CouldBeExpression,
    /// `x <- action; return (f x)` can use `Functor.map` instead.
    CouldUseFunctor,
}

/// Analyze a do-block and produce optimization hints.
#[must_use]
pub(crate) fn suggest_optimizations(stmts: &[DoStmt]) -> Vec<OptimizationHint> {
    let mut hints = Vec::new();
    if stmts.is_empty() {
        return hints;
    }

    // Pure-bind fusion: `x <- action; return x`.
    for i in 0..stmts.len().saturating_sub(1) {
        if let DoStmt::Bind { pat, .. } = &stmts[i] {
            if let Some(DoStmt::Return(Some(ret_expr))) = stmts.get(i + 1) {
                if is_name_reference(ret_expr, pat) {
                    hints.push(OptimizationHint::PureBindFusion { bind_index: i });
                }
            }
        }
    }
    // Could-be-expression (no binds, single statement).
    let metrics = compute_metrics(stmts);
    if metrics.bind_count == 0
        && metrics.statement_count == 1
        && matches!(&stmts[0], DoStmt::Action(_) | DoStmt::Return(_))
    {
        hints.push(OptimizationHint::CouldBeExpression);
    }
    // Could-use-functor: single bind + return (when not already fused).
    if stmts.len() == 2 {
        if let DoStmt::Bind { .. } = &stmts[0] {
            if matches!(&stmts[1], DoStmt::Return(Some(_))) {
                let fused = hints
                    .iter()
                    .any(|h| matches!(h, OptimizationHint::PureBindFusion { bind_index: 0 }));
                if !fused {
                    hints.push(OptimizationHint::CouldUseFunctor);
                }
            }
        }
    }
    // Independent let bindings.
    let dep_info = compute_dependencies(stmts);
    let mut let_run: Vec<usize> = Vec::new();
    for (i, stmt) in stmts.iter().enumerate() {
        if matches!(classify_stmt(stmt), StmtKind::LetBind | StmtKind::LetMut) {
            let_run.push(i);
        } else {
            flush_independent_lets(&let_run, &dep_info, &mut hints);
            let_run.clear();
        }
    }
    flush_independent_lets(&let_run, &dep_info, &mut hints);
    hints
}

fn flush_independent_lets(
    run: &[usize],
    dep_info: &DependencyInfo,
    hints: &mut Vec<OptimizationHint>,
) {
    if run.len() < 2 {
        return;
    }
    let run_set: HashSet<usize> = run.iter().copied().collect();
    let all_ind = run
        .iter()
        .all(|&idx| dep_info.deps[idx].intersection(&run_set).next().is_none());
    if all_ind {
        hints.push(OptimizationHint::IndependentLetBindings {
            indices: run.to_vec(),
        });
    }
}

fn is_name_reference(expr: &clean_kernel::Expr, name: &Name) -> bool {
    matches!(expr.kind(), clean_kernel::ExprKind::Const(n, _) if n == name)
}

// ---------------------------------------------------------------------------
// Monad operation detection
// ---------------------------------------------------------------------------

/// Which monad/functor operations a do-block actually requires.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct MonadUsage {
    pub(crate) uses_bind: bool,
    pub(crate) uses_pure: bool,
    pub(crate) uses_except: bool,
    pub(crate) uses_for_in: bool,
    pub(crate) uses_state: bool,
    pub(crate) minimum_class: &'static str,
}

/// Detect which monad operations a do-block requires.
#[must_use]
pub(crate) fn detect_monad_usage(stmts: &[DoStmt]) -> MonadUsage {
    let (mut b, mut p, mut e, mut f, mut s) = (false, false, false, false, false);
    scan_usage(stmts, &mut b, &mut p, &mut e, &mut f, &mut s);
    let minimum_class = if s {
        "MonadState"
    } else if e {
        "MonadExcept"
    } else if b || f {
        "Monad"
    } else if p {
        "Applicative"
    } else {
        "Functor"
    };
    MonadUsage {
        uses_bind: b,
        uses_pure: p,
        uses_except: e,
        uses_for_in: f,
        uses_state: s,
        minimum_class,
    }
}

fn scan_usage(
    stmts: &[DoStmt],
    b: &mut bool,
    p: &mut bool,
    e: &mut bool,
    fi: &mut bool,
    s: &mut bool,
) {
    for (i, stmt) in stmts.iter().enumerate() {
        let term = i == stmts.len() - 1;
        match stmt {
            DoStmt::Bind { .. } if !term => *b = true,
            DoStmt::Action(_) if term => *p = true,
            DoStmt::Action(_) => *b = true,
            DoStmt::Return(_) => *p = true,
            DoStmt::LetMut { .. } | DoStmt::Assign { .. } => *s = true,
            DoStmt::If { then_, else_, .. } => {
                if !term {
                    *b = true;
                }
                scan_usage(then_, b, p, e, fi, s);
                scan_usage(else_, b, p, e, fi, s);
            }
            DoStmt::For { body, .. } => {
                *fi = true;
                if !term {
                    *b = true;
                }
                scan_usage(body, b, p, e, fi, s);
            }
            DoStmt::TryCatch {
                try_body,
                catch_body,
                ..
            } => {
                *e = true;
                if !term {
                    *b = true;
                }
                scan_usage(try_body, b, p, e, fi, s);
                scan_usage(catch_body, b, p, e, fi, s);
            }
            DoStmt::Unless { body, .. } => {
                *p = true;
                if !term {
                    *b = true;
                }
                scan_usage(body, b, p, e, fi, s);
            }
            DoStmt::Repeat { body, .. } => {
                *fi = true;
                if !term {
                    *b = true;
                }
                scan_usage(body, b, p, e, fi, s);
            }
            _ => {}
        }
    }
}

// ---------------------------------------------------------------------------
// Desugar preview
// ---------------------------------------------------------------------------

/// Result of a desugar preview.
#[derive(Debug, Clone)]
pub(crate) struct DesugarPreview {
    pub(crate) preview_text: String,
    pub(crate) bind_count: usize,
    pub(crate) mut_vars: Vec<Name>,
    pub(crate) metrics: DoBlockMetrics,
    pub(crate) minimum_class: &'static str,
}

/// Preview the desugared output as a human-readable string (for IDE tooltips).
pub(crate) fn desugar_preview(
    stmts: &[DoStmt],
    config: &DoDesugarConfig,
) -> Result<DesugarPreview, DoDesugarExtError> {
    if stmts.is_empty() {
        return Err(DoDesugarExtError::EmptyBlock);
    }
    let result = desugar_do_block(stmts, config)
        .map_err(|e| DoDesugarExtError::PreviewFailed(e.to_string()))?;
    let metrics = compute_metrics(stmts);
    let usage = detect_monad_usage(stmts);
    Ok(DesugarPreview {
        preview_text: fmt_expr(&result.desugared, 0),
        bind_count: result.bind_count,
        mut_vars: result.mut_vars,
        metrics,
        minimum_class: usage.minimum_class,
    })
}

fn fmt_expr(expr: &clean_kernel::Expr, indent: usize) -> String {
    use clean_kernel::ExprKind;
    let pre = "  ".repeat(indent);
    match expr.kind() {
        ExprKind::App(f, a) => format!("{pre}({} {})", fmt_expr(f, 0), fmt_expr(a, 0)),
        ExprKind::Lam(_, _ty, body) => format!("{pre}(fun _ =>\n{})", fmt_expr(body, indent + 1)),
        ExprKind::Let(_, _ty, val, body, _) => format!(
            "{pre}let _ := {} in\n{}",
            fmt_expr(val, 0),
            fmt_expr(body, indent + 1)
        ),
        ExprKind::Const(name, _) => format!("{pre}{name}"),
        ExprKind::BVar(idx) => format!("{pre}#{idx}"),
        ExprKind::Sort(level) => format!("{pre}Sort {level}"),
        ExprKind::Lit(lit) => format!("{pre}{lit:?}"),
        _ => format!("{pre}<expr>"),
    }
}

// ---------------------------------------------------------------------------
// Bind chain analysis
// ---------------------------------------------------------------------------

/// A maximal run of consecutive `Bind`/`Action` statements.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct BindChain {
    pub(crate) start: usize,
    pub(crate) length: usize,
    pub(crate) ends_with_return: bool,
}

/// Find all maximal bind chains (consecutive `Bind`/`Action` runs).
#[must_use]
pub(crate) fn find_bind_chains(stmts: &[DoStmt]) -> Vec<BindChain> {
    let mut chains = Vec::new();
    let mut start: Option<usize> = None;
    let mut len: usize = 0;
    for (i, stmt) in stmts.iter().enumerate() {
        if matches!(stmt, DoStmt::Bind { .. } | DoStmt::Action(_)) {
            if start.is_none() {
                start = Some(i);
                len = 0;
            }
            len += 1;
        } else if let Some(s) = start.take() {
            chains.push(BindChain {
                start: s,
                length: len,
                ends_with_return: matches!(stmt, DoStmt::Return(_)),
            });
            len = 0;
        }
    }
    if let Some(s) = start {
        chains.push(BindChain {
            start: s,
            length: len,
            ends_with_return: false,
        });
    }
    chains
}
