// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended interactive command support: dependency analysis, batching,
//! validation, metrics, and command transformation.
//!
//! Builds on [`crate::commands`] by adding a small command model around
//! `#check`, `#eval`, and `#print`, then layering pure scheduling and
//! preprocessing utilities on top of the existing elaboration entry points.

use std::collections::{BTreeMap, BTreeSet};
use std::time::Instant;

use crate::commands::{self, CheckResult, EvalResult, PrintResult};
use crate::error::ElabError;
use clean_kernel::expr::ZFCSetExpr;
use clean_kernel::{Environment, Expr, ExprFolder, ExprKind, LevelVec, MDataMap, Name};

// =============================================================================
// Command model
// =============================================================================

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum CommandSpec {
    Check { expr: Expr },
    Eval { expr: Expr },
    Print { name: Name },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CommandPlan {
    pub(crate) declares: BTreeSet<Name>,
    pub(crate) command: CommandSpec,
}

impl CommandPlan {
    #[must_use]
    pub(crate) fn new(command: CommandSpec) -> Self {
        Self {
            declares: BTreeSet::new(),
            command,
        }
    }

    #[must_use]
    pub(crate) fn with_declares(mut self, declares: impl IntoIterator<Item = Name>) -> Self {
        self.declares.extend(declares);
        self
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct CommandDependencyInfo {
    pub(crate) declared: BTreeSet<Name>,
    pub(crate) referenced: BTreeSet<Name>,
    pub(crate) depends_on: BTreeSet<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct CommandBatch {
    pub(crate) index: usize,
    pub(crate) commands: Vec<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum CommandResult {
    Check(CheckResult),
    Eval(EvalResult),
    Print(PrintResult),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub(crate) struct CommandMetrics {
    pub(crate) dependency_count: usize,
    pub(crate) elaboration_depth: u32,
    pub(crate) elapsed_ns: u64,
    pub(crate) type_check_cost: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CommandExecution {
    pub(crate) dependencies: BTreeSet<Name>,
    pub(crate) metrics: CommandMetrics,
    pub(crate) result: CommandResult,
}

// =============================================================================
// Errors and validation
// =============================================================================

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub(crate) enum CommandExtError {
    #[error("standalone command contains loose bound variables")]
    LooseBoundVars,
    #[error("standalone command contains free variables")]
    FreeVars,
    #[error("#print requires a non-anonymous declaration name")]
    AnonymousPrintTarget,
    #[error("name `{name}` is declared by multiple commands ({first} and {second})")]
    DuplicateDeclaration {
        name: Name,
        first: usize,
        second: usize,
    },
    #[error("command dependency cycle detected among command indices {cycle:?}")]
    DependencyCycle { cycle: Vec<usize> },
}

impl From<CommandExtError> for ElabError {
    fn from(err: CommandExtError) -> Self {
        ElabError::Unsupported {
            feature: err.to_string(),
        }
    }
}

pub(crate) fn validate_command(command: &CommandSpec) -> Result<(), CommandExtError> {
    match command {
        CommandSpec::Check { expr } | CommandSpec::Eval { expr } => {
            if expr.has_loose_bvars() {
                return Err(CommandExtError::LooseBoundVars);
            }
            if expr.has_fvar_quick() {
                return Err(CommandExtError::FreeVars);
            }
        }
        CommandSpec::Print { name } if name.is_anon() => {
            return Err(CommandExtError::AnonymousPrintTarget);
        }
        CommandSpec::Print { .. } => {}
    }
    Ok(())
}

// =============================================================================
// Dependency analysis and batching
// =============================================================================

#[must_use]
pub(crate) fn command_dependencies(command: &CommandSpec) -> BTreeSet<Name> {
    match command {
        CommandSpec::Check { expr } | CommandSpec::Eval { expr } => {
            expr.collect_constants().into_iter().collect()
        }
        CommandSpec::Print { name } => std::iter::once(name.clone()).collect(),
    }
}

pub(crate) fn analyze_command_dependencies(
    plans: &[CommandPlan],
) -> Result<Vec<CommandDependencyInfo>, CommandExtError> {
    let mut declared_by = BTreeMap::<Name, usize>::new();
    for (index, plan) in plans.iter().enumerate() {
        validate_command(&plan.command)?;
        for decl in &plan.declares {
            if let Some(first) = declared_by.insert(decl.clone(), index) {
                return Err(CommandExtError::DuplicateDeclaration {
                    name: decl.clone(),
                    first,
                    second: index,
                });
            }
        }
    }

    plans
        .iter()
        .enumerate()
        .map(|(index, plan)| {
            let referenced = command_dependencies(&plan.command);
            let depends_on = referenced
                .iter()
                .filter_map(|name| declared_by.get(name).copied())
                .filter(|other| *other != index)
                .collect();
            Ok(CommandDependencyInfo {
                declared: plan.declares.clone(),
                referenced,
                depends_on,
            })
        })
        .collect()
}

pub(crate) fn batch_independent_commands(
    plans: &[CommandPlan],
) -> Result<Vec<CommandBatch>, CommandExtError> {
    let analyses = analyze_command_dependencies(plans)?;
    let mut remaining: BTreeMap<usize, BTreeSet<usize>> = analyses
        .iter()
        .enumerate()
        .map(|(index, info)| (index, info.depends_on.clone()))
        .collect();
    let mut batches = Vec::new();

    while !remaining.is_empty() {
        let ready: Vec<usize> = remaining
            .iter()
            .filter(|(_, deps)| deps.is_empty())
            .map(|(index, _)| *index)
            .collect();
        if ready.is_empty() {
            return Err(CommandExtError::DependencyCycle {
                cycle: remaining.keys().copied().collect(),
            });
        }

        let ready_set: BTreeSet<usize> = ready.iter().copied().collect();
        for index in &ready {
            remaining.remove(index);
        }
        for deps in remaining.values_mut() {
            deps.retain(|dep| !ready_set.contains(dep));
        }

        batches.push(CommandBatch {
            index: batches.len(),
            commands: ready,
        });
    }

    Ok(batches)
}

// =============================================================================
// Transformation
// =============================================================================

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum CommandTransform {
    NormalizeExpr,
    RewriteName { from: Name, to: Name },
}

struct CommandExprFolder {
    rewrites: BTreeMap<Name, Name>,
    strip_metadata: bool,
}

impl ExprFolder for CommandExprFolder {
    fn fold_const(&mut self, name: &Name, levels: &LevelVec) -> Expr {
        let rewritten = self
            .rewrites
            .get(name)
            .cloned()
            .unwrap_or_else(|| name.clone());
        Expr::const_(rewritten, levels.clone())
    }

    fn fold_proj(&mut self, struct_name: &Name, idx: u32, inner: &Expr) -> Expr {
        let rewritten = self
            .rewrites
            .get(struct_name)
            .cloned()
            .unwrap_or_else(|| struct_name.clone());
        Expr::proj(rewritten, idx, self.fold_expr(inner))
    }

    fn fold_mdata(&mut self, metadata: &MDataMap, inner: &Expr) -> Expr {
        let folded = self.fold_expr(inner);
        if self.strip_metadata {
            folded
        } else {
            Expr::mdata(metadata.clone(), folded)
        }
    }
}

#[must_use]
fn rewrite_name(name: &Name, rewrites: &BTreeMap<Name, Name>) -> Name {
    rewrites.get(name).cloned().unwrap_or_else(|| name.clone())
}

fn transform_expr(expr: &Expr, rewrites: &BTreeMap<Name, Name>, strip_metadata: bool) -> Expr {
    let mut folder = CommandExprFolder {
        rewrites: rewrites.clone(),
        strip_metadata,
    };
    folder.fold_expr(expr)
}

#[must_use]
pub(crate) fn apply_command_transform(
    command: &CommandSpec,
    transform: &CommandTransform,
) -> CommandSpec {
    match transform {
        CommandTransform::NormalizeExpr => match command {
            CommandSpec::Check { expr } => CommandSpec::Check {
                expr: transform_expr(expr, &BTreeMap::new(), true),
            },
            CommandSpec::Eval { expr } => CommandSpec::Eval {
                expr: transform_expr(expr, &BTreeMap::new(), true),
            },
            CommandSpec::Print { name } => CommandSpec::Print { name: name.clone() },
        },
        CommandTransform::RewriteName { from, to } => {
            let rewrites = std::iter::once((from.clone(), to.clone())).collect::<BTreeMap<_, _>>();
            match command {
                CommandSpec::Check { expr } => CommandSpec::Check {
                    expr: transform_expr(expr, &rewrites, false),
                },
                CommandSpec::Eval { expr } => CommandSpec::Eval {
                    expr: transform_expr(expr, &rewrites, false),
                },
                CommandSpec::Print { name } => CommandSpec::Print {
                    name: rewrite_name(name, &rewrites),
                },
            }
        }
    }
}

#[must_use]
pub(crate) fn transform_command(
    command: &CommandSpec,
    transforms: &[CommandTransform],
) -> CommandSpec {
    transforms
        .iter()
        .fold(command.clone(), |current, transform| {
            apply_command_transform(&current, transform)
        })
}

// =============================================================================
// Metrics and execution
// =============================================================================

#[must_use]
fn duration_as_nanos_u64(duration: std::time::Duration) -> u64 {
    u64::try_from(duration.as_nanos()).unwrap_or(u64::MAX)
}

#[must_use]
pub(crate) fn command_metrics(command: &CommandSpec, elapsed_ns: u64) -> CommandMetrics {
    let dependencies = command_dependencies(command);
    match command {
        CommandSpec::Check { expr } | CommandSpec::Eval { expr } => {
            let metrics = expr_metrics(expr);
            CommandMetrics {
                dependency_count: dependencies.len(),
                elaboration_depth: metrics.depth,
                elapsed_ns,
                type_check_cost: u64::from(metrics.nodes)
                    + u64::try_from(dependencies.len()).unwrap_or(u64::MAX),
            }
        }
        CommandSpec::Print { .. } => CommandMetrics {
            dependency_count: dependencies.len(),
            elaboration_depth: 0,
            elapsed_ns,
            type_check_cost: 1,
        },
    }
}

#[must_use]
fn expr_metrics(expr: &Expr) -> ExprMetrics {
    match expr.kind() {
        ExprKind::BVar(_)
        | ExprKind::FVar(_)
        | ExprKind::Sort(_)
        | ExprKind::Const(_, _)
        | ExprKind::Lit(_)
        | ExprKind::SProp
        | ExprKind::CubicalInterval
        | ExprKind::CubicalI0
        | ExprKind::CubicalI1 => ExprMetrics { depth: 1, nodes: 1 },
        ExprKind::App(f, a) => combine_binary(expr_metrics(f), expr_metrics(a)),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            combine_binary(expr_metrics(ty), expr_metrics(body))
        }
        ExprKind::Let(_, ty, val, body, _) => {
            combine_many(&[expr_metrics(ty), expr_metrics(val), expr_metrics(body)])
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
            bump(expr_metrics(inner))
        }
        ExprKind::CubicalPath { ty, left, right } => {
            combine_many(&[expr_metrics(ty), expr_metrics(left), expr_metrics(right)])
        }
        ExprKind::CubicalPathLam { body } => bump(expr_metrics(body)),
        ExprKind::CubicalPathApp { path, arg } => {
            combine_binary(expr_metrics(path), expr_metrics(arg))
        }
        ExprKind::CubicalHComp { ty, phi, u, base } => combine_many(&[
            expr_metrics(ty),
            expr_metrics(phi),
            expr_metrics(u),
            expr_metrics(base),
        ]),
        ExprKind::CubicalTransp { ty, phi, base } => {
            combine_many(&[expr_metrics(ty), expr_metrics(phi), expr_metrics(base)])
        }
        ExprKind::CubicalCoe { ty, r, s, base } => combine_many(&[
            expr_metrics(ty),
            expr_metrics(r),
            expr_metrics(s),
            expr_metrics(base),
        ]),
        ExprKind::ZFCSet(set_expr) => bump(zfc_set_expr_metrics(set_expr)),
        ExprKind::ZFCMem { element, set } => {
            combine_binary(expr_metrics(element), expr_metrics(set))
        }
        ExprKind::ZFCComprehension { domain, pred } => {
            combine_binary(expr_metrics(domain), expr_metrics(pred))
        }
    }
}

#[must_use]
fn zfc_set_expr_metrics(set_expr: &ZFCSetExpr) -> ExprMetrics {
    match set_expr {
        ZFCSetExpr::Empty | ZFCSetExpr::Infinity => ExprMetrics { depth: 1, nodes: 1 },
        ZFCSetExpr::Singleton(expr)
        | ZFCSetExpr::Union(expr)
        | ZFCSetExpr::PowerSet(expr)
        | ZFCSetExpr::Choice(expr) => bump(expr_metrics(expr)),
        ZFCSetExpr::Pair(left, right) => combine_binary(expr_metrics(left), expr_metrics(right)),
        ZFCSetExpr::Separation { set, pred } | ZFCSetExpr::Replacement { set, func: pred } => {
            combine_binary(expr_metrics(set), expr_metrics(pred))
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
struct ExprMetrics {
    depth: u32,
    nodes: u32,
}

#[must_use]
fn bump(metrics: ExprMetrics) -> ExprMetrics {
    ExprMetrics {
        depth: metrics.depth + 1,
        nodes: metrics.nodes + 1,
    }
}

#[must_use]
fn combine_binary(left: ExprMetrics, right: ExprMetrics) -> ExprMetrics {
    ExprMetrics {
        depth: 1 + left.depth.max(right.depth),
        nodes: 1 + left.nodes + right.nodes,
    }
}

#[must_use]
fn combine_many(metrics: &[ExprMetrics]) -> ExprMetrics {
    let mut depth = 0;
    let mut nodes = 1;
    for metric in metrics {
        depth = depth.max(metric.depth);
        nodes += metric.nodes;
    }
    ExprMetrics {
        depth: depth + 1,
        nodes,
    }
}

pub(crate) fn elaborate_command_ext(
    env: &Environment,
    command: &CommandSpec,
    transforms: &[CommandTransform],
) -> Result<CommandExecution, ElabError> {
    let transformed = transform_command(command, transforms);
    validate_command(&transformed)?;
    let dependencies = command_dependencies(&transformed);

    let start = Instant::now();
    let result = match &transformed {
        CommandSpec::Check { expr } => CommandResult::Check(commands::elab_check(env, expr)?),
        CommandSpec::Eval { expr } => CommandResult::Eval(commands::elab_eval(env, expr)?),
        CommandSpec::Print { name } => {
            CommandResult::Print(commands::elab_print(env, &name.to_string())?)
        }
    };
    let metrics = command_metrics(&transformed, duration_as_nanos_u64(start.elapsed()));

    Ok(CommandExecution {
        dependencies,
        metrics,
        result,
    })
}
