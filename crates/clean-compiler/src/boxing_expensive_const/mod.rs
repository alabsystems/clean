// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Expensive Constant Boxing Optimization for L5IR
//!
//! When a constant expression is "expensive" (e.g., a constructor application
//! with arguments, or a string literal), it should be boxed once and cached
//! rather than recomputed at every use site. This pass:
//!
//! 1. Walks the function body to identify expensive constant expressions.
//! 2. Deduplicates structurally identical expressions via a normalized key.
//! 3. Hoists each unique expensive expression to a `let` binding at function
//!    entry, replacing subsequent occurrences with variable references.
//!
//! # What counts as "expensive"
//!
//! - `Ctor { args }` where `args.len() >= config.min_args` and all args are
//!   either `Erased` or variables already in scope.
//! - `String` literals (heap-allocated).
//! - `Lit` values of non-small types (UInt64, USize, Float64, Float32) that
//!   require boxing when passed to polymorphic code.
//!
//! # Algorithm
//!
//! Two-pass design:
//! - **Pass 1 (collect):** Walk the body collecting every VDecl whose value
//!   matches an expensive pattern. Each unique expression (by normalized key)
//!   gets a fresh VarId. A substitution map records original VarId -> hoisted.
//! - **Pass 2 (rewrite):** Walk the body again. VDecls for hoisted expressions
//!   are removed. All VarId references are substituted per the plan. Finally,
//!   the hoisted bindings are prepended at function entry.
//!
//! # Lean 4 Reference
//!
//! Based on the expensive constant optimization in Lean 4's boxing pass
//! (`src/Lean/Compiler/IR/Boxing.lean`). The Lean 4 implementation hoists
//! expensive constants into auxiliary top-level declarations; this
//! implementation hoists them to function-entry `let` bindings for
//! simplicity and to avoid cross-declaration concerns.
//!
//! Part of #1053 -- boxing.rs missing expensive constant boxing optimization.

use std::collections::HashMap;

use crate::ir::{IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, VarId};

// ════════════════════════════════════════════════════════════════════════════
// Public API
// ════════════════════════════════════════════════════════════════════════════

/// Configuration for expensive constant boxing.
#[derive(Debug, Clone)]
pub struct ExpensiveConstConfig {
    /// Minimum number of constructor arguments to consider "expensive".
    ///
    /// A constructor with fewer arguments than this threshold is considered
    /// cheap enough to re-evaluate at each use site. Default: 1.
    pub min_args: usize,
}

impl Default for ExpensiveConstConfig {
    fn default() -> Self {
        Self { min_args: 1 }
    }
}

/// Result of the expensive constant boxing pass.
#[derive(Debug, Clone)]
pub struct ExpensiveConstResult {
    /// The transformed declaration with hoisted bindings prepended.
    pub decl: IRDecl,
    /// Number of unique expensive expressions that were hoisted.
    pub hoisted_count: usize,
}

/// Apply the expensive constant boxing optimization to a single declaration.
///
/// Scans the function body for expensive constant expressions, deduplicates
/// them by structural identity, and hoists each unique occurrence to a `let`
/// binding at function entry. Original VDecls that held expensive expressions
/// are removed and all references substituted to the hoisted variable.
#[must_use]
pub fn box_expensive_constants(
    decl: &IRDecl,
    config: &ExpensiveConstConfig,
) -> ExpensiveConstResult {
    let plan = build_hoist_plan(&decl.body, &decl.params, config);

    if plan.bindings.is_empty() {
        return ExpensiveConstResult {
            decl: decl.clone(),
            hoisted_count: 0,
        };
    }

    let hoisted_count = plan.bindings.len();
    let rewritten_body = apply_plan(&decl.body, &plan);

    // Prepend hoisted bindings at function entry.
    let mut final_body = rewritten_body;
    for binding in plan.bindings.into_iter().rev() {
        final_body = IRBody::VDecl {
            var: binding.var,
            ty: binding.ty,
            value: binding.value,
            rest: Box::new(final_body),
        };
    }

    ExpensiveConstResult {
        decl: IRDecl {
            name: decl.name.clone(),
            params: decl.params.clone(),
            return_type: decl.return_type.clone(),
            body: final_body,
        },
        hoisted_count,
    }
}

/// Apply the expensive constant boxing optimization with default config.
#[must_use]
pub fn box_expensive_constants_default(decl: &IRDecl) -> ExpensiveConstResult {
    box_expensive_constants(decl, &ExpensiveConstConfig::default())
}

// ════════════════════════════════════════════════════════════════════════════
// Normalized key for structural comparison
// ════════════════════════════════════════════════════════════════════════════

/// A hashable, equality-comparable key for deduplicating IRExpr values.
///
/// `IRExpr` does not derive `PartialEq`/`Hash` (CtorInfo contains floats
/// and `Name` which uses `Arc`), so we normalize into this key type.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum ExprKey {
    Ctor {
        name: String,
        tag: u32,
        args: Vec<ArgKey>,
    },
    String(String),
    LitU64(u64),
    LitUSize(u64),
    LitF64(u64), // bit pattern for deterministic Hash/Eq
    LitF32(u32), // bit pattern
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum ArgKey {
    Var(u32),
    Erased,
}

fn normalize_arg(arg: &IRArg) -> ArgKey {
    match arg {
        IRArg::Var(v) => ArgKey::Var(v.0),
        IRArg::Erased => ArgKey::Erased,
    }
}

/// Attempt to normalize an `IRExpr` into a hashable key.
///
/// Returns `None` for expressions that are not candidates for hoisting.
fn normalize_expr(expr: &IRExpr, config: &ExpensiveConstConfig) -> Option<ExprKey> {
    match expr {
        IRExpr::Ctor { info, args } if args.len() >= config.min_args => {
            let arg_keys: Vec<ArgKey> = args.iter().map(normalize_arg).collect();
            Some(ExprKey::Ctor {
                name: info.name.to_string(),
                tag: info.tag,
                args: arg_keys,
            })
        }
        IRExpr::String(s) => Some(ExprKey::String(s.clone())),
        IRExpr::Lit(IRLiteral::UInt64(v)) => Some(ExprKey::LitU64(*v)),
        IRExpr::Lit(IRLiteral::USize(v)) => Some(ExprKey::LitUSize(*v as u64)),
        IRExpr::Lit(IRLiteral::Float64(v)) => Some(ExprKey::LitF64(v.to_bits())),
        IRExpr::Lit(IRLiteral::Float32(v)) => Some(ExprKey::LitF32(v.to_bits())),
        _ => None,
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Hoisting plan
// ════════════════════════════════════════════════════════════════════════════

/// A single hoisted binding: `let var : ty = value`.
pub(crate) struct HoistedBinding {
    pub(crate) var: VarId,
    pub(crate) ty: IRType,
    pub(crate) value: IRExpr,
}

/// The result of pass 1: a plan for what to hoist and how to rewrite.
pub(crate) struct HoistPlan {
    /// Hoisted bindings to prepend at function entry.
    pub(crate) bindings: Vec<HoistedBinding>,
    /// Map from original VarId to the hoisted VarId that replaces it.
    pub(crate) subst: HashMap<VarId, VarId>,
    /// Set of original VarIds whose VDecls should be removed.
    pub(crate) removed: HashMap<VarId, ()>,
}

// ════════════════════════════════════════════════════════════════════════════
// Pass 1: collect expensive expression sites
// ════════════════════════════════════════════════════════════════════════════

/// Collected info about an expensive expression at a specific VDecl site.
struct ExpensiveSite {
    original_var: VarId,
    key: ExprKey,
}

fn collect_sites(body: &IRBody, config: &ExpensiveConstConfig, sites: &mut Vec<ExpensiveSite>) {
    match body {
        IRBody::VDecl {
            var, value, rest, ..
        } => {
            if let Some(key) = normalize_expr(value, config) {
                sites.push(ExpensiveSite {
                    original_var: *var,
                    key,
                });
            }
            collect_sites(rest, config, sites);
        }
        IRBody::JDecl { body, rest, .. } => {
            collect_sites(body, config, sites);
            collect_sites(rest, config, sites);
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => {
            collect_sites(rest, config, sites);
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                collect_sites(&alt.body, config, sites);
            }
            if let Some(d) = default {
                collect_sites(d, config, sites);
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

/// Collect the first (expr, type) for each unique expensive expression key.
fn collect_exprs(
    body: &IRBody,
    config: &ExpensiveConstConfig,
    map: &mut HashMap<ExprKey, (IRExpr, IRType)>,
) {
    match body {
        IRBody::VDecl {
            ty, value, rest, ..
        } => {
            if let Some(key) = normalize_expr(value, config) {
                map.entry(key)
                    .or_insert_with(|| (value.clone(), ty.clone()));
            }
            collect_exprs(rest, config, map);
        }
        IRBody::JDecl { body, rest, .. } => {
            collect_exprs(body, config, map);
            collect_exprs(rest, config, map);
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => {
            collect_exprs(rest, config, map);
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                collect_exprs(&alt.body, config, map);
            }
            if let Some(d) = default {
                collect_exprs(d, config, map);
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

fn build_hoist_plan(
    body: &IRBody,
    params: &[(VarId, IRType)],
    config: &ExpensiveConstConfig,
) -> HoistPlan {
    let mut sites = Vec::new();
    collect_sites(body, config, &mut sites);

    if sites.is_empty() {
        return HoistPlan {
            bindings: Vec::new(),
            subst: HashMap::new(),
            removed: HashMap::new(),
        };
    }

    let base_var = max_var_id(body, params) + 1;
    let mut next_var = base_var;

    let mut key_to_hoisted: HashMap<ExprKey, VarId> = HashMap::new();
    let mut key_to_expr: HashMap<ExprKey, (IRExpr, IRType)> = HashMap::new();
    collect_exprs(body, config, &mut key_to_expr);

    let mut subst: HashMap<VarId, VarId> = HashMap::new();
    let mut removed: HashMap<VarId, ()> = HashMap::new();

    // Track insertion order for deterministic binding order.
    let mut ordered_keys: Vec<ExprKey> = Vec::new();

    for site in &sites {
        let hoisted_var = if let Some(&existing) = key_to_hoisted.get(&site.key) {
            existing
        } else {
            let var = VarId(next_var);
            next_var += 1;
            key_to_hoisted.insert(site.key.clone(), var);
            ordered_keys.push(site.key.clone());
            var
        };
        subst.insert(site.original_var, hoisted_var);
        removed.insert(site.original_var, ());
    }

    let bindings: Vec<HoistedBinding> = ordered_keys
        .iter()
        .filter_map(|key| {
            let var = key_to_hoisted[key];
            let (expr, ty) = key_to_expr.get(key)?;
            Some(HoistedBinding {
                var,
                ty: ty.clone(),
                value: expr.clone(),
            })
        })
        .collect();

    HoistPlan {
        bindings,
        subst,
        removed,
    }
}

mod rewrite;
use rewrite::{apply_plan, max_var_id};

#[cfg(test)]
mod tests;
