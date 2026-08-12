// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! L5IR Function Specialization Pass
//!
//! Creates specialized versions of polymorphic functions for specific type
//! arguments at the low-level IR level. This complements the LCNF-level
//! specialization in `opt::specialize` by operating post-lowering, where
//! concrete `IRType` information is available.
//!
//! # Motivation
//!
//! After monomorphization (`to_mono`) and lowering to L5IR (`to_ir`), many
//! functions still use `Object` as a catch-all type for polymorphic parameters.
//! When call sites pass arguments with known concrete types (e.g., `UInt64`),
//! we can create specialized versions that:
//!
//! 1. Replace `Object` params with concrete scalar types
//! 2. Eliminate unnecessary box/unbox operations
//! 3. Enable scalar register allocation instead of heap allocation
//!
//! # Algorithm
//!
//! 1. **Candidate identification**: Find functions with `Object`-typed
//!    parameters that receive concrete-typed arguments at call sites
//! 2. **Call site collection**: Scan all declarations for Apply expressions
//!    with known concrete type arguments
//! 3. **Specialization key**: Build a dedup key from (fn_name, concrete_types)
//! 4. **Body generation**: Clone the function body, substituting `Object`
//!    with concrete `IRType` in params, locals, and expressions
//! 5. **Call site rewriting**: Redirect matching calls to specialized version
//!
//! # Reference
//!
//! Lean 4: `src/Lean/Compiler/IR/Specialize.lean`
//!
//! Part of Epic #3084 - IO/FFI/Native.

mod specialize_transform;

use crate::ir::{IRArg, IRDecl, IRType, VarId};
use clean_kernel::Name;
use std::collections::{HashMap, HashSet};

pub(crate) use specialize_transform::{
    build_type_env, collect_call_sites, ir_type_suffix, rewrite_call_sites, specialize_body,
    specialized_name, CallSite, TypeEnv,
};

// ═══════════════════════════════════════════════════════════════════════════
// Types and Configuration
// ═══════════════════════════════════════════════════════════════════════════

/// Configuration for the IR specialization pass.
#[derive(Debug, Clone)]
pub(crate) struct SpecializeConfig {
    /// Maximum number of specializations per function (prevents blow-up).
    pub max_specializations_per_fn: usize,
    /// Maximum total specializations across the entire module.
    pub max_total_specializations: usize,
    /// Only specialize functions in this set (empty = all eligible).
    pub specialize_only: HashSet<Name>,
    /// Skip functions in this set.
    pub skip_functions: HashSet<Name>,
}

impl Default for SpecializeConfig {
    fn default() -> Self {
        Self {
            max_specializations_per_fn: 8,
            max_total_specializations: 256,
            specialize_only: HashSet::new(),
            skip_functions: HashSet::new(),
        }
    }
}

/// A specialization key uniquely identifying a (function, type-args) pair.
///
/// Two call sites producing the same key share a single specialized version.
/// Uses a manual `Hash` impl because `IRType` does not derive `Hash`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SpecKey {
    /// Original function name.
    pub(crate) fn_name: Name,
    /// Concrete types for each parameter position.
    /// `None` means the parameter keeps its original type.
    pub(crate) type_args: Vec<Option<IRType>>,
}

impl std::hash::Hash for SpecKey {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.fn_name.hash(state);
        for arg in &self.type_args {
            match arg {
                Some(ty) => {
                    state.write_u8(1);
                    ir_type_suffix(ty).hash(state);
                }
                None => state.write_u8(0),
            }
        }
    }
}

/// Statistics from the specialization pass.
#[derive(Debug, Clone, Default)]
pub(crate) struct SpecStats {
    /// Number of candidate functions found.
    pub candidates_found: usize,
    /// Number of call sites analyzed.
    pub call_sites_analyzed: usize,
    /// Number of specialized functions generated.
    pub specializations_generated: usize,
    /// Number of call sites rewritten.
    pub call_sites_rewritten: usize,
    /// Number of specializations skipped due to limits.
    pub skipped_limit: usize,
    /// Number of deduplicated specializations (cache hits).
    pub dedup_hits: usize,
}

// ═══════════════════════════════════════════════════════════════════════════
// Candidate Identification
// ═══════════════════════════════════════════════════════════════════════════

/// Check if a function is a specialization candidate.
///
/// A function is a candidate if it has at least one `Object`-typed parameter
/// that could benefit from concrete type substitution.
pub(crate) fn is_specialization_candidate(decl: &IRDecl) -> bool {
    decl.params.iter().any(|(_, ty)| *ty == IRType::Object)
}

/// Collect all candidate function names from declarations.
pub(crate) fn find_candidates(decls: &[IRDecl], config: &SpecializeConfig) -> HashSet<Name> {
    decls
        .iter()
        .filter(|d| {
            if !config.skip_functions.is_empty() && config.skip_functions.contains(&d.name) {
                return false;
            }
            if !config.specialize_only.is_empty() && !config.specialize_only.contains(&d.name) {
                return false;
            }
            is_specialization_candidate(d)
        })
        .map(|d| d.name.clone())
        .collect()
}

/// Resolve the concrete type of an IRArg using the type environment.
pub(crate) fn resolve_arg_type(arg: &IRArg, env: &TypeEnv) -> Option<IRType> {
    match arg {
        IRArg::Var(var) => env.get(var).cloned(),
        IRArg::Erased => None,
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Top-Level Entry Point
// ═══════════════════════════════════════════════════════════════════════════

/// Run the IR-level specialization pass on a set of declarations.
///
/// Returns the (potentially modified) declarations plus any generated
/// specialized declarations, and statistics.
pub(crate) fn specialize_ir(
    decls: &[IRDecl],
    config: &SpecializeConfig,
) -> (Vec<IRDecl>, SpecStats) {
    let mut stats = SpecStats::default();

    // Phase 1: Find candidate functions
    let candidates = find_candidates(decls, config);
    stats.candidates_found = candidates.len();

    if candidates.is_empty() {
        return (decls.to_vec(), stats);
    }

    // Build declaration index for lookup
    let decl_index: HashMap<Name, &IRDecl> = decls.iter().map(|d| (d.name.clone(), d)).collect();

    // Phase 2: Collect all unique call sites across all declarations
    let mut unique_keys: HashMap<SpecKey, ()> = HashMap::new();
    let mut per_fn_count: HashMap<Name, usize> = HashMap::new();

    for decl in decls {
        let env = build_type_env(decl);
        let mut sites = Vec::new();
        collect_call_sites(&decl.body, &env, &candidates, &mut sites);
        stats.call_sites_analyzed += sites.len();

        for site in sites {
            let fn_count = per_fn_count.entry(site.key.fn_name.clone()).or_insert(0);
            if *fn_count >= config.max_specializations_per_fn {
                stats.skipped_limit += 1;
                continue;
            }
            if unique_keys.len() >= config.max_total_specializations {
                stats.skipped_limit += 1;
                continue;
            }
            if let std::collections::hash_map::Entry::Vacant(e) = unique_keys.entry(site.key) {
                *fn_count += 1;
                e.insert(());
            } else {
                stats.dedup_hits += 1;
            }
        }
    }

    // Phase 3: Generate specialized declarations
    let mut rewrites: HashMap<SpecKey, Name> = HashMap::new();
    let mut new_decls: Vec<IRDecl> = Vec::new();

    for key in unique_keys.keys() {
        let Some(original) = decl_index.get(&key.fn_name) else {
            continue;
        };

        let spec_name = specialized_name(&key.fn_name, &key.type_args);

        // Build param substitution map
        let mut param_map: HashMap<VarId, IRType> = HashMap::new();
        let new_params: Vec<(VarId, IRType)> = original
            .params
            .iter()
            .zip(key.type_args.iter())
            .map(|((var, orig_ty), spec_ty)| {
                if let Some(concrete) = spec_ty {
                    param_map.insert(*var, concrete.clone());
                    (*var, concrete.clone())
                } else {
                    (*var, orig_ty.clone())
                }
            })
            .collect();

        let new_body = specialize_body(&original.body, &param_map);
        let return_type = original.return_type.clone();

        new_decls.push(IRDecl {
            name: spec_name.clone(),
            params: new_params,
            return_type,
            body: new_body,
        });

        rewrites.insert(key.clone(), spec_name);
        stats.specializations_generated += 1;
    }

    // Phase 4: Rewrite call sites in original declarations
    let mut result: Vec<IRDecl> = decls
        .iter()
        .map(|decl| {
            let env = build_type_env(decl);
            let new_body = rewrite_call_sites(&decl.body, &env, &rewrites);
            if format!("{:?}", new_body) != format!("{:?}", decl.body) {
                stats.call_sites_rewritten += 1;
            }
            IRDecl {
                name: decl.name.clone(),
                params: decl.params.clone(),
                return_type: decl.return_type.clone(),
                body: new_body,
            }
        })
        .collect();

    // Append generated specializations
    result.extend(new_decls);

    (result, stats)
}

/// Convenience wrapper with default configuration.
#[must_use]
pub(crate) fn specialize_ir_default(decls: &[IRDecl]) -> Vec<IRDecl> {
    let (result, _) = specialize_ir(decls, &SpecializeConfig::default());
    result
}

#[cfg(test)]
#[path = "specialize_tests.rs"]
mod tests;
