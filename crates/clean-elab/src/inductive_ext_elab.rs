// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended inductive type elaboration pipeline.
//!
//! Consumes specifications from `inductive_ext` and produces elaborated
//! results by delegating to the mutual inductive pipeline. Handles
//! single inductive, mutual inductive, and auxiliary generation
//! (casesOn, noConfusion).
//!
//! See `inductive_ext.rs` for type definitions and core analysis functions.

use clean_kernel::inductive::mentions_name;
use clean_kernel::{BinderInfo, Expr, Level, Name};
use std::collections::HashSet;

use crate::error::ElabError;
use crate::inductive_ext::{
    check_strict_positivity, is_prop_type, InductiveElabConfig, InductiveResult, InductiveSpec,
    MutualInductiveResult, MutualInductiveSpec,
};
use crate::mutual_inductive::{
    elaborate_mutual_inductive, ConstructorInfo, InductiveTypeInfo, MutualIndConfig,
    MutualInductiveBlock,
};

// =============================================================================
// Single inductive elaboration
// =============================================================================

/// Elaborate a single `InductiveSpec` into an `InductiveResult`.
///
/// Validates configuration limits, checks positivity (if enabled),
/// then delegates to the mutual inductive pipeline (as a single-type block).
pub(crate) fn elaborate_inductive(
    spec: &InductiveSpec,
    config: &InductiveElabConfig,
) -> Result<InductiveResult, ElabError> {
    if spec.params.len() > config.max_params {
        return Err(ElabError::Unsupported {
            feature: format!(
                "inductive {} has {} parameters, exceeding limit of {}",
                spec.name,
                spec.params.len(),
                config.max_params,
            ),
        });
    }

    if spec.is_nested && !config.allow_nested {
        return Err(ElabError::Unsupported {
            feature: format!("nested inductive type {} not allowed by config", spec.name),
        });
    }

    if config.check_positivity {
        check_strict_positivity(spec).map_err(|e| ElabError::Unsupported {
            feature: e.to_string(),
        })?;
    }

    let block = spec_to_block(spec);
    let mut_config = to_mutual_config(config);
    let env = clean_kernel::Environment::new();
    let mut_result = elaborate_mutual_inductive(&block, &env, &mut_config)?;

    let decl = spec.type_.clone();
    let recursor = if let Some(rec_spec) = mut_result.recursor_specs.first() {
        rec_spec.val.type_.clone()
    } else {
        Expr::sort(Level::zero())
    };

    let cases_on = if !spec.ctors.is_empty() {
        Some(build_cases_on_type(spec))
    } else {
        None
    };

    let no_confusion = if !spec.ctors.is_empty() && !is_prop_type(&spec.type_) {
        Some(build_no_confusion_type(spec))
    } else {
        None
    };

    Ok(InductiveResult {
        decl,
        recursor,
        cases_on,
        no_confusion,
    })
}

// =============================================================================
// Mutual inductive elaboration
// =============================================================================

/// Elaborate a `MutualInductiveSpec` into a `MutualInductiveResult`.
///
/// Validates mutual blocks are allowed, checks all positivity, and
/// generates per-type results plus mutual recursors.
pub(crate) fn elaborate_mutual_inductive_spec(
    spec: &MutualInductiveSpec,
    config: &InductiveElabConfig,
) -> Result<MutualInductiveResult, ElabError> {
    if spec.inductives.len() > 1 && !config.allow_mutual {
        return Err(ElabError::Unsupported {
            feature: "mutual inductive types not allowed by config".into(),
        });
    }

    for ind in &spec.inductives {
        if ind.params.len() > config.max_params {
            return Err(ElabError::Unsupported {
                feature: format!(
                    "inductive {} has {} parameters, exceeding limit of {}",
                    ind.name,
                    ind.params.len(),
                    config.max_params,
                ),
            });
        }
    }

    let mut names = HashSet::new();
    for ind in &spec.inductives {
        if !names.insert(&ind.name) {
            return Err(ElabError::Unsupported {
                feature: format!("duplicate inductive type name: {}", ind.name),
            });
        }
    }

    if config.check_positivity {
        for ind in &spec.inductives {
            check_strict_positivity(ind).map_err(|e| ElabError::Unsupported {
                feature: e.to_string(),
            })?;
        }
    }

    let block = mutual_spec_to_block(spec);
    let mut_config = to_mutual_config(config);
    let env = clean_kernel::Environment::new();
    let mut_result = elaborate_mutual_inductive(&block, &env, &mut_config)?;

    let results: Vec<InductiveResult> = spec
        .inductives
        .iter()
        .map(|ind| {
            let decl = ind.type_.clone();
            let recursor = mut_result
                .recursor_specs
                .iter()
                .find(|r| r.val.inductive_name == ind.name)
                .map(|r| r.val.type_.clone())
                .unwrap_or_else(|| Expr::sort(Level::zero()));

            let cases_on = if !ind.ctors.is_empty() {
                Some(build_cases_on_type(ind))
            } else {
                None
            };

            let no_confusion = if !ind.ctors.is_empty() && !is_prop_type(&ind.type_) {
                Some(build_no_confusion_type(ind))
            } else {
                None
            };

            InductiveResult {
                decl,
                recursor,
                cases_on,
                no_confusion,
            }
        })
        .collect();

    let mutual_recursors = mut_result
        .recursor_specs
        .iter()
        .map(|r| r.val.type_.clone())
        .collect();

    Ok(MutualInductiveResult {
        results,
        mutual_recursors,
    })
}

// =============================================================================
// Conversion helpers
// =============================================================================

/// Convert an `InductiveSpec` into a `MutualInductiveBlock` for delegation.
fn spec_to_block(spec: &InductiveSpec) -> MutualInductiveBlock {
    let ctors: Vec<ConstructorInfo> = spec
        .ctors
        .iter()
        .map(|c| ConstructorInfo {
            name: c.name.clone(),
            type_expr: c.type_.clone(),
        })
        .collect();

    MutualInductiveBlock {
        types: vec![InductiveTypeInfo {
            name: spec.name.clone(),
            type_expr: spec.type_.clone(),
            constructors: ctors,
            is_recursive: spec.is_recursive,
            references_siblings: false,
        }],
        universe_params: Vec::new(),
        num_params: spec.params.len() as u32,
        is_unsafe: false,
    }
}

/// Convert a `MutualInductiveSpec` into a `MutualInductiveBlock`.
fn mutual_spec_to_block(spec: &MutualInductiveSpec) -> MutualInductiveBlock {
    let all_names: HashSet<&Name> = spec.inductives.iter().map(|i| &i.name).collect();
    let num_params = spec
        .inductives
        .first()
        .map(|i| i.params.len() as u32)
        .unwrap_or(0);

    let types = spec
        .inductives
        .iter()
        .map(|ind| {
            let ctors: Vec<ConstructorInfo> = ind
                .ctors
                .iter()
                .map(|c| ConstructorInfo {
                    name: c.name.clone(),
                    type_expr: c.type_.clone(),
                })
                .collect();

            let references_siblings = ind.ctors.iter().any(|c| {
                c.fields.iter().any(|(_, ty, _)| {
                    all_names
                        .iter()
                        .any(|n| **n != ind.name && mentions_name(ty, n))
                })
            });

            InductiveTypeInfo {
                name: ind.name.clone(),
                type_expr: ind.type_.clone(),
                constructors: ctors,
                is_recursive: ind.is_recursive,
                references_siblings,
            }
        })
        .collect();

    MutualInductiveBlock {
        types,
        universe_params: spec.universe_params.clone(),
        num_params,
        is_unsafe: false,
    }
}

/// Convert `InductiveElabConfig` to `MutualIndConfig`.
fn to_mutual_config(config: &InductiveElabConfig) -> MutualIndConfig {
    MutualIndConfig {
        check_positivity: config.check_positivity,
        generate_recursors: true,
        max_mutual_types: if config.allow_mutual { 32 } else { 1 },
    }
}

// =============================================================================
// Auxiliary type builders
// =============================================================================

/// Build a placeholder `casesOn` type for the given inductive spec.
///
/// The actual implementation would produce a full dependent eliminator;
/// this builds the type skeleton with correct binder count.
fn build_cases_on_type(spec: &InductiveSpec) -> Expr {
    let n_binders = spec.params.len() + 1 + spec.ctors.len() + 1;
    let mut result = Expr::sort(Level::param(Name::from_string("u_cases")));
    for _ in 0..n_binders {
        result = Expr::pi(BinderInfo::Default, Expr::sort(Level::zero()), result);
    }
    result
}

/// Build a placeholder `noConfusion` type for the given inductive spec.
///
/// noConfusion proves that distinct constructors produce distinct values.
/// Binder count follows the v4.30 heterogeneous `noConfusionType` shape
/// (designs/2026-07-03-noconfusion-ctoridx-convention.md §3):
/// `Sort u → {p…} → T p… → {p'…} → T p'… → Sort u`, i.e. `2*params + 3`
/// binders (P, the params + first major, the PRIMED params + second major).
/// For 0 params this coincides with the classic `params + 3` count.
fn build_no_confusion_type(spec: &InductiveSpec) -> Expr {
    let n_binders = 2 * spec.params.len() + 3;
    let mut result = Expr::sort(Level::param(Name::from_string("u_nc")));
    for _ in 0..n_binders {
        result = Expr::pi(BinderInfo::Default, Expr::sort(Level::zero()), result);
    }
    result
}
