// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Mutual inductive type elaboration: validation, positivity checking,
//! recursor generation, and universe computation.
//!
//! Lean 4 reference: `src/kernel/inductive.cpp`.

use clean_kernel::inductive::{
    self, count_pi_args, mentions_name, InductiveDecl, InductiveType, RecursorRule, RecursorVal,
};
use clean_kernel::{
    BinderInfo, Constructor, ConstructorVal, Environment, Expr, InductiveError, InductiveVal,
    Level, Name, RecursorArgOrder,
};
use std::collections::HashSet;

use crate::error::ElabError;

/// Configuration for mutual inductive elaboration.
#[derive(Debug, Clone)]
pub(crate) struct MutualIndConfig {
    pub(crate) check_positivity: bool,
    pub(crate) generate_recursors: bool,
    pub(crate) max_mutual_types: usize,
}

impl Default for MutualIndConfig {
    fn default() -> Self {
        Self {
            check_positivity: true,
            generate_recursors: true,
            max_mutual_types: 32,
        }
    }
}

/// Info for one type in a mutual block.
#[derive(Debug, Clone)]
// Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
// keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[allow(dead_code)]
pub(crate) struct InductiveTypeInfo {
    pub(crate) name: Name,
    pub(crate) type_expr: Expr,
    pub(crate) constructors: Vec<ConstructorInfo>,
    pub(crate) is_recursive: bool,
    pub(crate) references_siblings: bool,
}

/// Constructor info at the elaboration level.
#[derive(Debug, Clone)]
pub(crate) struct ConstructorInfo {
    pub(crate) name: Name,
    pub(crate) type_expr: Expr,
}

/// A mutual inductive block ready for elaboration.
#[derive(Debug, Clone)]
pub(crate) struct MutualInductiveBlock {
    pub(crate) types: Vec<InductiveTypeInfo>,
    pub(crate) universe_params: Vec<Name>,
    pub(crate) num_params: u32,
    // Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
    // keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
    #[allow(dead_code)]
    pub(crate) is_unsafe: bool,
}

/// Positivity check result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum PositivityResult {
    StrictlyPositive,
    NonPositive { offender: Name, location: String },
}

/// Specification for a generated recursor.
#[derive(Debug, Clone)]
pub(crate) struct RecursorSpec {
    pub(crate) val: RecursorVal,
}

/// Result of mutual inductive elaboration.
#[derive(Debug, Clone)]
pub(crate) struct MutualIndResult {
    pub(crate) decl: InductiveDecl,
    pub(crate) inductive_vals: Vec<InductiveVal>,
    pub(crate) constructor_vals: Vec<ConstructorVal>,
    pub(crate) recursor_specs: Vec<RecursorSpec>,
    pub(crate) large_elim: bool,
}

// --- Helpers ---

/// Convert elaboration-level constructor info to kernel Constructor.
fn to_kernel_ctor(c: &ConstructorInfo) -> Constructor {
    Constructor {
        name: c.name.clone(),
        type_: c.type_expr.clone(),
    }
}

fn to_kernel_ctors(ctors: &[ConstructorInfo]) -> Vec<Constructor> {
    ctors.iter().map(to_kernel_ctor).collect()
}

/// Extract the universe level from a type expression (strips Pi telescope).
fn extract_sort_level(expr: &Expr) -> Level {
    let mut current = expr;
    while let clean_kernel::ExprKind::Pi(_, _, body) = current.kind() {
        current = body;
    }
    match current.kind() {
        clean_kernel::ExprKind::Sort(level) => level.clone(),
        _ => Level::zero(),
    }
}

/// Check if any constructor argument mentions any of the given names.
fn check_is_recursive(all_names: &[Name], constructors: &[Constructor]) -> bool {
    constructors.iter().any(|ctor| {
        let mut current = &ctor.type_;
        while let clean_kernel::ExprKind::Pi(_, domain, body) = current.kind() {
            if all_names.iter().any(|n| mentions_name(domain, n)) {
                return true;
            }
            current = body;
        }
        false
    })
}

/// Check if any constructor has a function-typed argument mentioning a mutual name.
fn check_is_reflexive(all_names: &[Name], constructors: &[Constructor]) -> bool {
    constructors.iter().any(|ctor| {
        let mut current = &ctor.type_;
        while let clean_kernel::ExprKind::Pi(_, domain, body) = current.kind() {
            if let clean_kernel::ExprKind::Pi(_, inner_dom, inner_cod) = domain.kind() {
                if all_names
                    .iter()
                    .any(|n| mentions_name(inner_dom, n) || mentions_name(inner_cod, n))
                {
                    return true;
                }
            }
            current = body;
        }
        false
    })
}

/// Compute which constructor fields (past params) are recursive.
fn compute_recursive_fields(ctor_type: &Expr, num_params: u32, all_names: &[Name]) -> Vec<bool> {
    let mut fields = Vec::new();
    let mut current = ctor_type;
    let mut idx = 0u32;
    while let clean_kernel::ExprKind::Pi(_, domain, body) = current.kind() {
        if idx >= num_params {
            fields.push(all_names.iter().any(|n| mentions_name(domain, n)));
        }
        current = body;
        idx += 1;
    }
    fields
}

// --- Validation ---

/// Validate well-formedness: non-empty, within limits, no duplicate names.
pub(crate) fn validate_mutual_block(
    block: &MutualInductiveBlock,
    config: &MutualIndConfig,
) -> Result<(), ElabError> {
    if block.types.is_empty() {
        return Err(ElabError::NotImplemented(
            "empty mutual inductive block".into(),
        ));
    }
    if block.types.len() > config.max_mutual_types {
        return Err(ElabError::Unsupported {
            feature: format!(
                "mutual inductive block with {} types exceeds limit of {}",
                block.types.len(),
                config.max_mutual_types
            ),
        });
    }
    let mut type_names = HashSet::new();
    for ty in &block.types {
        if !type_names.insert(&ty.name) {
            return Err(ElabError::Unsupported {
                feature: format!("duplicate inductive type name: {}", ty.name),
            });
        }
    }
    let mut ctor_names = HashSet::new();
    for ty in &block.types {
        for ctor in &ty.constructors {
            if !ctor_names.insert(&ctor.name) {
                return Err(ElabError::Unsupported {
                    feature: format!("duplicate constructor name: {}", ctor.name),
                });
            }
        }
    }
    Ok(())
}

// --- Positivity ---

/// Check strict positivity for one type against its constructors.
pub(crate) fn check_strict_positivity(
    type_name: &Name,
    constructors: &[Constructor],
    mutual_names: &[&Name],
    num_params: u32,
) -> PositivityResult {
    for ctor in constructors {
        if let Err(InductiveError::NonPositive(offender, _)) =
            inductive::check_positivity(type_name, &ctor.type_, num_params, mutual_names)
        {
            return PositivityResult::NonPositive {
                offender,
                location: format!("constructor {}", ctor.name),
            };
        }
    }
    PositivityResult::StrictlyPositive
}

/// Check strict positivity for all types in a mutual block.
pub(crate) fn check_all_positivity(block: &MutualInductiveBlock) -> Result<(), ElabError> {
    let all_names: Vec<&Name> = block.types.iter().map(|t| &t.name).collect();
    for ty in &block.types {
        let kernel_ctors = to_kernel_ctors(&ty.constructors);
        if let PositivityResult::NonPositive { offender, location } =
            check_strict_positivity(&ty.name, &kernel_ctors, &all_names, block.num_params)
        {
            return Err(ElabError::Unsupported {
                feature: format!("non-positive occurrence of {offender} in {location}"),
            });
        }
    }
    Ok(())
}

// --- Universe computation ---

/// Compute the result universe as `max` of all type former universes.
pub(crate) fn compute_result_universe(types: &[InductiveTypeInfo]) -> Level {
    match types.len() {
        0 => Level::zero(),
        1 => extract_sort_level(&types[0].type_expr),
        _ => {
            let mut result = extract_sort_level(&types[0].type_expr);
            for ty in &types[1..] {
                result = Level::max(result, extract_sort_level(&ty.type_expr));
            }
            result
        }
    }
}

// --- Large elimination ---

/// Check if the mutual block allows large elimination.
pub(crate) fn can_eliminate_to_type(block: &MutualInductiveBlock, env: &Environment) -> bool {
    if block.types.is_empty() {
        return false;
    }
    // Mutual Prop inductives never allow large elimination.
    if block.types.len() > 1 {
        if block
            .types
            .iter()
            .any(|ty| extract_sort_level(&ty.type_expr) == Level::zero())
        {
            return false;
        }
        return true;
    }
    // Single type: delegate to kernel.
    let ty = &block.types[0];
    let kernel_ctors = to_kernel_ctors(&ty.constructors);
    inductive::allows_large_elim(env, &ty.type_expr, &kernel_ctors, block.num_params, 1)
}

// --- Recursor generation ---

/// Generate recursor specs for each type in the mutual block.
pub(crate) fn generate_mutual_recursors(
    block: &MutualInductiveBlock,
    env: &Environment,
) -> Vec<RecursorSpec> {
    let n_types = block.types.len();
    let all_names: Vec<Name> = block.types.iter().map(|t| t.name.clone()).collect();
    let total_minors: u32 = block
        .types
        .iter()
        .map(|t| t.constructors.len() as u32)
        .sum();
    let large_elim = can_eliminate_to_type(block, env);

    block
        .types
        .iter()
        .map(|ty| {
            let rec_name = Name::from_string(&format!("{}.rec", ty.name));
            let total_binders = count_pi_args(&ty.type_expr);
            let num_indices = total_binders.saturating_sub(block.num_params);

            let rules: Vec<RecursorRule> = ty
                .constructors
                .iter()
                .map(|ctor| {
                    let num_fields =
                        count_pi_args(&ctor.type_expr).saturating_sub(block.num_params);
                    RecursorRule {
                        constructor_name: ctor.name.clone(),
                        num_fields,
                        recursive_fields: compute_recursive_fields(
                            &ctor.type_expr,
                            block.num_params,
                            &all_names,
                        ),
                        rhs: Expr::sort(Level::zero()), // placeholder
                    }
                })
                .collect();

            let motive_u = if large_elim {
                Level::param(Name::from_string("u_motive"))
            } else {
                Level::zero()
            };

            // Build placeholder recursor type with correct binder count.
            let total = block.num_params + n_types as u32 + total_minors + num_indices + 1;
            let mut rec_type = Expr::sort(motive_u.clone());
            for _ in 0..total {
                rec_type = Expr::pi(BinderInfo::Default, Expr::sort(Level::zero()), rec_type);
            }

            let mut level_params = block.universe_params.clone();
            if large_elim {
                level_params.push(Name::from_string("u_motive"));
            }

            RecursorSpec {
                val: RecursorVal {
                    name: rec_name,
                    arg_order: RecursorArgOrder::MajorAfterMinors,
                    level_params,
                    type_: rec_type,
                    inductive_name: ty.name.clone(),
                    num_params: block.num_params,
                    num_indices,
                    num_motives: n_types as u32,
                    num_minors: total_minors,
                    rules,
                    is_k: false,
                },
            }
        })
        .collect()
}

// --- Full pipeline ---

/// Elaborate a mutual inductive block: validate, positivity, universes, recursors.
pub(crate) fn elaborate_mutual_inductive(
    block: &MutualInductiveBlock,
    env: &Environment,
    config: &MutualIndConfig,
) -> Result<MutualIndResult, ElabError> {
    validate_mutual_block(block, config)?;
    if config.check_positivity {
        check_all_positivity(block)?;
    }
    let _result_universe = compute_result_universe(&block.types);

    let kernel_types: Vec<InductiveType> = block
        .types
        .iter()
        .map(|ty| InductiveType {
            name: ty.name.clone(),
            type_: ty.type_expr.clone(),
            constructors: to_kernel_ctors(&ty.constructors),
        })
        .collect();

    let decl = InductiveDecl {
        level_params: block.universe_params.clone(),
        num_params: block.num_params,
        types: kernel_types,
    };

    let large_elim = can_eliminate_to_type(block, env);
    let all_names: Vec<Name> = block.types.iter().map(|t| t.name.clone()).collect();

    let inductive_vals: Vec<InductiveVal> = block
        .types
        .iter()
        .map(|ty| {
            let kernel_ctors = to_kernel_ctors(&ty.constructors);
            let num_indices = count_pi_args(&ty.type_expr).saturating_sub(block.num_params);
            InductiveVal {
                name: ty.name.clone(),
                level_params: block.universe_params.clone(),
                type_: ty.type_expr.clone(),
                num_params: block.num_params,
                num_indices,
                all_names: all_names.clone(),
                constructor_names: ty.constructors.iter().map(|c| c.name.clone()).collect(),
                is_recursive: check_is_recursive(&all_names, &kernel_ctors),
                is_reflexive: check_is_reflexive(&all_names, &kernel_ctors),
                is_large_elim: large_elim,
                is_nested: false,
            }
        })
        .collect();

    let mut constructor_vals = Vec::new();
    for ty in &block.types {
        for (idx, ctor) in ty.constructors.iter().enumerate() {
            let num_fields = count_pi_args(&ctor.type_expr).saturating_sub(block.num_params);
            constructor_vals.push(ConstructorVal {
                name: ctor.name.clone(),
                inductive_name: ty.name.clone(),
                level_params: block.universe_params.clone(),
                type_: ctor.type_expr.clone(),
                num_params: block.num_params,
                num_fields,
                constructor_idx: idx as u32,
            });
        }
    }

    let recursor_specs = if config.generate_recursors {
        generate_mutual_recursors(block, env)
    } else {
        Vec::new()
    };

    Ok(MutualIndResult {
        decl,
        inductive_vals,
        constructor_vals,
        recursor_specs,
        large_elim,
    })
}

#[cfg(test)]
#[path = "mutual_inductive_tests.rs"]
mod tests;
