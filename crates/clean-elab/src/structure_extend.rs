// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structure extension support for parent structure inheritance.

use crate::error::ElabError;
use crate::structure_cmd::StructField;
use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Level, Name};
use std::collections::{HashMap, HashSet};

fn to_u32(value: usize) -> u32 {
    u32::try_from(value).unwrap_or(u32::MAX)
}

fn mk_levels(universe_params: &[Name]) -> Vec<Level> {
    universe_params
        .iter()
        .map(|param| Level::param(param.clone()))
        .collect()
}

fn mk_aligned_levels(target_params: &[Name], source_params: &[Name]) -> Vec<Level> {
    target_params
        .iter()
        .enumerate()
        .map(|(idx, target)| {
            Level::param(
                source_params
                    .get(idx)
                    .cloned()
                    .unwrap_or_else(|| target.clone()),
            )
        })
        .collect()
}

fn mk_const_with_params(
    name: &Name,
    levels: &[Level],
    param_count: usize,
    extra_binders: usize,
) -> Expr {
    let mut expr = Expr::const_(name.clone(), levels.to_vec());
    for param_idx in 0..param_count {
        let bvar_idx = to_u32(extra_binders + param_count - 1 - param_idx);
        expr = Expr::app(expr, Expr::bvar(bvar_idx));
    }
    expr
}

fn collect_constructor_field_types(
    ctor_type: &Expr,
    num_params: usize,
    num_fields: usize,
) -> Vec<Expr> {
    let mut field_types = Vec::with_capacity(num_fields);
    let mut current = strip_n_pi(ctor_type, num_params);

    while field_types.len() < num_fields {
        match current.kind() {
            clean_kernel::ExprKind::Pi(_, domain, body) => {
                field_types.push((**domain).clone());
                current = body;
            }
            _ => break,
        }
    }

    field_types
}

fn infer_parent_from_field(field: &Name, env: &Environment) -> Option<Name> {
    let leaf = field.last_component()?;
    let suffix = leaf.strip_prefix("to")?;
    if suffix.is_empty() {
        return None;
    }

    let exact = Name::from_string(suffix);
    if env.get_structure_field_names(&exact).is_some() {
        return Some(exact);
    }

    env.constants()
        .map(|constant| constant.name.clone())
        .filter(|candidate| {
            env.get_structure_field_names(candidate).is_some()
                && candidate.last_component().as_deref() == Some(suffix)
        })
        .min_by_key(|candidate| candidate.to_string())
}

pub(crate) fn flatten_parents(
    parents: &[Name],
    env: &Environment,
) -> Result<Vec<StructField>, ElabError> {
    let mut flattened = Vec::new();
    let mut seen = HashSet::new();

    for parent in parents {
        let field_names =
            env.get_structure_field_names(parent)
                .ok_or_else(|| ElabError::UnknownStruct {
                    name: parent.to_string(),
                })?;
        let inductive = env
            .get_inductive(parent)
            .ok_or_else(|| ElabError::UnknownStruct {
                name: parent.to_string(),
            })?;
        let ctor_name =
            inductive
                .constructor_names
                .first()
                .ok_or_else(|| ElabError::UnknownStruct {
                    name: parent.to_string(),
                })?;
        let ctor = env
            .get_constructor(ctor_name)
            .ok_or_else(|| ElabError::UnknownStruct {
                name: parent.to_string(),
            })?;

        let field_types = collect_constructor_field_types(
            &ctor.type_,
            ctor.num_params as usize,
            ctor.num_fields as usize,
        );
        if field_names.len() != field_types.len() {
            return Err(ElabError::NotImplemented(format!(
                "structure extension metadata mismatch for {}",
                parent
            )));
        }

        for (field_name, field_type) in field_names.iter().zip(field_types) {
            if seen.insert(field_name.clone()) {
                flattened.push(StructField {
                    name: field_name.clone(),
                    type_: field_type,
                    default_value: None,
                    binder_info: BinderInfo::Default,
                    auto_param: false,
                });
            }
        }
    }

    Ok(flattened)
}

pub(crate) fn generate_parent_coercions(
    child: &Name,
    child_universe_params: &[Name],
    child_params: &[(Name, Expr, BinderInfo)],
    parents: &[Name],
    env: &Environment,
) -> Vec<Declaration> {
    let Some(child_field_names) = env.get_structure_field_names(child) else {
        return Vec::new();
    };

    let child_levels = mk_levels(child_universe_params);
    let child_field_indices: HashMap<Name, u32> = child_field_names
        .iter()
        .enumerate()
        .map(|(idx, field)| (field.clone(), to_u32(idx)))
        .collect();

    parents
        .iter()
        .filter_map(|parent| {
            let parent_fields = env.get_structure_field_names(parent)?;
            let parent_inductive = env.get_inductive(parent)?;
            let parent_ctor_name = parent_inductive.constructor_names.first()?.clone();
            let parent_levels =
                mk_aligned_levels(&parent_inductive.level_params, child_universe_params);

            let child_type = mk_const_with_params(child, &child_levels, child_params.len(), 0);
            let parent_type = mk_const_with_params(parent, &parent_levels, child_params.len(), 1);

            let mut value = Expr::const_(parent_ctor_name, parent_levels.clone());
            value = Expr::apps(
                value,
                (0..child_params.len())
                    .map(|param_idx| Expr::bvar(to_u32(child_params.len() - param_idx))),
            );

            for field_name in parent_fields {
                let field_idx = *child_field_indices.get(field_name)?;
                value = Expr::app(value, Expr::proj(child.clone(), field_idx, Expr::bvar(0)));
            }

            let mut type_ = Expr::pi(BinderInfo::Default, child_type.clone(), parent_type);
            let mut value = Expr::lam(BinderInfo::Default, child_type, value);

            for (_, param_type, _) in child_params.iter().rev() {
                type_ = Expr::pi(BinderInfo::Implicit, param_type.clone(), type_);
                value = Expr::lam(BinderInfo::Implicit, param_type.clone(), value);
            }

            Some(Declaration::Definition {
                name: Name::append(
                    child,
                    &format!(
                        "to{}",
                        parent
                            .last_component()
                            .unwrap_or_else(|| parent.to_string())
                    ),
                ),
                level_params: child_universe_params.to_vec(),
                type_,
                value,
                is_reducible: true,
            })
        })
        .collect()
}

pub(crate) fn detect_circular_extension(
    name: &Name,
    parents: &[Name],
    env: &Environment,
) -> Result<(), ElabError> {
    let mut stack: Vec<Name> = parents.to_vec();
    let mut visited = HashSet::new();

    while let Some(current) = stack.pop() {
        if &current == name {
            return Err(ElabError::NotImplemented(format!(
                "circular structure extension detected for {}",
                name
            )));
        }

        if !visited.insert(current.clone()) {
            continue;
        }

        let Some(field_names) = env.get_structure_field_names(&current) else {
            continue;
        };

        for field_name in field_names {
            if let Some(parent) = infer_parent_from_field(field_name, env) {
                if &parent == name {
                    return Err(ElabError::NotImplemented(format!(
                        "circular structure extension detected for {}",
                        name
                    )));
                }
                if !visited.contains(&parent) {
                    stack.push(parent);
                }
            }
        }
    }

    Ok(())
}

pub(crate) fn strip_n_pi(expr: &Expr, n: usize) -> &Expr {
    let mut current = expr;
    let mut remaining = n;

    while remaining > 0 {
        match current.kind() {
            clean_kernel::ExprKind::Pi(_, _, body) => {
                current = body;
                remaining -= 1;
            }
            _ => break,
        }
    }

    current
}
