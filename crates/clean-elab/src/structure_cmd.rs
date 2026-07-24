// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structure and class command elaboration.
//!
//! Generates inductive types with projections from structure definitions.

use crate::error::ElabError;
use crate::structure_extend::flatten_parents;
use clean_kernel::env::KernelClassInfo;
use clean_kernel::{
    BinderInfo, Constructor, Declaration, Environment, Expr, InductiveDecl, InductiveType, Level,
    Name, TypeChecker,
};
use std::collections::HashSet;

#[derive(Clone, Debug)]
pub(crate) struct StructField {
    pub(crate) name: Name,
    pub(crate) type_: Expr,
    pub(crate) default_value: Option<Expr>,
    pub(crate) binder_info: BinderInfo,
    pub(crate) auto_param: bool,
}

#[derive(Clone, Debug)]
pub(crate) struct StructDef {
    pub(crate) name: Name,
    pub(crate) universe_params: Vec<Name>,
    pub(crate) params: Vec<(Name, Expr, BinderInfo)>,
    pub(crate) fields: Vec<StructField>,
    pub(crate) parents: Vec<Name>,
    pub(crate) is_class: bool,
}

fn kernel_registration_failed(
    operation: impl Into<String>,
    error: clean_kernel::EnvError,
) -> ElabError {
    match error {
        clean_kernel::EnvError::TypeCheckFailed { name, source } => ElabError::KernelCheckFailed {
            name,
            detail: source.to_string(),
        },
        clean_kernel::EnvError::TheoremTypeNotProp { name, sort } => ElabError::KernelCheckFailed {
            name,
            detail: format!("type must be Prop, inferred sort {sort:?}"),
        },
        other => ElabError::KernelRegistrationFailed {
            operation: operation.into(),
            detail: other.to_string(),
        },
    }
}

fn to_u32(value: usize) -> u32 {
    u32::try_from(value).unwrap_or(u32::MAX)
}

fn mk_levels(universe_params: &[Name]) -> Vec<Level> {
    universe_params
        .iter()
        .map(|param| Level::param(param.clone()))
        .collect()
}

fn mk_projection_name(struct_name: &Name, field_name: &Name) -> Name {
    match field_name.last_component() {
        Some(component) => Name::append(struct_name, &component),
        None => Name::append(struct_name, &field_name.to_string()),
    }
}

fn mk_struct_const_with_params(
    struct_name: &Name,
    universe_params: &[Name],
    param_count: usize,
    extra_binders: usize,
) -> Expr {
    let mut struct_type = Expr::const_(struct_name.clone(), mk_levels(universe_params));
    for param_idx in 0..param_count {
        let bvar_idx = to_u32(extra_binders + param_count - 1 - param_idx);
        struct_type = Expr::app(struct_type, Expr::bvar(bvar_idx));
    }
    struct_type
}

fn parent_field_name(parent: &Name) -> Name {
    let parent_leaf = parent
        .last_component()
        .unwrap_or_else(|| parent.to_string());
    Name::from_string(&format!("to{parent_leaf}"))
}

fn is_parent_link_field(field: &Name, env: &Environment) -> bool {
    let Some(leaf) = field.last_component() else {
        return false;
    };
    let Some(suffix) = leaf.strip_prefix("to") else {
        return false;
    };
    if suffix.is_empty() {
        return false;
    }
    let exact = Name::from_string(suffix);
    if env.get_structure_field_names(&exact).is_some() {
        return true;
    }
    env.constants().any(|constant| {
        env.get_structure_field_names(&constant.name).is_some()
            && constant.name.last_component().as_deref() == Some(suffix)
    })
}

fn mk_parent_struct_type(
    parent: &Name,
    parent_param_count: usize,
    parent_universe_params: &[Name],
    child_universe_params: &[Name],
    child_param_count: usize,
) -> Expr {
    let levels: Vec<Level> = parent_universe_params
        .iter()
        .enumerate()
        .map(|(idx, parent_param)| {
            Level::param(
                child_universe_params
                    .get(idx)
                    .cloned()
                    .unwrap_or_else(|| parent_param.clone()),
            )
        })
        .collect();
    let mut expr = Expr::const_(parent.clone(), levels);
    for param_idx in 0..parent_param_count.min(child_param_count) {
        expr = Expr::app(expr, Expr::bvar(to_u32(child_param_count - 1 - param_idx)));
    }
    expr
}

fn merge_field_by_name(fields: &mut Vec<StructField>, field: StructField) {
    if let Some(existing) = fields
        .iter_mut()
        .find(|existing| existing.name == field.name)
    {
        *existing = field;
    } else {
        fields.push(field);
    }
}

fn expand_parent_fields(def: &StructDef, env: &Environment) -> Result<Vec<StructField>, ElabError> {
    if def.parents.is_empty() {
        return Ok(def.fields.clone());
    }

    let mut fields = Vec::new();
    let mut added_parent_links = HashSet::new();

    for parent in &def.parents {
        let parent_fields = flatten_parents(std::slice::from_ref(parent), env)?;
        let parent_inductive =
            env.get_inductive(parent)
                .ok_or_else(|| ElabError::UnknownStruct {
                    name: parent.to_string(),
                })?;

        let link_name = parent_field_name(parent);
        if added_parent_links.insert(link_name.clone()) {
            merge_field_by_name(
                &mut fields,
                StructField {
                    name: link_name,
                    type_: mk_parent_struct_type(
                        parent,
                        parent_inductive.num_params as usize,
                        &parent_inductive.level_params,
                        &def.universe_params,
                        def.params.len(),
                    ),
                    default_value: None,
                    binder_info: BinderInfo::Default,
                    auto_param: false,
                },
            );
        }

        for field in parent_fields {
            if !is_parent_link_field(&field.name, env) {
                merge_field_by_name(&mut fields, field);
            }
        }
    }

    for field in &def.fields {
        merge_field_by_name(&mut fields, field.clone());
    }

    Ok(fields)
}

fn field_sort_level_syntax(field_type: &Expr) -> Option<Level> {
    match field_type.kind() {
        clean_kernel::ExprKind::Sort(level) => Some(Level::succ(level.clone())),
        _ => None,
    }
}

fn structure_result_level(fields: &[StructField], env: &Environment) -> Level {
    let tc = TypeChecker::new(env);
    fields
        .iter()
        .fold(Level::succ(Level::zero()), |level, field| {
            let field_sort = tc
                .infer_sort(&field.type_)
                .ok()
                .or_else(|| field_sort_level_syntax(&field.type_));
            match field_sort {
                Some(field_sort) => Level::max(level, field_sort),
                None => level,
            }
        })
}

fn mk_projection_field_type(struct_name: &Name, field_idx: usize, field_type: &Expr) -> Expr {
    // Insert the structure argument between the params and earlier field binders,
    // then replace earlier field references with the corresponding projections.
    let lifted = field_type.lift_from(to_u32(field_idx), 1);
    if field_idx == 0 {
        return lifted;
    }

    let replacements: Vec<Expr> = (0..field_idx)
        .rev()
        .map(|earlier_idx| Expr::proj(struct_name.clone(), to_u32(earlier_idx), Expr::bvar(0)))
        .collect();

    lifted.instantiate_rev(&replacements)
}

pub(crate) fn elaborate_structure(
    def: &StructDef,
    env: &mut Environment,
) -> Result<Vec<Declaration>, ElabError> {
    let fields = expand_parent_fields(def, env)?;
    let num_params = u32::try_from(def.params.len()).map_err(|_| ElabError::Unsupported {
        feature: format!("structure {} has too many parameters", def.name),
    })?;

    let mut structure_type = Expr::sort(structure_result_level(&fields, env));
    for (_, param_type, binder_info) in def.params.iter().rev() {
        structure_type = Expr::pi(*binder_info, param_type.clone(), structure_type);
    }

    let ctor_name = Name::append(&def.name, "mk");
    let mut ctor_type = mk_struct_const_with_params(
        &def.name,
        &def.universe_params,
        def.params.len(),
        fields.len(),
    );
    for field in fields.iter().rev() {
        ctor_type = Expr::pi(field.binder_info, field.type_.clone(), ctor_type);
    }
    for (_, param_type, _) in def.params.iter().rev() {
        ctor_type = Expr::pi(BinderInfo::Implicit, param_type.clone(), ctor_type);
    }

    let decl = InductiveDecl {
        level_params: def.universe_params.clone(),
        num_params,
        types: vec![InductiveType {
            name: def.name.clone(),
            type_: structure_type,
            constructors: vec![Constructor {
                name: ctor_name,
                type_: ctor_type,
            }],
        }],
    };

    env.add_inductive(decl).map_err(|error| {
        kernel_registration_failed(format!("add_inductive {}", def.name), error)
    })?;

    let field_names: Vec<Name> = fields.iter().map(|field| field.name.clone()).collect();
    env.register_structure_fields(def.name.clone(), field_names)
        .map_err(|error| {
            kernel_registration_failed(format!("register_structure_fields {}", def.name), error)
        })?;

    // Propagate field defaults into the kernel's elaborator-side metadata
    // store. These are not consulted by type checking; they exist so that
    // inheritance resolution can pull a parent's defaults into a child.
    for field in &fields {
        if let Some(default) = &field.default_value {
            env.register_structure_field_default(
                def.name.clone(),
                field.name.clone(),
                default.clone(),
            );
        }
    }

    let projections =
        generate_projections(&def.name, &def.universe_params, &def.params, &fields, env);

    if def.is_class {
        env.register_class(KernelClassInfo {
            name: def.name.clone(),
            num_params: def.params.len(),
            out_params: Vec::new(),
            semi_out_params: Vec::new(),
        });
    }

    Ok(projections)
}

pub(crate) fn generate_projections(
    struct_name: &Name,
    universe_params: &[Name],
    params: &[(Name, Expr, BinderInfo)],
    fields: &[StructField],
    _env: &Environment,
) -> Vec<Declaration> {
    fields
        .iter()
        .enumerate()
        .map(|(field_idx, field)| {
            let proj_name = mk_projection_name(struct_name, &field.name);
            let proj_idx = to_u32(field_idx);

            let struct_type =
                mk_struct_const_with_params(struct_name, universe_params, params.len(), 0);
            let field_type = mk_projection_field_type(struct_name, field_idx, &field.type_);

            let mut proj_type = Expr::pi(BinderInfo::Default, struct_type.clone(), field_type);
            for (_, param_type, _) in params.iter().rev() {
                proj_type = Expr::pi(BinderInfo::Implicit, param_type.clone(), proj_type);
            }

            let mut proj_value = Expr::lam(
                BinderInfo::Default,
                struct_type,
                Expr::proj(struct_name.clone(), proj_idx, Expr::bvar(0)),
            );
            for (_, param_type, _) in params.iter().rev() {
                proj_value = Expr::lam(BinderInfo::Implicit, param_type.clone(), proj_value);
            }

            Declaration::Definition {
                name: proj_name,
                level_params: universe_params.to_vec(),
                type_: proj_type,
                value: proj_value,
                is_reducible: true,
            }
        })
        .collect()
}
