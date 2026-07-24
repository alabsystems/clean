// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended structure extension elaboration.
//!
//! Full `extends` pipeline: field resolution, diamond detection, conflict
//! resolution, default propagation, projection/coercion/eta generation.

use crate::structure_cmd::{generate_projections, StructField};
use crate::structure_extend::{detect_circular_extension, flatten_parents};
use crate::structure_inherit::{FieldInfo, InheritError, InheritanceResolver};
use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Level, Name};
use std::collections::{HashMap, HashSet};
use thiserror::Error;

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

// ---------------------------------------------------------------------------
// Error
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Error)]
#[non_exhaustive]
pub(crate) enum ExtendExtError {
    #[error("inheritance error: {0}")]
    Inherit(#[from] InheritError),
    #[error("diamond inheritance conflict for field `{field}` via ancestors {ancestors:?}")]
    DiamondConflict { field: Name, ancestors: Vec<Name> },
    #[error("circular extension: {detail}")]
    CircularExtension { detail: String },
    #[error("unknown parent structure `{name}`")]
    UnknownParent { name: Name },
    #[error("extension config violation: {detail}")]
    ConfigViolation { detail: String },
}

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub(crate) struct ExtendConfig {
    pub(crate) max_depth: usize,
    pub(crate) strict_diamond: bool,
    pub(crate) propagate_defaults: bool,
    pub(crate) generate_eta: bool,
}

impl Default for ExtendConfig {
    fn default() -> Self {
        Self {
            max_depth: 64,
            strict_diamond: false,
            propagate_defaults: true,
            generate_eta: true,
        }
    }
}

// ---------------------------------------------------------------------------
// Diagnostics
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ExtendDiagnostic {
    pub(crate) kind: DiagnosticKind,
    pub(crate) message: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DiagnosticKind {
    DiamondDetected,
    FieldOverride,
    DefaultPropagated,
    DepthWarning,
    CoercionGenerated,
}

// ---------------------------------------------------------------------------
// Result types
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub(crate) struct ExtendExtResult {
    pub(crate) fields: Vec<ResolvedField>,
    pub(crate) projections: Vec<Declaration>,
    pub(crate) coercions: Vec<Declaration>,
    pub(crate) diamonds: Vec<DiamondInfo>,
    pub(crate) eta_expansions: Vec<Declaration>,
    pub(crate) diagnostics: Vec<ExtendDiagnostic>,
}

#[derive(Debug, Clone)]
pub(crate) struct ResolvedField {
    pub(crate) name: Name,
    pub(crate) type_expr: Expr,
    pub(crate) default_value: Option<Expr>,
    pub(crate) binder_info: BinderInfo,
    pub(crate) origin: FieldOrigin,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum FieldOrigin {
    Own,
    Inherited { parent: Name },
    Diamond { parents: Vec<Name> },
    Override { original_parent: Name },
}

#[derive(Debug, Clone)]
pub(crate) struct DiamondInfo {
    pub(crate) ancestor: Name,
    pub(crate) via_parents: Vec<Name>,
    pub(crate) shared_fields: Vec<Name>,
}

// ---------------------------------------------------------------------------
// Pipeline
// ---------------------------------------------------------------------------

/// Main entry point for `extends` clause processing.
pub(crate) fn elaborate_extend_ext(
    struct_name: &Name,
    universe_params: &[Name],
    params: &[(Name, Expr, BinderInfo)],
    own_fields: &[StructField],
    parents: &[Name],
    env: &Environment,
    config: &ExtendConfig,
) -> Result<ExtendExtResult, ExtendExtError> {
    let mut diagnostics = Vec::new();
    if parents.is_empty() {
        return Ok(no_parents_result(own_fields));
    }

    detect_circular_extension(struct_name, parents, env).map_err(|e| {
        ExtendExtError::CircularExtension {
            detail: e.to_string(),
        }
    })?;

    let resolver = InheritanceResolver::new(env);
    let own_field_infos: Vec<FieldInfo> = own_fields
        .iter()
        .map(|f| FieldInfo {
            name: f.name.clone(),
            type_expr: f.type_.clone(),
            default_value: f.default_value.clone(),
            is_inherited: false,
            source_struct: None,
        })
        .collect();
    let inheritance = resolver.resolve_inheritance(struct_name, parents, &own_field_infos)?;

    let diamonds = detect_diamonds(parents, env, config, &mut diagnostics)?;
    let fields = build_resolved_fields(
        &inheritance.all_fields,
        own_fields,
        parents,
        &diamonds,
        config,
        &mut diagnostics,
    );

    let struct_fields: Vec<StructField> = fields
        .iter()
        .map(|f| StructField {
            name: f.name.clone(),
            type_: f.type_expr.clone(),
            default_value: f.default_value.clone(),
            binder_info: f.binder_info,
            auto_param: false,
        })
        .collect();

    let projections =
        generate_projections(struct_name, universe_params, params, &struct_fields, env);
    let coercions = generate_coercions_from_resolved_fields(
        struct_name,
        universe_params,
        params,
        parents,
        &fields,
        env,
    );
    for coe in &coercions {
        if let Declaration::Definition { name, .. } = coe {
            diagnostics.push(ExtendDiagnostic {
                kind: DiagnosticKind::CoercionGenerated,
                message: format!("generated coercion {name}"),
            });
        }
    }

    let eta_expansions = if config.generate_eta {
        generate_eta_expansions(struct_name, universe_params, params, parents, &fields, env)
    } else {
        Vec::new()
    };

    Ok(ExtendExtResult {
        fields,
        projections,
        coercions,
        diamonds,
        eta_expansions,
        diagnostics,
    })
}

// ---------------------------------------------------------------------------
// Diamond detection
// ---------------------------------------------------------------------------

fn detect_diamonds(
    parents: &[Name],
    env: &Environment,
    config: &ExtendConfig,
    diagnostics: &mut Vec<ExtendDiagnostic>,
) -> Result<Vec<DiamondInfo>, ExtendExtError> {
    if parents.len() < 2 {
        return Ok(Vec::new());
    }
    let mut ancestor_sources: HashMap<Name, Vec<Name>> = HashMap::new();
    for parent in parents {
        for ancestor in collect_ancestors(parent, env, config.max_depth) {
            ancestor_sources
                .entry(ancestor)
                .or_default()
                .push(parent.clone());
        }
    }
    let mut diamonds = Vec::new();
    for (ancestor, via_parents) in &ancestor_sources {
        if via_parents.len() < 2 {
            continue;
        }
        let shared_fields = env
            .get_structure_field_names(ancestor)
            .map(|n| n.to_vec())
            .unwrap_or_default();
        if config.strict_diamond && !shared_fields.is_empty() {
            return Err(ExtendExtError::DiamondConflict {
                field: shared_fields[0].clone(),
                ancestors: via_parents.clone(),
            });
        }
        diagnostics.push(ExtendDiagnostic {
            kind: DiagnosticKind::DiamondDetected,
            message: format!(
                "diamond: {} reachable via {:?}",
                ancestor,
                via_parents
                    .iter()
                    .map(|p| p.to_string())
                    .collect::<Vec<_>>()
            ),
        });
        diamonds.push(DiamondInfo {
            ancestor: ancestor.clone(),
            via_parents: via_parents.clone(),
            shared_fields,
        });
    }
    Ok(diamonds)
}

fn collect_ancestors(name: &Name, env: &Environment, max_depth: usize) -> HashSet<Name> {
    let mut ancestors = HashSet::new();
    let mut stack: Vec<(Name, usize)> = vec![(name.clone(), 0)];
    while let Some((current, depth)) = stack.pop() {
        if depth >= max_depth {
            continue;
        }
        let Some(field_names) = env.get_structure_field_names(&current) else {
            continue;
        };
        for field_name in field_names {
            if let Some(parent) = infer_parent_from_to_field(field_name, env) {
                if ancestors.insert(parent.clone()) {
                    stack.push((parent, depth + 1));
                }
            }
        }
    }
    ancestors
}

fn infer_parent_from_to_field(field: &Name, env: &Environment) -> Option<Name> {
    let leaf = field.last_component()?;
    let suffix = leaf.strip_prefix("to")?;
    if suffix.is_empty() {
        return None;
    }
    let candidate = Name::from_string(suffix);
    if env.get_structure_field_names(&candidate).is_some() {
        Some(candidate)
    } else {
        None
    }
}

fn parent_link_field_name(parent: &Name) -> Name {
    Name::from_string(&format!(
        "to{}",
        parent
            .last_component()
            .unwrap_or_else(|| parent.to_string())
    ))
}

fn generate_coercions_from_resolved_fields(
    child: &Name,
    child_universe_params: &[Name],
    child_params: &[(Name, Expr, BinderInfo)],
    parents: &[Name],
    fields: &[ResolvedField],
    env: &Environment,
) -> Vec<Declaration> {
    let child_levels = mk_levels(child_universe_params);
    let child_field_indices: HashMap<Name, u32> = fields
        .iter()
        .enumerate()
        .map(|(idx, field)| (field.name.clone(), to_u32(idx)))
        .collect();

    parents
        .iter()
        .filter_map(|parent| {
            let parent_inductive = env.get_inductive(parent)?;
            let parent_ctor_name = parent_inductive.constructor_names.first()?.clone();
            let parent_levels =
                mk_aligned_levels(&parent_inductive.level_params, child_universe_params);
            let parent_param_count = (parent_inductive.num_params as usize).min(child_params.len());

            let child_type = mk_const_with_params(child, &child_levels, child_params.len(), 0);
            let parent_type = mk_const_with_params(parent, &parent_levels, parent_param_count, 1);

            let value = if let Some(field_idx) =
                child_field_indices.get(&parent_link_field_name(parent))
            {
                Expr::proj(child.clone(), *field_idx, Expr::bvar(0))
            } else {
                let parent_fields = env.get_structure_field_names(parent)?;
                let mut value = Expr::const_(parent_ctor_name, parent_levels.clone());
                value = Expr::apps(
                    value,
                    (0..parent_param_count)
                        .map(|param_idx| Expr::bvar(to_u32(parent_param_count - param_idx))),
                );

                for field_name in parent_fields {
                    let field_idx = *child_field_indices.get(field_name)?;
                    value = Expr::app(value, Expr::proj(child.clone(), field_idx, Expr::bvar(0)));
                }
                value
            };

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

// ---------------------------------------------------------------------------
// Field resolution
// ---------------------------------------------------------------------------

fn build_resolved_fields(
    all_fields: &[FieldInfo],
    own_fields: &[StructField],
    parents: &[Name],
    diamonds: &[DiamondInfo],
    config: &ExtendConfig,
    diagnostics: &mut Vec<ExtendDiagnostic>,
) -> Vec<ResolvedField> {
    let own_names: HashSet<&Name> = own_fields.iter().map(|f| &f.name).collect();
    let own_defaults: HashMap<&Name, Option<&Expr>> = own_fields
        .iter()
        .map(|f| (&f.name, f.default_value.as_ref()))
        .collect();

    let diamond_fields: HashMap<&Name, Vec<Name>> = {
        let mut map: HashMap<&Name, Vec<Name>> = HashMap::new();
        for di in diamonds {
            for field in &di.shared_fields {
                map.entry(field)
                    .or_default()
                    .extend(di.via_parents.iter().cloned());
            }
        }
        map
    };

    let fallback = || parents.first().cloned().unwrap_or_else(Name::anon);

    all_fields
        .iter()
        .map(|field| {
            let origin = if own_names.contains(&field.name) && field.is_inherited {
                let parent = field.source_struct.clone().unwrap_or_else(&fallback);
                diagnostics.push(ExtendDiagnostic {
                    kind: DiagnosticKind::FieldOverride,
                    message: format!("field `{}` overrides inherited from {}", field.name, parent),
                });
                FieldOrigin::Override {
                    original_parent: parent,
                }
            } else if let Some(via) = diamond_fields.get(&field.name) {
                FieldOrigin::Diamond {
                    parents: via.clone(),
                }
            } else if field.is_inherited {
                FieldOrigin::Inherited {
                    parent: field.source_struct.clone().unwrap_or_else(&fallback),
                }
            } else {
                FieldOrigin::Own
            };

            let default_value = if let Some(Some(own_def)) = own_defaults.get(&field.name) {
                Some((*own_def).clone())
            } else if config.propagate_defaults {
                if let Some(ref dv) = field.default_value {
                    diagnostics.push(ExtendDiagnostic {
                        kind: DiagnosticKind::DefaultPropagated,
                        message: format!("propagated default for field `{}`", field.name),
                    });
                    Some(dv.clone())
                } else {
                    None
                }
            } else {
                None
            };

            ResolvedField {
                name: field.name.clone(),
                type_expr: field.type_expr.clone(),
                default_value,
                binder_info: BinderInfo::Default,
                origin,
            }
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Eta expansion
// ---------------------------------------------------------------------------

fn generate_eta_expansions(
    struct_name: &Name,
    universe_params: &[Name],
    params: &[(Name, Expr, BinderInfo)],
    parents: &[Name],
    fields: &[ResolvedField],
    _env: &Environment,
) -> Vec<Declaration> {
    let levels: Vec<Level> = universe_params
        .iter()
        .map(|p| Level::param(p.clone()))
        .collect();
    parents
        .iter()
        .map(|parent| {
            let leaf = parent
                .last_component()
                .unwrap_or_else(|| parent.to_string());
            let eta_name = Name::append(struct_name, &format!("eta{leaf}"));
            let struct_const = {
                let mut c = Expr::const_(struct_name.clone(), levels.clone());
                for i in 0..params.len() {
                    c = Expr::app(c, Expr::bvar((params.len() - 1 - i + 1) as u32));
                }
                c
            };
            let ctor_name = Name::append(struct_name, "mk");
            let mut body = Expr::const_(ctor_name, levels.clone());
            for i in 0..params.len() {
                body = Expr::app(body, Expr::bvar((params.len() - i) as u32));
            }
            for (idx, _) in fields.iter().enumerate() {
                body = Expr::app(
                    body,
                    Expr::proj(struct_name.clone(), idx as u32, Expr::bvar(0)),
                );
            }
            let mut value = Expr::lam(BinderInfo::Default, struct_const.clone(), body);
            let mut type_ = Expr::pi(
                BinderInfo::Default,
                struct_const.clone(),
                struct_const.clone(),
            );
            for (_, pt, _) in params.iter().rev() {
                value = Expr::lam(BinderInfo::Implicit, pt.clone(), value);
                type_ = Expr::pi(BinderInfo::Implicit, pt.clone(), type_);
            }
            Declaration::Definition {
                name: eta_name,
                level_params: universe_params.to_vec(),
                type_,
                value,
                is_reducible: true,
            }
        })
        .collect()
}

fn no_parents_result(own_fields: &[StructField]) -> ExtendExtResult {
    ExtendExtResult {
        fields: own_fields
            .iter()
            .map(|f| ResolvedField {
                name: f.name.clone(),
                type_expr: f.type_.clone(),
                default_value: f.default_value.clone(),
                binder_info: f.binder_info,
                origin: FieldOrigin::Own,
            })
            .collect(),
        projections: Vec::new(),
        coercions: Vec::new(),
        diamonds: Vec::new(),
        eta_expansions: Vec::new(),
        diagnostics: Vec::new(),
    }
}

/// Check if a set of parents introduces a diamond.
pub(crate) fn has_diamond(parents: &[Name], env: &Environment) -> bool {
    if parents.len() < 2 {
        return false;
    }
    let config = ExtendConfig::default();
    let mut diags = Vec::new();
    detect_diamonds(parents, env, &config, &mut diags)
        .map(|d| !d.is_empty())
        .unwrap_or(false)
}

/// Flatten all transitive parent fields, deduplicating by name.
pub(crate) fn flatten_all_parents(
    parents: &[Name],
    env: &Environment,
) -> Result<Vec<StructField>, ExtendExtError> {
    flatten_parents(parents, env).map_err(|e| ExtendExtError::CircularExtension {
        detail: e.to_string(),
    })
}

/// Return ancestors reachable from a structure's parents.
pub(crate) fn ancestor_set(parents: &[Name], env: &Environment) -> HashSet<Name> {
    let mut result = HashSet::new();
    for parent in parents {
        result.extend(collect_ancestors(parent, env, 64));
    }
    result
}
