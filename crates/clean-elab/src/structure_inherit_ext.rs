// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended structure inheritance elaboration.
//!
//! Builds on [`crate::structure_inherit`] with diamond resolution,
//! field override validation, default propagation, field renaming,
//! type class extension, eta expansion, and depth/cycle tracking.

use crate::structure_inherit::{
    structural_type_eq, FieldInfo, InheritError, InheritanceResolver, ProjectionInfo,
};
use clean_kernel::{BinderInfo, Environment, Expr, Level, Name};
use std::collections::{HashMap, HashSet};
use thiserror::Error;

// ---------------------------------------------------------------------------
// Error
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Error)]
#[non_exhaustive]
pub(crate) enum InheritExtError {
    #[error("base inheritance error: {0}")]
    Base(#[from] InheritError),
    #[error("field override type mismatch: `{field}` expected `{expected}`, got `{actual}`")]
    OverrideTypeMismatch {
        field: Name,
        expected: String,
        actual: String,
    },
    #[error("inheritance depth limit ({limit}) exceeded for `{name}`")]
    DepthLimitExceeded { name: Name, limit: usize },
    #[error("inheritance cycle detected involving `{name}`")]
    CycleDetected { name: Name },
    #[error("field rename conflict: `{new_name}` already exists")]
    RenameConflict { new_name: Name },
    #[error("diamond inheritance: field `{field}` from `{ancestor}` via {paths:?}")]
    DiamondConflict {
        field: Name,
        ancestor: Name,
        paths: Vec<Name>,
    },
}

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub(crate) struct InheritExtConfig {
    pub(crate) max_depth: usize,
    pub(crate) allow_diamond: bool,
    pub(crate) propagate_defaults: bool,
    pub(crate) generate_eta: bool,
    pub(crate) strict_overrides: bool,
}

impl Default for InheritExtConfig {
    fn default() -> Self {
        Self {
            max_depth: 64,
            allow_diamond: true,
            propagate_defaults: true,
            generate_eta: true,
            strict_overrides: false,
        }
    }
}

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

/// A rename mapping: rename a field from `original` to `renamed`.
#[derive(Debug, Clone)]
pub(crate) struct FieldRename {
    pub(crate) original: Name,
    pub(crate) renamed: Name,
}

/// A resolved field with extended provenance information.
#[derive(Debug, Clone)]
pub(crate) struct ExtFieldInfo {
    pub(crate) name: Name,
    pub(crate) type_expr: Expr,
    pub(crate) default_value: Option<Expr>,
    pub(crate) binder_info: BinderInfo,
    pub(crate) origin: ExtFieldOrigin,
}

/// Where an extended field originates from.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ExtFieldOrigin {
    Own,
    Inherited { parent: Name },
    Diamond { parents: Vec<Name>, ancestor: Name },
    Override { original_parent: Name },
    Renamed { original_name: Name, parent: Name },
}

/// Information about a detected diamond in the inheritance graph.
#[derive(Debug, Clone)]
pub(crate) struct DiamondRecord {
    pub(crate) ancestor: Name,
    pub(crate) paths: Vec<Name>,
    pub(crate) shared_fields: Vec<Name>,
}

/// Complete result of extended inheritance resolution.
#[derive(Debug, Clone)]
pub(crate) struct InheritExtResult {
    pub(crate) fields: Vec<ExtFieldInfo>,
    pub(crate) projections: Vec<ProjectionInfo>,
    pub(crate) diamonds: Vec<DiamondRecord>,
    pub(crate) depth: usize,
    pub(crate) tc_extensions: Vec<Name>,
}

// ---------------------------------------------------------------------------
// Extended resolver
// ---------------------------------------------------------------------------

pub(crate) struct InheritExtResolver<'a> {
    env: &'a Environment,
    config: InheritExtConfig,
}

impl<'a> InheritExtResolver<'a> {
    pub(crate) fn new(env: &'a Environment, config: InheritExtConfig) -> Self {
        Self { env, config }
    }

    pub(crate) fn with_defaults(env: &'a Environment) -> Self {
        Self::new(env, InheritExtConfig::default())
    }

    /// Main entry point: resolve extended inheritance.
    pub(crate) fn resolve(
        &self,
        struct_name: &Name,
        parent_names: &[Name],
        own_fields: &[FieldInfo],
        renames: &[FieldRename],
        tc_instances: &[Name],
    ) -> Result<InheritExtResult, InheritExtError> {
        if parent_names.is_empty() {
            return Ok(self.no_parents_result(own_fields, tc_instances));
        }
        let depth = self.compute_depth(parent_names)?;
        if depth >= self.config.max_depth {
            return Err(InheritExtError::DepthLimitExceeded {
                name: struct_name.clone(),
                limit: self.config.max_depth,
            });
        }
        self.check_cycles(struct_name, parent_names)?;

        let base = InheritanceResolver::new(self.env);
        let base_result = base.resolve_inheritance(struct_name, parent_names, own_fields)?;
        let inherited_fields: Vec<FieldInfo> = base_result
            .parents
            .iter()
            .flat_map(|parent| parent.fields.iter().cloned())
            .collect();

        let diamonds = self.detect_diamonds(parent_names)?;
        if !self.config.allow_diamond {
            for d in &diamonds {
                if !d.shared_fields.is_empty() {
                    return Err(InheritExtError::DiamondConflict {
                        field: d.shared_fields[0].clone(),
                        ancestor: d.ancestor.clone(),
                        paths: d.paths.clone(),
                    });
                }
            }
        }
        if self.config.strict_overrides {
            self.validate_overrides(own_fields, &inherited_fields)?;
        }
        let renamed_fields = self.apply_renames(&base_result.all_fields, renames)?;
        let fields = self.build_ext_fields(
            &renamed_fields,
            own_fields,
            &inherited_fields,
            parent_names,
            &diamonds,
            renames,
        );

        Ok(InheritExtResult {
            fields,
            projections: base_result.parent_projections,
            diamonds,
            depth: depth + 1,
            tc_extensions: tc_instances.to_vec(),
        })
    }

    fn compute_depth(&self, parent_names: &[Name]) -> Result<usize, InheritExtError> {
        let mut max_depth = 0usize;
        for parent in parent_names {
            max_depth = max_depth.max(self.depth_of(parent, &mut HashSet::new(), 0)?);
        }
        Ok(max_depth)
    }

    fn depth_of(
        &self,
        name: &Name,
        visited: &mut HashSet<Name>,
        current: usize,
    ) -> Result<usize, InheritExtError> {
        if current >= self.config.max_depth {
            return Err(InheritExtError::DepthLimitExceeded {
                name: name.clone(),
                limit: self.config.max_depth,
            });
        }
        if !visited.insert(name.clone()) {
            return Err(InheritExtError::CycleDetected { name: name.clone() });
        }
        let parent_names = self.parents_of(name);
        if parent_names.is_empty() {
            visited.remove(name);
            return Ok(current);
        }
        let mut max_d = current;
        for p in &parent_names {
            max_d = max_d.max(self.depth_of(p, visited, current + 1)?);
        }
        visited.remove(name);
        Ok(max_d)
    }

    fn parents_of(&self, name: &Name) -> Vec<Name> {
        let Some(field_names) = self.env.get_structure_field_names(name) else {
            return Vec::new();
        };
        field_names
            .iter()
            .filter_map(|f| {
                let leaf = f.last_component()?;
                let suffix = leaf.strip_prefix("to")?;
                if suffix.is_empty() {
                    return None;
                }
                let candidate = Name::from_string(suffix);
                if self.env.get_structure_field_names(&candidate).is_some() {
                    Some(candidate)
                } else {
                    None
                }
            })
            .collect()
    }

    fn check_cycles(
        &self,
        struct_name: &Name,
        parent_names: &[Name],
    ) -> Result<(), InheritExtError> {
        let mut visited = HashSet::new();
        let mut stack = parent_names.to_vec();
        while let Some(current) = stack.pop() {
            if &current == struct_name {
                return Err(InheritExtError::CycleDetected {
                    name: struct_name.clone(),
                });
            }
            if !visited.insert(current.clone()) {
                continue;
            }
            stack.extend(self.parents_of(&current));
        }
        Ok(())
    }

    fn detect_diamonds(
        &self,
        parent_names: &[Name],
    ) -> Result<Vec<DiamondRecord>, InheritExtError> {
        if parent_names.len() < 2 {
            return Ok(Vec::new());
        }
        let mut ancestor_sources: HashMap<Name, Vec<Name>> = HashMap::new();
        for parent in parent_names {
            for ancestor in self.collect_ancestors(parent) {
                ancestor_sources
                    .entry(ancestor)
                    .or_default()
                    .push(parent.clone());
            }
        }
        let mut diamonds = Vec::new();
        for (ancestor, paths) in &ancestor_sources {
            if paths.len() < 2 {
                continue;
            }
            let shared_fields = self
                .env
                .get_structure_field_names(ancestor)
                .map(|n| n.to_vec())
                .unwrap_or_default();
            diamonds.push(DiamondRecord {
                ancestor: ancestor.clone(),
                paths: paths.clone(),
                shared_fields,
            });
        }
        Ok(diamonds)
    }

    fn collect_ancestors(&self, name: &Name) -> HashSet<Name> {
        let mut ancestors = HashSet::new();
        let mut stack: Vec<(Name, usize)> = vec![(name.clone(), 0)];
        while let Some((current, depth)) = stack.pop() {
            if depth >= self.config.max_depth {
                continue;
            }
            for parent in self.parents_of(&current) {
                if ancestors.insert(parent.clone()) {
                    stack.push((parent, depth + 1));
                }
            }
        }
        ancestors
    }

    fn validate_overrides(
        &self,
        own_fields: &[FieldInfo],
        all_fields: &[FieldInfo],
    ) -> Result<(), InheritExtError> {
        let inherited_by_name: HashMap<&Name, &FieldInfo> = all_fields
            .iter()
            .filter(|f| f.is_inherited)
            .map(|f| (&f.name, f))
            .collect();
        for own in own_fields {
            if let Some(inherited) = inherited_by_name.get(&own.name) {
                if !structural_type_eq(&own.type_expr, &inherited.type_expr) {
                    return Err(InheritExtError::OverrideTypeMismatch {
                        field: own.name.clone(),
                        expected: format!("{:?}", inherited.type_expr),
                        actual: format!("{:?}", own.type_expr),
                    });
                }
            }
        }
        Ok(())
    }

    fn apply_renames(
        &self,
        fields: &[FieldInfo],
        renames: &[FieldRename],
    ) -> Result<Vec<FieldInfo>, InheritExtError> {
        let rename_map: HashMap<&Name, &Name> =
            renames.iter().map(|r| (&r.original, &r.renamed)).collect();
        let existing_names: HashSet<&Name> = fields.iter().map(|f| &f.name).collect();
        for rename in renames {
            if existing_names.contains(&rename.renamed) && !rename_map.contains_key(&rename.renamed)
            {
                return Err(InheritExtError::RenameConflict {
                    new_name: rename.renamed.clone(),
                });
            }
        }
        Ok(fields
            .iter()
            .map(|f| {
                if let Some(new_name) = rename_map.get(&f.name) {
                    FieldInfo {
                        name: (*new_name).clone(),
                        type_expr: f.type_expr.clone(),
                        default_value: f.default_value.clone(),
                        is_inherited: f.is_inherited,
                        source_struct: f.source_struct.clone(),
                    }
                } else {
                    f.clone()
                }
            })
            .collect())
    }

    fn build_ext_fields(
        &self,
        fields: &[FieldInfo],
        own_fields: &[FieldInfo],
        inherited_fields: &[FieldInfo],
        parent_names: &[Name],
        diamonds: &[DiamondRecord],
        renames: &[FieldRename],
    ) -> Vec<ExtFieldInfo> {
        let own_names: HashSet<&Name> = own_fields.iter().map(|f| &f.name).collect();
        let inherited_by_name: HashMap<&Name, &FieldInfo> = inherited_fields
            .iter()
            .map(|field| (&field.name, field))
            .collect();
        let rename_map: HashMap<&Name, &Name> =
            renames.iter().map(|r| (&r.original, &r.renamed)).collect();
        let diamond_fields = diamond_field_map(diamonds);
        let fallback = || parent_names.first().cloned().unwrap_or_else(Name::anon);

        fields
            .iter()
            .map(|f| {
                let origin = if rename_map.contains_key(&f.name)
                    || renames.iter().any(|r| r.renamed == f.name)
                {
                    let original = renames
                        .iter()
                        .find(|r| r.renamed == f.name)
                        .map(|r| r.original.clone())
                        .unwrap_or_else(|| f.name.clone());
                    ExtFieldOrigin::Renamed {
                        original_name: original,
                        parent: f.source_struct.clone().unwrap_or_else(&fallback),
                    }
                } else if own_names.contains(&f.name) && inherited_by_name.contains_key(&f.name) {
                    ExtFieldOrigin::Override {
                        original_parent: inherited_by_name
                            .get(&f.name)
                            .and_then(|field| field.source_struct.clone())
                            .unwrap_or_else(&fallback),
                    }
                } else if let Some((ancestor, paths)) = diamond_fields.get(&f.name) {
                    ExtFieldOrigin::Diamond {
                        parents: paths.clone(),
                        ancestor: (*ancestor).clone(),
                    }
                } else if f.is_inherited {
                    ExtFieldOrigin::Inherited {
                        parent: f.source_struct.clone().unwrap_or_else(&fallback),
                    }
                } else {
                    ExtFieldOrigin::Own
                };

                let default_value = if let Some(own) = own_fields.iter().find(|o| o.name == f.name)
                {
                    own.default_value.clone()
                } else if self.config.propagate_defaults {
                    f.default_value.clone()
                } else {
                    None
                };

                ExtFieldInfo {
                    name: f.name.clone(),
                    type_expr: f.type_expr.clone(),
                    default_value,
                    binder_info: BinderInfo::Default,
                    origin,
                }
            })
            .collect()
    }

    fn no_parents_result(
        &self,
        own_fields: &[FieldInfo],
        tc_instances: &[Name],
    ) -> InheritExtResult {
        InheritExtResult {
            fields: own_fields
                .iter()
                .map(|f| ExtFieldInfo {
                    name: f.name.clone(),
                    type_expr: f.type_expr.clone(),
                    default_value: f.default_value.clone(),
                    binder_info: BinderInfo::Default,
                    origin: ExtFieldOrigin::Own,
                })
                .collect(),
            projections: Vec::new(),
            diamonds: Vec::new(),
            depth: 0,
            tc_extensions: tc_instances.to_vec(),
        }
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn diamond_field_map<'d>(
    diamonds: &'d [DiamondRecord],
) -> HashMap<&'d Name, (&'d Name, Vec<Name>)> {
    let mut map: HashMap<&'d Name, (&'d Name, Vec<Name>)> = HashMap::new();
    for d in diamonds {
        for field in &d.shared_fields {
            map.entry(field).or_insert((&d.ancestor, d.paths.clone()));
        }
    }
    map
}

/// Generate eta expansion expression for inherited structure fields.
pub(crate) fn generate_eta_expansion(
    struct_name: &Name,
    universe_params: &[Name],
    fields: &[ExtFieldInfo],
) -> Expr {
    let levels: Vec<Level> = universe_params
        .iter()
        .map(|p| Level::param(p.clone()))
        .collect();
    let struct_const = Expr::const_(struct_name.clone(), levels.clone());
    let ctor_name = Name::append(struct_name, "mk");
    let mut body = Expr::const_(ctor_name, levels);
    for (idx, _) in fields.iter().enumerate() {
        body = Expr::app(
            body,
            Expr::proj(struct_name.clone(), idx as u32, Expr::bvar(0)),
        );
    }
    Expr::lam(BinderInfo::Default, struct_const.clone(), body)
}

/// Compute the transitive inheritance depth of a structure.
pub(crate) fn inheritance_depth(name: &Name, env: &Environment, max: usize) -> usize {
    let resolver = InheritExtResolver::with_defaults(env);
    let parents = resolver.parents_of(name);
    if parents.is_empty() {
        return 0;
    }
    let mut visited = HashSet::new();
    resolver.depth_of(name, &mut visited, 0).unwrap_or(max)
}

/// Check whether an inheritance graph has any diamond patterns.
pub(crate) fn has_diamond_inheritance(parent_names: &[Name], env: &Environment) -> bool {
    let resolver = InheritExtResolver::with_defaults(env);
    resolver
        .detect_diamonds(parent_names)
        .map(|d| !d.is_empty())
        .unwrap_or(false)
}
