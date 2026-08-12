// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structure inheritance resolution for `extends` clauses.
//!
//! When a structure declaration includes `extends Parent`, this module:
//! 1. Resolves parent structures from the environment
//! 2. Collects and merges inherited fields (with override handling)
//! 3. Generates `toParent` projection function metadata
//! 4. Generates coercion registration metadata
//!
//! The resolver works against the kernel [`Environment`] to look up parent
//! inductive types, constructor field types, and registered structure fields.
//! It produces an [`InheritanceResult`] consumed by the structure elaboration
//! pipeline in [`crate::structure_cmd`].

use crate::structure_extend::strip_n_pi;
use clean_kernel::{Environment, Expr, ExprKind, Name};
use std::collections::{HashMap, HashSet};
use thiserror::Error;

// ---------------------------------------------------------------------------
// Error
// ---------------------------------------------------------------------------

/// Errors arising during structure inheritance resolution.
#[derive(Debug, Clone, Error)]
#[non_exhaustive]
pub(crate) enum InheritError {
    /// A parent name does not correspond to a registered structure.
    #[error("unknown parent structure `{name}`")]
    UnknownParent { name: Name },

    /// A parent structure has no constructors (malformed inductive).
    #[error("parent structure `{name}` has no constructor")]
    NoConstructor { name: Name },

    /// Field name collision between own and inherited fields that cannot be
    /// resolved by override (the types are incompatible).
    #[error("field `{field}` conflicts: inherited from `{origin}`, also declared locally")]
    // Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
    // keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
    #[allow(dead_code)]
    FieldConflict { field: Name, origin: Name },

    /// Two distinct parents contribute a field with the same name but
    /// different types, and neither is an explicit override.
    #[error(
        "field `{field}` inherited from both `{source_a}` and `{source_b}` with different types"
    )]
    AmbiguousField {
        field: Name,
        source_a: Name,
        source_b: Name,
    },

    /// Circular inheritance detected (struct transitively extends itself).
    #[error("circular inheritance: `{name}` transitively extends itself")]
    CircularInheritance { name: Name },
}

// ---------------------------------------------------------------------------
// Core types
// ---------------------------------------------------------------------------

/// Information about a resolved parent structure.
#[derive(Debug, Clone)]
pub(crate) struct ParentInfo {
    pub(crate) name: Name,
    pub(crate) fields: Vec<FieldInfo>,
    pub(crate) universe_params: Vec<Name>,
    pub(crate) num_params: u32,
}

/// A structure field — own or inherited.
#[derive(Debug, Clone)]
pub(crate) struct FieldInfo {
    pub(crate) name: Name,
    pub(crate) type_expr: Expr,
    pub(crate) default_value: Option<Expr>,
    /// `true` when the field was inherited from a parent.
    pub(crate) is_inherited: bool,
    /// The structure this field originates from (`None` for locally declared).
    pub(crate) source_struct: Option<Name>,
}

/// Metadata for a `toParent` projection function.
#[derive(Debug, Clone)]
pub(crate) struct ProjectionInfo {
    pub(crate) name: Name,
    pub(crate) parent: Name,
    /// Indices into the child's flattened field list that map to the parent's
    /// fields, in order.
    pub(crate) field_indices: Vec<usize>,
}

/// Metadata for a parent coercion to register.
#[derive(Debug, Clone)]
pub(crate) struct CoercionInfo {
    pub(crate) from: Name,
    pub(crate) to: Name,
    pub(crate) projection_name: Name,
}

/// Complete result of inheritance resolution.
#[derive(Debug, Clone)]
pub(crate) struct InheritanceResult {
    /// All fields in declaration order: inherited first, then own.
    pub(crate) all_fields: Vec<FieldInfo>,
    /// `toParent` projection metadata for each parent.
    pub(crate) parent_projections: Vec<ProjectionInfo>,
    /// Coercion metadata for each parent.
    pub(crate) coercions: Vec<CoercionInfo>,
    /// Resolved parent info for each parent (in order).
    pub(crate) parents: Vec<ParentInfo>,
}

// ---------------------------------------------------------------------------
// Resolver
// ---------------------------------------------------------------------------

/// Resolves structure inheritance from `extends` clauses.
pub(crate) struct InheritanceResolver<'a> {
    env: &'a Environment,
}

impl<'a> InheritanceResolver<'a> {
    pub(crate) fn new(env: &'a Environment) -> Self {
        Self { env }
    }

    // -- public pipeline entry point ----------------------------------------

    /// Full inheritance resolution pipeline.
    ///
    /// Given a struct name, its parent names (from `extends`), and its own
    /// locally-declared fields, resolves all inherited fields, checks for
    /// conflicts, and produces projection + coercion metadata.
    pub(crate) fn resolve_inheritance(
        &self,
        struct_name: &Name,
        parent_names: &[Name],
        own_fields: &[FieldInfo],
    ) -> Result<InheritanceResult, InheritError> {
        if parent_names.is_empty() {
            return Ok(InheritanceResult {
                all_fields: own_fields.to_vec(),
                parent_projections: Vec::new(),
                coercions: Vec::new(),
                parents: Vec::new(),
            });
        }

        self.check_circular(struct_name, parent_names)?;

        let parents = self.resolve_parents(parent_names)?;
        let inherited = self.collect_inherited_fields(&parents);
        self.check_field_conflicts(own_fields, &inherited)?;

        let all_fields = Self::merge_fields(&inherited, own_fields);
        let parent_projections = self.generate_projections(struct_name, &parents, &all_fields);
        let coercions = self.generate_coercions(struct_name, &parents, &parent_projections);

        Ok(InheritanceResult {
            all_fields,
            parent_projections,
            coercions,
            parents,
        })
    }

    // -- parent resolution --------------------------------------------------

    /// Look up each parent name in the environment and collect its field info.
    pub(crate) fn resolve_parents(
        &self,
        parent_names: &[Name],
    ) -> Result<Vec<ParentInfo>, InheritError> {
        parent_names.iter().map(|p| self.resolve_one(p)).collect()
    }

    fn resolve_one(&self, parent: &Name) -> Result<ParentInfo, InheritError> {
        let field_names = self.env.get_structure_field_names(parent).ok_or_else(|| {
            InheritError::UnknownParent {
                name: parent.clone(),
            }
        })?;

        let inductive =
            self.env
                .get_inductive(parent)
                .ok_or_else(|| InheritError::UnknownParent {
                    name: parent.clone(),
                })?;

        let ctor_name =
            inductive
                .constructor_names
                .first()
                .ok_or_else(|| InheritError::NoConstructor {
                    name: parent.clone(),
                })?;

        let ctor =
            self.env
                .get_constructor(ctor_name)
                .ok_or_else(|| InheritError::NoConstructor {
                    name: parent.clone(),
                })?;

        let field_types = collect_ctor_field_types(
            &ctor.type_,
            ctor.num_params as usize,
            ctor.num_fields as usize,
        );

        let fields = field_names
            .iter()
            .zip(field_types)
            .map(|(name, type_expr)| FieldInfo {
                name: name.clone(),
                type_expr,
                default_value: self.env.get_structure_field_default(parent, name).cloned(),
                is_inherited: true,
                source_struct: Some(parent.clone()),
            })
            .collect();

        Ok(ParentInfo {
            name: parent.clone(),
            fields,
            universe_params: inductive.level_params.clone(),
            num_params: inductive.num_params,
        })
    }

    // -- field collection & conflict checking --------------------------------

    /// Merge inherited fields from all parents, deduplicating by name
    /// (first occurrence wins, matching Lean 4 semantics for diamond cases).
    pub(crate) fn collect_inherited_fields(&self, parents: &[ParentInfo]) -> Vec<FieldInfo> {
        let mut seen = HashSet::new();
        let mut result = Vec::new();

        for parent in parents {
            for field in &parent.fields {
                if seen.insert(field.name.clone()) {
                    result.push(field.clone());
                }
            }
        }

        result
    }

    /// Check for naming conflicts between own fields and inherited fields.
    ///
    /// A local field with the same name as an inherited field is treated as an
    /// **override** (the local type supersedes the inherited one). However we
    /// still check for ambiguity among inherited fields from different parents.
    pub(crate) fn check_field_conflicts(
        &self,
        own_fields: &[FieldInfo],
        inherited_fields: &[FieldInfo],
    ) -> Result<(), InheritError> {
        // Detect cross-parent ambiguity: two parents contributing the same
        // field name with structurally different types.
        let mut by_name: HashMap<&Name, &FieldInfo> = HashMap::new();
        for field in inherited_fields {
            if let Some(existing) = by_name.get(&field.name) {
                if !structural_type_eq(&existing.type_expr, &field.type_expr) {
                    return Err(InheritError::AmbiguousField {
                        field: field.name.clone(),
                        source_a: existing
                            .source_struct
                            .clone()
                            .unwrap_or_else(|| Name::from_string("<unknown>")),
                        source_b: field
                            .source_struct
                            .clone()
                            .unwrap_or_else(|| Name::from_string("<unknown>")),
                    });
                }
            } else {
                by_name.insert(&field.name, field);
            }
        }

        // Own fields that collide with inherited fields are overrides — ok.
        // We only error if explicitly desired (Lean 4 allows overrides).
        // For now, we accept overrides silently.
        let _ = own_fields; // Used for documentation; override check is permissive.

        Ok(())
    }

    // -- projection generation -----------------------------------------------

    /// Generate `toParent` projection metadata for each parent.
    ///
    /// For a child with flattened fields `[a, b, c, d]` and parent `P` with
    /// fields `[a, b]`, the projection maps field indices `[0, 1]`.
    pub(crate) fn generate_projections(
        &self,
        struct_name: &Name,
        parents: &[ParentInfo],
        all_fields: &[FieldInfo],
    ) -> Vec<ProjectionInfo> {
        let field_index: HashMap<&Name, usize> = all_fields
            .iter()
            .enumerate()
            .map(|(i, f)| (&f.name, i))
            .collect();

        parents
            .iter()
            .map(|parent| {
                let parent_leaf = parent
                    .name
                    .last_component()
                    .unwrap_or_else(|| parent.name.to_string());
                let proj_name = Name::append(struct_name, &format!("to{parent_leaf}"));

                let field_indices = parent
                    .fields
                    .iter()
                    .filter_map(|f| field_index.get(&f.name).copied())
                    .collect();

                ProjectionInfo {
                    name: proj_name,
                    parent: parent.name.clone(),
                    field_indices,
                }
            })
            .collect()
    }

    /// Generate coercion metadata from child to each parent.
    pub(crate) fn generate_coercions(
        &self,
        struct_name: &Name,
        parents: &[ParentInfo],
        projections: &[ProjectionInfo],
    ) -> Vec<CoercionInfo> {
        parents
            .iter()
            .zip(projections.iter())
            .map(|(parent, proj)| CoercionInfo {
                from: struct_name.clone(),
                to: parent.name.clone(),
                projection_name: proj.name.clone(),
            })
            .collect()
    }

    // -- circularity check ---------------------------------------------------

    /// Detect circular inheritance (struct transitively extending itself).
    fn check_circular(
        &self,
        struct_name: &Name,
        parent_names: &[Name],
    ) -> Result<(), InheritError> {
        let mut stack: Vec<Name> = parent_names.to_vec();
        let mut visited = HashSet::new();

        while let Some(current) = stack.pop() {
            if &current == struct_name {
                return Err(InheritError::CircularInheritance {
                    name: struct_name.clone(),
                });
            }
            if !visited.insert(current.clone()) {
                continue;
            }
            if let Some(field_names) = self.env.get_structure_field_names(&current) {
                for field_name in field_names {
                    if let Some(parent) = infer_parent_from_field_name(field_name, self.env) {
                        if !visited.contains(&parent) {
                            stack.push(parent);
                        }
                    }
                }
            }
        }

        Ok(())
    }

    // -- field merging -------------------------------------------------------

    /// Merge inherited and own fields. Inherited fields come first; own fields
    /// that override an inherited field replace in-place, otherwise append.
    fn merge_fields(inherited: &[FieldInfo], own: &[FieldInfo]) -> Vec<FieldInfo> {
        let own_names: HashSet<&Name> = own.iter().map(|f| &f.name).collect();

        let mut result: Vec<FieldInfo> = inherited
            .iter()
            .map(|f| {
                if let Some(override_field) = own.iter().find(|o| o.name == f.name) {
                    // Override: keep position but use local type/default.
                    FieldInfo {
                        name: f.name.clone(),
                        type_expr: override_field.type_expr.clone(),
                        default_value: override_field.default_value.clone(),
                        is_inherited: false,
                        source_struct: None,
                    }
                } else {
                    f.clone()
                }
            })
            .collect();

        // Append own fields that are not overrides.
        for field in own {
            if !inherited.iter().any(|inh| inh.name == field.name) {
                let already_present =
                    own_names.contains(&field.name) && result.iter().any(|r| r.name == field.name);
                if !already_present {
                    result.push(field.clone());
                }
            }
        }

        result
    }
}

// ---------------------------------------------------------------------------
// Helpers (module-private)
// ---------------------------------------------------------------------------

/// Extract field types from a constructor type by stripping `num_params` Pi
/// binders then collecting the next `num_fields` Pi domains.
fn collect_ctor_field_types(ctor_type: &Expr, num_params: usize, num_fields: usize) -> Vec<Expr> {
    let mut types = Vec::with_capacity(num_fields);
    let mut current = strip_n_pi(ctor_type, num_params);

    while types.len() < num_fields {
        match current.kind() {
            ExprKind::Pi(_, domain, body) => {
                types.push((**domain).clone());
                current = body;
            }
            _ => break,
        }
    }

    types
}

/// Infer a parent structure name from a field name like `toFoo`.
fn infer_parent_from_field_name(field: &Name, env: &Environment) -> Option<Name> {
    let leaf = field.last_component()?;
    let suffix = leaf.strip_prefix("to")?;
    if suffix.is_empty() {
        return None;
    }

    let exact = Name::from_string(suffix);
    if env.get_structure_field_names(&exact).is_some() {
        return Some(exact);
    }

    // Fallback: search all constants for a structure whose leaf matches.
    env.constants()
        .map(|c| c.name.clone())
        .filter(|candidate| {
            env.get_structure_field_names(candidate).is_some()
                && candidate.last_component().as_deref() == Some(suffix)
        })
        .min_by_key(|c| c.to_string())
}

/// Conservative structural type equality for conflict checking.
pub(crate) fn structural_type_eq(a: &Expr, b: &Expr) -> bool {
    structural_type_eq_core(a.kind(), b.kind())
}

fn structural_type_eq_core(a: &ExprKind, b: &ExprKind) -> bool {
    match (a, b) {
        (ExprKind::BVar(l), ExprKind::BVar(r)) => l == r,
        (ExprKind::FVar(l), ExprKind::FVar(r)) => l == r,
        (ExprKind::Const(ln, ll), ExprKind::Const(rn, rl)) => ln == rn && ll == rl,
        (ExprKind::Sort(l), ExprKind::Sort(r)) => l == r,
        (ExprKind::App(lf, la), ExprKind::App(rf, ra)) => {
            structural_type_eq(lf, rf) && structural_type_eq(la, ra)
        }
        (ExprKind::Lam(lb, lt, lbody), ExprKind::Lam(rb, rt, rbody))
        | (ExprKind::Pi(lb, lt, lbody), ExprKind::Pi(rb, rt, rbody)) => {
            lb == rb && structural_type_eq(lt, rt) && structural_type_eq(lbody, rbody)
        }
        (ExprKind::Let(_, lt, lv, lb, _), ExprKind::Let(_, rt, rv, rb, _)) => {
            structural_type_eq(lt, rt) && structural_type_eq(lv, rv) && structural_type_eq(lb, rb)
        }
        (ExprKind::Lit(l), ExprKind::Lit(r)) => l == r,
        (ExprKind::Proj(ln, li, le), ExprKind::Proj(rn, ri, re)) => {
            ln == rn && li == ri && structural_type_eq(le, re)
        }
        _ => false,
    }
}
