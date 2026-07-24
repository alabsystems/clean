// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended structure command elaboration: field elaboration, constructor/projector
//! generation, inheritance merging, eta expansion, anonymous constructors, subobject
//! handling, recursor generation, field update syntax, and statistics.

use crate::error::ElabError;
use crate::structure_cmd::{StructDef, StructField};
use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Level, Name};
use std::cell::Cell;
use std::collections::HashMap;
use thiserror::Error;

// -- Error ------------------------------------------------------------------

#[derive(Debug, Clone, Error)]
#[non_exhaustive]
pub(crate) enum StructExtError {
    #[error("cannot resolve type for field `{field}` in structure `{structure}`")]
    UnresolvedFieldType { structure: Name, field: Name },
    #[error("anonymous constructor for `{structure}` expects {expected} args, got {actual}")]
    AnonCtorArityMismatch {
        structure: Name,
        expected: usize,
        actual: usize,
    },
    #[error("subobject field `{field}` references unknown structure `{target}`")]
    UnknownSubobject { field: Name, target: Name },
    #[error("field `{field}` not found in structure `{structure}`")]
    UnknownUpdateField { structure: Name, field: Name },
    #[error("duplicate field `{field}` during merge in `{structure}`")]
    DuplicateField { structure: Name, field: Name },
}

impl From<StructExtError> for ElabError {
    fn from(err: StructExtError) -> Self {
        ElabError::NotImplemented(err.to_string())
    }
}

// -- Statistics -------------------------------------------------------------

// Per-thread counters: the test harness runs tests across a thread pool, so a
// process-global counter would race (one test's `reset_stats` + exact-value
// assertion interleaving with another test's elaboration). Thread-local cells
// give each test thread its own isolated view. These counters have no
// production consumer; they exist solely for test telemetry.
thread_local! {
    static STRUCTURES_ELABORATED: Cell<u64> = const { Cell::new(0) };
    static FIELDS_PROCESSED: Cell<u64> = const { Cell::new(0) };
    static PROJECTORS_GENERATED: Cell<u64> = const { Cell::new(0) };
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct StructStats {
    pub(crate) structures_elaborated: u64,
    pub(crate) fields_processed: u64,
    pub(crate) projectors_generated: u64,
}

#[must_use]
pub(crate) fn stats() -> StructStats {
    StructStats {
        structures_elaborated: STRUCTURES_ELABORATED.with(Cell::get),
        fields_processed: FIELDS_PROCESSED.with(Cell::get),
        projectors_generated: PROJECTORS_GENERATED.with(Cell::get),
    }
}

pub(crate) fn reset_stats() {
    STRUCTURES_ELABORATED.with(|c| c.set(0));
    FIELDS_PROCESSED.with(|c| c.set(0));
    PROJECTORS_GENERATED.with(|c| c.set(0));
}

fn record_elaboration(field_count: u64, projector_count: u64) {
    STRUCTURES_ELABORATED.with(|c| c.set(c.get() + 1));
    FIELDS_PROCESSED.with(|c| c.set(c.get() + field_count));
    PROJECTORS_GENERATED.with(|c| c.set(c.get() + projector_count));
}

// -- Helpers ----------------------------------------------------------------

fn to_u32(value: usize) -> u32 {
    u32::try_from(value).unwrap_or(u32::MAX)
}

fn mk_levels(universe_params: &[Name]) -> Vec<Level> {
    universe_params
        .iter()
        .map(|p| Level::param(p.clone()))
        .collect()
}

fn mk_struct_const(name: &Name, universe_params: &[Name], param_count: usize) -> Expr {
    let mut expr = Expr::const_(name.clone(), mk_levels(universe_params));
    for i in 0..param_count {
        expr = Expr::app(expr, Expr::bvar(to_u32(param_count - 1 - i)));
    }
    expr
}

fn head_const(expr: &Expr) -> Option<Name> {
    match expr.kind() {
        clean_kernel::ExprKind::Const(name, _) => Some(name.clone()),
        clean_kernel::ExprKind::App(func, _) => head_const(func),
        _ => None,
    }
}

fn field_component(name: &Name) -> String {
    name.last_component().unwrap_or_else(|| name.to_string())
}

fn mk_projection_field_type(struct_name: &Name, field_idx: usize, field_type: &Expr) -> Expr {
    let lifted = field_type.lift_from(to_u32(field_idx), 1);
    if field_idx == 0 {
        return lifted;
    }
    let replacements: Vec<Expr> = (0..field_idx)
        .rev()
        .map(|earlier| Expr::proj(struct_name.clone(), to_u32(earlier), Expr::bvar(0)))
        .collect();
    lifted.instantiate_rev(&replacements)
}

fn collect_app_args(expr: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut args = Vec::new();
    let mut current = expr;
    while let clean_kernel::ExprKind::App(func, arg) = current.kind() {
        args.push(arg.as_ref());
        current = func;
    }
    args.reverse();
    (current, args)
}

// -- 1. Field elaboration ---------------------------------------------------

#[derive(Debug, Clone)]
pub(crate) struct ElaboratedField {
    pub(crate) name: Name,
    pub(crate) type_: Expr,
    pub(crate) default_value: Option<Expr>,
    pub(crate) binder_info: BinderInfo,
    pub(crate) is_subobject: bool,
}

pub(crate) fn elaborate_fields(
    def: &StructDef,
    env: &Environment,
) -> Result<Vec<ElaboratedField>, StructExtError> {
    def.fields
        .iter()
        .map(|field| {
            let is_subobject = head_const(&field.type_)
                .and_then(|n| env.get_structure_field_names(&n))
                .is_some();
            Ok(ElaboratedField {
                name: field.name.clone(),
                type_: field.type_.clone(),
                default_value: field.default_value.clone(),
                binder_info: field.binder_info,
                is_subobject,
            })
        })
        .collect()
}

// -- 2. Constructor generation ----------------------------------------------

#[must_use]
pub(crate) fn constructor_name(struct_name: &Name) -> Name {
    Name::append(struct_name, "mk")
}

pub(crate) fn generate_constructor_type(
    struct_name: &Name,
    universe_params: &[Name],
    params: &[(Name, Expr, BinderInfo)],
    fields: &[ElaboratedField],
) -> Expr {
    let mut result = {
        let mut r = Expr::const_(struct_name.clone(), mk_levels(universe_params));
        for i in 0..params.len() {
            r = Expr::app(r, Expr::bvar(to_u32(fields.len() + params.len() - 1 - i)));
        }
        r
    };
    for field in fields.iter().rev() {
        result = Expr::pi(field.binder_info, field.type_.clone(), result);
    }
    for (_, param_type, _) in params.iter().rev() {
        result = Expr::pi(BinderInfo::Implicit, param_type.clone(), result);
    }
    result
}

// -- 3. Projection generation -----------------------------------------------

#[derive(Debug, Clone)]
pub(crate) struct ProjectorDecl {
    pub(crate) name: Name,
    pub(crate) field_idx: u32,
    pub(crate) decl: Declaration,
}

pub(crate) fn generate_projectors(
    struct_name: &Name,
    universe_params: &[Name],
    params: &[(Name, Expr, BinderInfo)],
    fields: &[ElaboratedField],
) -> Vec<ProjectorDecl> {
    fields
        .iter()
        .enumerate()
        .map(|(idx, field)| {
            let proj_name = Name::append(struct_name, &field_component(&field.name));
            let proj_idx = to_u32(idx);
            let struct_type = mk_struct_const(struct_name, universe_params, params.len());
            let field_type = mk_projection_field_type(struct_name, idx, &field.type_);

            let mut proj_type = Expr::pi(BinderInfo::Default, struct_type.clone(), field_type);
            let mut proj_value = Expr::lam(
                BinderInfo::Default,
                struct_type.clone(),
                Expr::proj(struct_name.clone(), proj_idx, Expr::bvar(0)),
            );
            for (_, param_type, _) in params.iter().rev() {
                proj_type = Expr::pi(BinderInfo::Implicit, param_type.clone(), proj_type);
                proj_value = Expr::lam(BinderInfo::Implicit, param_type.clone(), proj_value);
            }
            ProjectorDecl {
                name: proj_name.clone(),
                field_idx: proj_idx,
                decl: Declaration::Definition {
                    name: proj_name,
                    level_params: universe_params.to_vec(),
                    type_: proj_type,
                    value: proj_value,
                    is_reducible: true,
                },
            }
        })
        .collect()
}

// -- 4. Inheritance field merging -------------------------------------------

pub(crate) fn merge_inherited_fields(
    parent_fields: &[StructField],
    child_fields: &[StructField],
    struct_name: &Name,
) -> Result<Vec<StructField>, StructExtError> {
    let mut seen: HashMap<Name, usize> = HashMap::new();
    let mut result: Vec<StructField> = Vec::new();
    for field in parent_fields {
        seen.insert(field.name.clone(), result.len());
        result.push(field.clone());
    }
    for field in child_fields {
        if let Some(&idx) = seen.get(&field.name) {
            result[idx] = field.clone(); // Override
        } else if seen.contains_key(&field.name) {
            return Err(StructExtError::DuplicateField {
                structure: struct_name.clone(),
                field: field.name.clone(),
            });
        } else {
            seen.insert(field.name.clone(), result.len());
            result.push(field.clone());
        }
    }
    Ok(result)
}

// -- 5. Structure eta expansion ---------------------------------------------

/// Eta-expand: `s` -> `S.mk (s.f0) (s.f1) ... (s.fn)`
pub(crate) fn eta_expand(
    struct_name: &Name,
    universe_params: &[Name],
    field_count: usize,
    struct_val: Expr,
) -> Expr {
    let ctor = Expr::const_(constructor_name(struct_name), mk_levels(universe_params));
    let args = (0..field_count)
        .map(|idx| Expr::proj(struct_name.clone(), to_u32(idx), struct_val.clone()));
    Expr::apps(ctor, args)
}

/// Eta-reduce: `S.mk (S.proj0 s) ... (S.projN s)` -> `Some(s)`
#[must_use]
pub(crate) fn eta_reduce(struct_name: &Name, field_count: usize, expr: &Expr) -> Option<Expr> {
    let (head, args) = collect_app_args(expr);
    if args.len() != field_count {
        return None;
    }
    let ctor = constructor_name(struct_name);
    match head.kind() {
        clean_kernel::ExprKind::Const(name, _) if *name == ctor => {}
        _ => return None,
    }
    let mut candidate: Option<&Expr> = None;
    for (idx, arg) in args.iter().enumerate() {
        match arg.kind() {
            clean_kernel::ExprKind::Proj(pn, pi, pe) if pn == struct_name && *pi == to_u32(idx) => {
                match candidate {
                    None => candidate = Some(pe),
                    Some(prev) if format!("{prev:?}") != format!("{pe:?}") => return None,
                    _ => {}
                }
            }
            _ => return None,
        }
    }
    candidate.cloned()
}

// -- 6. Anonymous constructor -----------------------------------------------

pub(crate) fn resolve_anon_constructor(
    struct_name: &Name,
    universe_params: &[Name],
    args: &[Expr],
    field_count: usize,
) -> Result<Expr, StructExtError> {
    if args.len() != field_count {
        return Err(StructExtError::AnonCtorArityMismatch {
            structure: struct_name.clone(),
            expected: field_count,
            actual: args.len(),
        });
    }
    let ctor = Expr::const_(constructor_name(struct_name), mk_levels(universe_params));
    Ok(Expr::apps(ctor, args.iter().cloned()))
}

// -- 7. Subobject field handling --------------------------------------------

#[derive(Debug, Clone)]
pub(crate) struct SubobjectInfo {
    pub(crate) field_name: Name,
    pub(crate) field_idx: usize,
    pub(crate) target_struct: Name,
    pub(crate) target_field_count: usize,
}

pub(crate) fn collect_subobjects(
    fields: &[ElaboratedField],
    env: &Environment,
) -> Vec<SubobjectInfo> {
    fields
        .iter()
        .enumerate()
        .filter_map(|(idx, field)| {
            if !field.is_subobject {
                return None;
            }
            let target = head_const(&field.type_)?;
            let target_fields = env.get_structure_field_names(&target)?;
            Some(SubobjectInfo {
                field_name: field.name.clone(),
                field_idx: idx,
                target_struct: target,
                target_field_count: target_fields.len(),
            })
        })
        .collect()
}

// -- 8. Auto-generated recursor ---------------------------------------------

#[must_use]
pub(crate) fn recursor_name(struct_name: &Name) -> Name {
    Name::append(struct_name, "rec")
}

/// Generate recursor type:
/// `{motive : S -> Sort u} -> ((f1:T1) -> ... -> motive (S.mk f1 ...)) -> (s:S) -> motive s`
pub(crate) fn generate_recursor_type(
    struct_name: &Name,
    universe_params: &[Name],
    params: &[(Name, Expr, BinderInfo)],
    fields: &[ElaboratedField],
) -> Expr {
    let struct_type = mk_struct_const(struct_name, universe_params, params.len());
    let motive_type = Expr::pi(
        BinderInfo::Default,
        struct_type.clone(),
        Expr::sort(Level::param(Name::from_string("u_rec"))),
    );
    // Minor premise
    let mut ctor_app = Expr::const_(constructor_name(struct_name), mk_levels(universe_params));
    for i in 0..fields.len() {
        ctor_app = Expr::app(ctor_app, Expr::bvar(to_u32(fields.len() - 1 - i)));
    }
    let mut minor = Expr::app(Expr::bvar(to_u32(fields.len())), ctor_app);
    for field in fields.iter().rev() {
        minor = Expr::pi(BinderInfo::Default, field.type_.clone(), minor);
    }
    // Major premise + full type
    let major = Expr::pi(
        BinderInfo::Default,
        struct_type,
        Expr::app(Expr::bvar(1), Expr::bvar(0)),
    );
    let mut rec_type = Expr::pi(BinderInfo::Default, minor, major);
    rec_type = Expr::pi(BinderInfo::Implicit, motive_type, rec_type);
    for (_, param_type, _) in params.iter().rev() {
        rec_type = Expr::pi(BinderInfo::Implicit, param_type.clone(), rec_type);
    }
    rec_type
}

// -- 9. Field update syntax -------------------------------------------------

#[derive(Debug, Clone)]
pub(crate) struct FieldUpdate {
    pub(crate) field_name: Name,
    pub(crate) new_value: Expr,
}

pub(crate) fn elaborate_field_update(
    struct_name: &Name,
    universe_params: &[Name],
    fields: &[ElaboratedField],
    source: Expr,
    updates: &[FieldUpdate],
) -> Result<Expr, StructExtError> {
    let update_map: HashMap<&Name, &Expr> = updates
        .iter()
        .map(|u| (&u.field_name, &u.new_value))
        .collect();
    for update in updates {
        if !fields.iter().any(|f| f.name == update.field_name) {
            return Err(StructExtError::UnknownUpdateField {
                structure: struct_name.clone(),
                field: update.field_name.clone(),
            });
        }
    }
    let ctor = Expr::const_(constructor_name(struct_name), mk_levels(universe_params));
    let args = fields.iter().enumerate().map(|(idx, field)| {
        if let Some(new_val) = update_map.get(&field.name) {
            (*new_val).clone()
        } else {
            Expr::proj(struct_name.clone(), to_u32(idx), source.clone())
        }
    });
    Ok(Expr::apps(ctor, args))
}

// -- 10. Full pipeline ------------------------------------------------------

#[derive(Debug, Clone)]
pub(crate) struct ExtStructResult {
    pub(crate) fields: Vec<ElaboratedField>,
    pub(crate) projectors: Vec<ProjectorDecl>,
    pub(crate) subobjects: Vec<SubobjectInfo>,
    pub(crate) constructor_type: Expr,
    pub(crate) recursor_type: Expr,
    pub(crate) stats: StructStats,
}

pub(crate) fn elaborate_structure_ext(
    def: &StructDef,
    env: &Environment,
) -> Result<ExtStructResult, ElabError> {
    let fields = elaborate_fields(def, env)?;
    let projectors = generate_projectors(&def.name, &def.universe_params, &def.params, &fields);
    let subobjects = collect_subobjects(&fields, env);
    let constructor_type =
        generate_constructor_type(&def.name, &def.universe_params, &def.params, &fields);
    let recursor_type =
        generate_recursor_type(&def.name, &def.universe_params, &def.params, &fields);
    record_elaboration(fields.len() as u64, projectors.len() as u64);
    Ok(ExtStructResult {
        fields,
        projectors,
        subobjects,
        constructor_type,
        recursor_type,
        stats: stats(),
    })
}
