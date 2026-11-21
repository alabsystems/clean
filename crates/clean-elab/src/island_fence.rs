// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

//! Island prelude registration fence (Ph3 I.2 / Clean F5).
//!
//! When an environment carries the island-prelude marker
//! ([`crate::source_prelude::is_island_prelude`]), mounted units elaborate over
//! pinned Lean `Init` and may not declare axioms, body-less opaques, or
//! `unsafe`/`partial` items, nor lean (directly or transitively) on any
//! trust marker, `unsafe`/`partial` constant, or non-foundational value-less
//! constant.

use std::collections::{BTreeSet, HashSet};

use clean_kernel::env::{
    is_canonical_foundational_constant, is_trust_marker, ConstantInfo, ConstantKind, Environment,
};
use clean_kernel::expr::UsedConstants;
use clean_kernel::{Expr, Name};
use clean_parser::DeclModifiers;

use crate::error::ElabError;
use crate::infer::ElabResult;

pub(crate) fn enforce_island_registration(
    env: &Environment,
    result: &ElabResult,
) -> Result<(), ElabError> {
    if !crate::source_prelude::is_island_prelude(env) {
        return Ok(());
    }
    let mut own_names = HashSet::new();
    let mut direct_refs = HashSet::new();
    collect_result_obligations(result, &mut own_names, &mut direct_refs)?;

    let subject = result
        .declaration_name()
        .map(ToString::to_string)
        .unwrap_or_else(|| "<anonymous>".to_string());

    for name in &own_names {
        if is_trust_marker(name) {
            return Err(fence_refusal(
                &subject,
                format!("island unit may not declare trust marker `{name}`"),
            ));
        }
    }

    let mut pending: BTreeSet<Name> = direct_refs.into_iter().collect();
    let mut visited: HashSet<Name> = HashSet::new();
    while let Some(current) = pending.pop_first() {
        if !visited.insert(current.clone()) {
            continue;
        }
        if is_trust_marker(&current) {
            return Err(fence_refusal(
                &subject,
                format!("island unit leans on trust marker `{current}`"),
            ));
        }
        if own_names.contains(&current) {
            continue;
        }
        let Some(info) = env.get_const(&current) else {
            continue;
        };
        if env.is_unsafe(&current) {
            return Err(fence_refusal(
                &subject,
                format!("island unit leans on unsafe constant `{current}`"),
            ));
        }
        if env.is_partial(&current) {
            return Err(fence_refusal(
                &subject,
                format!("island unit leans on partial constant `{current}`"),
            ));
        }
        if info.value.is_none() && !is_allowed_valueless_constant(env, info) {
            return Err(fence_refusal(
                &subject,
                format!(
                    "island unit leans on non-foundational value-less constant `{current}` ({:?})",
                    info.kind
                ),
            ));
        }
        let mut step_refs = HashSet::new();
        info.type_
            .used_constants_dag(UsedConstants::ConstantsOnly, &mut step_refs);
        if let Some(value) = &info.value {
            value.used_constants_dag(UsedConstants::ConstantsOnly, &mut step_refs);
        }
        if let Some(recursor) = env.get_recursor(&current) {
            for rule in &recursor.rules {
                rule.rhs
                    .used_constants_dag(UsedConstants::ConstantsOnly, &mut step_refs);
            }
        }
        for next in step_refs {
            if !visited.contains(&next) {
                pending.insert(next);
            }
        }
    }
    Ok(())
}

fn collect_result_obligations(
    result: &ElabResult,
    own_names: &mut HashSet<Name>,
    refs: &mut HashSet<Name>,
) -> Result<(), ElabError> {
    let mut add_expr = |expr: &Expr| {
        expr.used_constants_dag(UsedConstants::ConstantsOnly, refs);
    };
    match result {
        ElabResult::Diagnosed { result, .. } => collect_result_obligations(result, own_names, refs),
        ElabResult::Multiple(items) => {
            for item in items {
                collect_result_obligations(item, own_names, refs)?;
            }
            Ok(())
        }
        ElabResult::Axiom { name, .. } => Err(fence_refusal(
            &name.to_string(),
            format!("island unit may not declare axiom `{name}`"),
        )),
        ElabResult::Opaque {
            name,
            ty,
            val,
            modifiers,
            ..
        } => {
            check_safe_total_modifiers(name, modifiers)?;
            let Some(body) = val else {
                return Err(fence_refusal(
                    &name.to_string(),
                    format!("island unit may not declare body-less opaque `{name}`"),
                ));
            };
            own_names.insert(name.clone());
            add_expr(ty);
            add_expr(body);
            Ok(())
        }
        ElabResult::Definition {
            name,
            ty,
            val,
            modifiers,
            ..
        }
        | ElabResult::Instance {
            name,
            ty,
            val,
            modifiers,
            ..
        } => {
            check_safe_total_modifiers(name, modifiers)?;
            own_names.insert(name.clone());
            add_expr(ty);
            add_expr(val);
            Ok(())
        }
        ElabResult::Theorem {
            name,
            ty,
            proof,
            modifiers,
            ..
        } => {
            check_safe_total_modifiers(name, modifiers)?;
            own_names.insert(name.clone());
            add_expr(ty);
            add_expr(proof);
            Ok(())
        }
        ElabResult::Inductive {
            name,
            ty,
            constructors,
            derived_instances,
            modifiers,
            ..
        } => {
            check_safe_total_modifiers(name, modifiers)?;
            own_names.insert(name.clone());
            add_expr(ty);
            for (ctor_name, ctor_ty) in constructors {
                own_names.insert(ctor_name.clone());
                add_expr(ctor_ty);
            }
            for inst in derived_instances {
                own_names.insert(inst.name.clone());
                add_expr(&inst.ty);
                add_expr(&inst.val);
            }
            Ok(())
        }
        ElabResult::MutualInductive {
            decl,
            derived_instances,
            modifiers,
        } => {
            for ind_ty in &decl.types {
                check_safe_total_modifiers(&ind_ty.name, modifiers)?;
                own_names.insert(ind_ty.name.clone());
                add_expr(&ind_ty.type_);
                for ctor in &ind_ty.constructors {
                    own_names.insert(ctor.name.clone());
                    add_expr(&ctor.type_);
                }
            }
            for inst in derived_instances {
                own_names.insert(inst.name.clone());
                add_expr(&inst.ty);
                add_expr(&inst.val);
            }
            Ok(())
        }
        ElabResult::Structure {
            name,
            ty,
            ctor_name,
            ctor_ty,
            field_defaults,
            projections,
            derived_instances,
            modifiers,
            ..
        } => {
            check_safe_total_modifiers(name, modifiers)?;
            own_names.insert(name.clone());
            own_names.insert(ctor_name.clone());
            add_expr(ty);
            add_expr(ctor_ty);
            for (_, default_expr) in field_defaults {
                add_expr(default_expr);
            }
            for (proj_name, proj_ty, proj_val) in projections {
                own_names.insert(proj_name.clone());
                add_expr(proj_ty);
                add_expr(proj_val);
            }
            for inst in derived_instances {
                own_names.insert(inst.name.clone());
                add_expr(&inst.ty);
                add_expr(&inst.val);
            }
            Ok(())
        }
        ElabResult::Example { ty, val } => {
            add_expr(ty);
            add_expr(val);
            Ok(())
        }
        ElabResult::Command(_) | ElabResult::Skipped | ElabResult::Failed { .. } => Ok(()),
    }
}

fn check_safe_total_modifiers(name: &Name, modifiers: &DeclModifiers) -> Result<(), ElabError> {
    if modifiers.is_unsafe {
        return Err(fence_refusal(
            &name.to_string(),
            format!("island unit may not declare unsafe item `{name}`"),
        ));
    }
    if modifiers.is_partial {
        return Err(fence_refusal(
            &name.to_string(),
            format!("island unit may not declare partial item `{name}`"),
        ));
    }
    Ok(())
}

fn is_allowed_valueless_constant(env: &Environment, info: &ConstantInfo) -> bool {
    if is_trust_marker(&info.name) || env.is_unsafe(&info.name) || env.is_partial(&info.name) {
        return false;
    }
    if kernel_generated_metadata_matches(env, info) {
        return true;
    }
    is_canonical_foundational_constant(info) && env.check_foundation_premises(&info.name).is_ok()
}

fn kernel_generated_metadata_matches(env: &Environment, info: &ConstantInfo) -> bool {
    if info.kind != ConstantKind::Definition || info.value.is_some() {
        return false;
    }
    if let Some(inductive) = env.get_inductive(&info.name) {
        return inductive.level_params == info.level_params && inductive.type_ == info.type_;
    }
    if let Some(constructor) = env.get_constructor(&info.name) {
        return constructor.level_params == info.level_params && constructor.type_ == info.type_;
    }
    if let Some(recursor) = env.get_recursor(&info.name) {
        return recursor.level_params == info.level_params && recursor.type_ == info.type_;
    }
    false
}

fn fence_refusal(subject: &str, detail: String) -> ElabError {
    ElabError::KernelRegistrationFailed {
        operation: format!("island prelude fence ({subject})"),
        detail,
    }
}
