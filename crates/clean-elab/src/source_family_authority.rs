// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0
//! Source freshness and closed builtin completion are separate from typed replay.

use std::collections::{BTreeMap, BTreeSet};

use clean_kernel::env::ConstantKind;
use clean_kernel::{Environment, Expr, Name};

use crate::{ElabError, ElabResult};

/// Evidence minted only after authoritative source registration succeeds.
/// It cannot authorize an axiom replacement and is consumed by a staging mirror.
pub(crate) struct PublishedSourceResult<'a> {
    result: &'a ElabResult,
}

impl PublishedSourceResult<'_> {
    pub(crate) fn mirror_into(self, staging: &mut Environment) -> Result<(), ElabError> {
        crate::register::register_elab_result(staging, self.result)
    }
}

/// Check explicit typed and derived source outputs before registration. Names
/// generated inside the kernel retain its existing checked collision/rollback
/// policy; this frontend does not guess their spelling.
pub(crate) fn register_source<'a>(
    env: &mut Environment,
    result: &'a ElabResult,
) -> Result<PublishedSourceResult<'a>, ElabError> {
    preflight_source_slots(env, result)?;
    crate::register::register_elab_result(env, result)?;
    Ok(PublishedSourceResult { result })
}

fn collision(name: &Name) -> ElabError {
    ElabError::KernelRegistrationFailed {
        operation: "source family name preflight".to_owned(),
        detail: format!(
            "environment already contains '{}'",
            name.to_unambiguous_string()
        ),
    }
}

/// Read actual typed result names, including declared derived outputs. A
/// projection-backed instance occupies one slot within the same family result.
fn collect_source_outputs(
    result: &ElabResult,
    counts: &mut BTreeMap<Name, usize>,
    family_outputs: &mut BTreeSet<Name>,
) {
    match result {
        ElabResult::Diagnosed { result, .. } => {
            collect_source_outputs(result, counts, family_outputs);
        }
        ElabResult::Multiple(results) => {
            for result in results {
                collect_source_outputs(result, counts, family_outputs);
            }
        }
        _ => {
            let mut outputs: BTreeSet<_> = crate::register::leaf_own_names(result)
                .into_iter()
                .collect();
            let is_family = match result {
                ElabResult::Structure {
                    derived_instances, ..
                }
                | ElabResult::Inductive {
                    derived_instances, ..
                }
                | ElabResult::MutualInductive {
                    derived_instances, ..
                } => {
                    outputs.extend(
                        derived_instances
                            .iter()
                            .map(|instance| instance.name.clone()),
                    );
                    true
                }
                _ => false,
            };
            for name in outputs {
                *counts.entry(name.clone()).or_default() += 1;
                if is_family {
                    family_outputs.insert(name);
                }
            }
        }
    }
}

fn preflight_source_slots(env: &Environment, result: &ElabResult) -> Result<(), ElabError> {
    let mut counts = BTreeMap::new();
    let mut outputs = BTreeSet::new();
    collect_source_outputs(result, &mut counts, &mut outputs);
    for name in outputs {
        if counts.get(&name).copied() != Some(1)
            || env.get_const(&name).is_some()
            || env.get_inductive(&name).is_some()
            || env.get_constructor(&name).is_some()
            || env.get_recursor(&name).is_some()
        {
            return Err(collision(&name));
        }
    }
    Ok(())
}

fn fact_slots(result: &ElabResult) -> Result<(&[Name], Vec<(&Name, &Expr)>), ElabError> {
    if let ElabResult::Diagnosed { result, .. } = result {
        return fact_slots(result);
    }
    let ElabResult::Structure {
        name,
        universe_params,
        ty,
        ctor_name,
        ctor_ty,
        projections,
        ..
    } = result
    else {
        return Err(ElabError::InternalInvariant(
            "builtin Fact did not elaborate to a structure".to_owned(),
        ));
    };
    let slots = std::iter::once((name, ty))
        .chain(std::iter::once((ctor_name, ctor_ty)))
        .chain(projections.iter().map(|(name, type_, _)| (name, type_)))
        .collect();
    Ok((universe_params, slots))
}

/// Complete the existing builtin Fact creator before yielding the environment.
/// Only declarations actually created by this successful invocation may be
/// removed. No delayed marker, caller-supplied result, or user source gains a
/// compatibility capability. An initializer no-op creates no authority.
pub(crate) fn complete_fact_bootstrap(env: &mut Environment) -> Result<(), ElabError> {
    let mut candidate = env.clone();
    let before: BTreeSet<_> = candidate
        .constants()
        .map(|info| info.name.clone())
        .collect();
    candidate
        .init_fact()
        .map_err(|error| ElabError::KernelRegistrationFailed {
            operation: "builtin Fact creation".to_owned(),
            detail: error.to_string(),
        })?;
    let created: BTreeMap<_, _> = candidate
        .constants()
        .filter(|info| !before.contains(&info.name))
        .map(|info| (info.name.clone(), info.clone()))
        .collect();
    if created.is_empty() {
        return Ok(());
    }

    let declarations = clean_parser::parse_file("class Fact (p : Prop) : Prop where\n  out : p\n")
        .map_err(|error| ElabError::InternalInvariant(format!("builtin Fact syntax: {error}")))?;
    let [declaration] = declarations.as_slice() else {
        return Err(ElabError::InternalInvariant(
            "builtin Fact source has the wrong declaration count".to_owned(),
        ));
    };
    let result = crate::elaborate_decl(&candidate, declaration)?;
    let (universe_params, slots) = fact_slots(&result)?;
    if created.len() != slots.len() {
        return Err(ElabError::InternalInvariant(
            "builtin Fact creation did not produce its complete family".to_owned(),
        ));
    }
    {
        let checker = clean_kernel::TypeChecker::new(&candidate);
        for (name, type_) in &slots {
            let Some(info) = created.get(*name) else {
                return Err(collision(name));
            };
            if candidate.get_const(name) != Some(info)
                || info.kind != ConstantKind::Axiom
                || info.value.is_some()
                || info.level_params.as_slice() != universe_params
                || !checker.is_def_eq(&info.type_, type_)
            {
                return Err(collision(name));
            }
        }
    }
    // All slots were authenticated and checked before the first removal. The
    // local transaction owns the environment throughout creation and completion;
    // no authoritative dependent declaration can be introduced between them.
    for (name, _) in slots {
        if !candidate.discharge_axiom_stub_for_inductive_import(name) {
            return Err(ElabError::InternalInvariant(
                "builtin Fact slot changed during completion".to_owned(),
            ));
        }
    }
    register_source(&mut candidate, &result)?;
    crate::register::register_param_names(&mut candidate, declaration, &result);
    *env = candidate;
    Ok(())
}
