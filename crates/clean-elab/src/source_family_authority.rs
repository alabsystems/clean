// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0
//! Source freshness and closed builtin completion are separate from typed replay.

use std::collections::{BTreeMap, BTreeSet};

use clean_kernel::env::{ConstantKind, TrustedEnvExt};
use clean_kernel::{Environment, Expr, Name};

use crate::{ElabError, ElabResult};

/// The constructor matchers generated or reused during recursive lowering.
pub(crate) type GeneratedMatchers = Vec<(Name, clean_kernel::env::MatcherInfo)>;

/// Evidence minted only after authoritative source registration succeeds.
/// It cannot authorize an axiom replacement and is consumed by a staging mirror.
pub(crate) struct PublishedSourceResult<'a> {
    result: &'a ElabResult,
    matchers: GeneratedMatchers,
    pub(crate) registered_names: Vec<Name>,
}

impl PublishedSourceResult<'_> {
    pub(crate) fn mirror_into(
        self,
        staging: &mut Environment,
        published: &Environment,
        decl: &clean_parser::SurfaceDecl,
        names: &BTreeSet<Name>,
    ) -> Result<(), ElabError> {
        crate::register::register_elab_result_with_matchers(staging, self.result, &self.matchers)?;
        // Later source bodies elaborate in this environment. The registered
        // kernel telescope retains binder kinds, while the source declaration
        // supplies the names used by named arguments.
        crate::register::register_param_names(staging, decl, self.result);
        // An attribute on the published declaration may override its default
        // reducibility. Later tactics must see the same unfolding boundary.
        for name in names {
            if let (Some(hint), Some(staged)) = (
                published.get_reducibility(name),
                staging.get_reducibility(name),
            ) {
                if hint != staged {
                    staging.set_reducibility(name, hint);
                }
            }
        }
        Ok(())
    }
}

/// Register generated matcher definitions and their elaborator metadata atomically.
/// Reused resident matchers keep the same metadata equality check as new rows.
pub(crate) fn register_source_with_matchers<'a>(
    env: &mut Environment,
    result: &'a ElabResult,
    matchers: GeneratedMatchers,
) -> Result<PublishedSourceResult<'a>, ElabError> {
    preflight_source_slots(env, result)?;
    let registered_names =
        crate::register::register_elab_result_with_matchers(env, result, &matchers)?;
    Ok(PublishedSourceResult {
        result,
        matchers,
        registered_names,
    })
}

/// Check explicit typed and derived source outputs before registration. Names
/// generated inside the kernel retain its existing checked collision/rollback
/// policy; this frontend does not guess their spelling.
pub(crate) fn register_source<'a>(
    env: &mut Environment,
    result: &'a ElabResult,
) -> Result<PublishedSourceResult<'a>, ElabError> {
    register_source_with_matchers(env, result, Vec::new())
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

#[cfg(test)]
mod matcher_tests {
    use super::*;
    use clean_kernel::env::MatcherInfo;
    use clean_kernel::BinderInfo;

    #[test]
    fn inconsistent_reused_matcher_preserves_the_whole_source_transaction() {
        let mut env = Environment::with_prelude();
        let definition = |name: &str| {
            let nat = Expr::const_str("Nat");
            ElabResult::Definition {
                name: Name::from_string(name),
                universe_params: vec![],
                ty: Expr::arrow(nat.clone(), Expr::arrow(nat.clone(), nat.clone())),
                val: Expr::lam(
                    BinderInfo::Default,
                    nat.clone(),
                    Expr::lam(BinderInfo::Default, nat, Expr::bvar(1)),
                ),
                modifiers: Default::default(),
            }
        };
        let resident = Name::from_string("priorMatcher");
        register_source(&mut env, &definition("priorMatcher")).unwrap();
        let prior = MatcherInfo {
            num_params: 0,
            num_discrs: 1,
            alt_num_params: vec![],
            u_elim_pos: None,
            discr_names: vec![None],
            details: None,
        };
        env.register_matcher_info(resident.clone(), prior.clone())
            .unwrap();
        let mut changed = prior.clone();
        changed.discr_names[0] = Some(Name::from_string("h"));
        let candidate = definition("newDefinition");
        let result =
            register_source_with_matchers(&mut env, &candidate, vec![(resident.clone(), changed)]);
        assert!(matches!(
            result,
            Err(ElabError::KernelRegistrationFailed { .. })
        ));
        assert!(env.get_const(&Name::from_string("newDefinition")).is_none());
        assert_eq!(env.get_matcher_info(&resident), Some(&prior));
    }
}
