// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Ordinary source controls for the kernel-record / compiler-name boundary.
use super::*;
use crate::module::typed_extensions::TypedExtensionEntry;
use crate::DefinitionSafety;

fn fixture() -> [LoadModule; 3] {
    let root = crate::test_support::compiled_fixture_dir("logical_compiler_names");
    let parts = ["", ".server", ".private"].map(|suffix| {
        std::fs::read(root.join(format!("LogicalCompilerNames.olean{suffix}"))).unwrap()
    });
    [
        parse_load_module(parts[0].clone()).unwrap(),
        parse_load_module_incremental(&parts[0], None, parts[1].clone()).unwrap(),
        parse_load_module_incremental(&parts[0], Some(&parts[1]), parts[2].clone()).unwrap(),
    ]
}

fn load(parts: &[LoadModule; 3]) -> Result<(Environment, Vec<LoadSummary>), ImportError> {
    let mut env = Environment::with_prelude();
    let mut summaries = Vec::new();
    load_artifact_parts(
        &mut env,
        "LogicalCompilerNames",
        &parts[0],
        Some(&parts[1]),
        Some(&parts[2]),
        &mut summaries,
        &mut ExprInternCache::default(),
        OleanImportPolicy::allow_unpinned_legacy(),
    )?;
    super::super::load_register::flush_pending_structure_metadata(&mut env)?;
    Ok((env, summaries))
}

#[test]
fn compiler_name_safe_source_projections_and_definitions_remain_logical() {
    let parts = fixture();
    let projection = Name::from_string("Ordinary._specFinalizedAt");
    for part in &parts {
        let entry = part
            .entries
            .iter()
            .flat_map(|extension| &extension.entries)
            .find_map(|entry| match entry {
                TypedExtensionEntry::Structure(info)
                    if info.struct_name == Name::from_string("Ordinary") =>
                {
                    Some(info)
                }
                _ => None,
            })
            .unwrap();
        assert!(entry
            .field_proj_fns
            .contains(&(Name::from_string("_specFinalizedAt"), projection.clone())));
        assert!(part
            .constants
            .iter()
            .any(|constant| constant.kernel_name == projection
                && constant.definition_safety == Some(DefinitionSafety::Safe)));
    }
    let (env, summaries) =
        load(&parts).expect("ordinary source imports through the projection guard");
    let mut names: Vec<Name> = [
        "Ordinary._specFinalizedAt",
        "Ordinary._lambdaField",
        "Ordinary.use",
        "Logical._spec",
        "Logical._lambda_1",
        "Logical._rarg",
        "Logical._unsafe_rec",
        "Logical._specification",
        "Logical._spec_1.nested",
        "Logical._elambda_1.nested",
    ]
    .map(Name::from_string)
    .into();
    names.push(Name::anon().str("Logical").str("Quoted._spec_1"));
    for name in names {
        let constant = env
            .get_const(&name)
            .unwrap_or_else(|| panic!("missing {name}"));
        assert!(
            constant.value.is_some(),
            "{name} retains its authoritative body"
        );
        assert!(!env.is_unsafe(&name) && !env.is_partial(&name));
        assert!(!summaries.iter().any(|part| part
            .skipped_constants
            .iter()
            .any(|row| row.name == name.to_string())));
        assert!(summaries
            .iter()
            .any(|part| part
                .stored_declarations
                .as_ref()
                .is_some_and(|records| records
                    .declarations
                    .iter()
                    .any(|(stored, safety)| stored == &name
                        && *safety == Some(DefinitionSafety::Safe)))));
    }
    let fields = [
        Name::from_string("_specFinalizedAt"),
        Name::from_string("_lambdaField"),
    ];
    assert_eq!(
        env.get_structure_field_names(&Name::from_string("Ordinary")),
        Some(fields.as_slice())
    );
}

#[test]
fn compiler_name_missing_projection_still_refuses_the_original_guard() {
    let mut parts = fixture();
    let name = Name::from_string("Ordinary._specFinalizedAt");
    for part in &mut parts {
        part.constants
            .retain(|constant| constant.kernel_name != name);
        part.const_names.retain(|constant| constant != &name);
    }
    let error = match load(&parts) {
        Ok(_) => panic!("metadata cannot stand in for an absent projection"),
        Err(error) => error,
    };
    assert!(
        matches!(error, ImportError::InconsistentStructureTable { .. }),
        "{error}"
    );
    assert!(error.to_string().contains("_specFinalizedAt"));
}

#[test]
fn compiler_name_contradictory_stub_safety_refuses_before_registration() {
    for (stub, full) in [
        (DefinitionSafety::Unsafe, DefinitionSafety::Safe),
        (DefinitionSafety::Safe, DefinitionSafety::Unsafe),
    ] {
        let mut parts = fixture();
        let name = Name::from_string("Logical._unsafe_rec");
        for (index, part) in parts.iter_mut().enumerate() {
            let constant = part
                .constants
                .iter_mut()
                .find(|c| c.kernel_name == name)
                .unwrap();
            constant.definition_safety = Some(if index < 2 { stub } else { full });
        }
        let mut env = Environment::with_prelude();
        let before = env.constants().count();
        let error = load_artifact_parts(
            &mut env,
            "LogicalCompilerNames",
            &parts[0],
            Some(&parts[1]),
            Some(&parts[2]),
            &mut Vec::new(),
            &mut ExprInternCache::default(),
            OleanImportPolicy::allow_unpinned_legacy(),
        )
        .expect_err("source safety contradicts its stub");
        assert!(
            matches!(error, ImportError::PartsDisagree { .. }),
            "{error}"
        );
        assert_eq!(env.constants().count(), before);
        assert!(env.get_const(&name).is_none());
    }
}

#[test]
fn compiler_name_430_partial_stubs_use_authoritative_safety_for_every_part() {
    let root = crate::test_support::compiled_fixture_dir("runtime_probe");
    let bytes = ["", ".server", ".private"]
        .map(|suffix| std::fs::read(root.join(format!("RuntimeProbe.olean{suffix}"))).unwrap());
    let parts = [
        parse_load_module(bytes[0].clone()).unwrap(),
        parse_load_module_incremental(&bytes[0], None, bytes[1].clone()).unwrap(),
        parse_load_module_incremental(&bytes[0], Some(&bytes[1]), bytes[2].clone()).unwrap(),
    ];
    let generated = Name::from_string("RuntimeProbe.count._unsafe_rec");
    assert_eq!(
        parts[0]
            .constants
            .iter()
            .find(|c| c.kernel_name == generated)
            .unwrap()
            .definition_safety,
        Some(DefinitionSafety::Safe)
    );
    assert_eq!(
        parts[2]
            .constants
            .iter()
            .find(|c| c.kernel_name == generated)
            .unwrap()
            .definition_safety,
        Some(DefinitionSafety::Partial)
    );
    let mut env = Environment::with_prelude();
    let mut summaries = Vec::new();
    load_artifact_parts(
        &mut env,
        "RuntimeProbe",
        &parts[0],
        Some(&parts[1]),
        Some(&parts[2]),
        &mut summaries,
        &mut ExprInternCache::default(),
        OleanImportPolicy::allow_unpinned_legacy(),
    )
    .unwrap();
    for summary in &summaries {
        assert!(summary
            .skipped_not_replayable
            .contains(&generated.to_string()));
        assert!(!summary
            .stored_declarations
            .as_ref()
            .unwrap()
            .declarations
            .iter()
            .any(|(name, _)| name == &generated));
    }
    assert!(env.get_const(&generated).is_none());
    for name in [
        Name::anon().str("RuntimeProbe").str("count._unsafe_rec"),
        Name::from_string("RuntimeProbe.safe._unsafe_rec"),
    ] {
        assert!(
            env.get_const(&name).is_some_and(|c| c.value.is_some()),
            "{name}"
        );
        assert!(!env.is_unsafe(&name) && !env.is_partial(&name));
    }
}

#[test]
fn compiler_name_exact_components_are_checked_and_bad_bodies_do_not_disappear() {
    use clean_kernel::env::{ConstantInfo, TrustedEnvExt};
    use clean_kernel::expr::{BinderInfo, Expr};
    use std::collections::BTreeSet;
    let names: Vec<Name> = [
        "_spec",
        "_spec_1",
        "_elambda_1",
        "_lambda_1",
        "_cstage1",
        "_rarg",
        "_unsafe_rec",
    ]
    .map(|name| Name::anon().str("Ordinary").str(name))
    .into();
    let ty = Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_());
    let good = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
    for malformed in [false, true] {
        let mut producer = Environment::default();
        producer.extend_constants_unchecked(names.iter().map(|name| {
            ConstantInfo::new(
                name.clone(),
                vec![],
                ty.clone(),
                Some(if malformed {
                    Expr::prop()
                } else {
                    good.clone()
                }),
                true,
            )
        }));
        let bytes = crate::OleanExporter::export_with_env(
            &producer,
            &[],
            &[],
            "0000000000000000000000000000000000000000",
        )
        .unwrap();
        for direct in [false, true] {
            let mut env = Environment::default();
            let summary = if direct {
                super::super::load_register::load_module_direct_with_cache(
                    &mut env,
                    &parse_load_module(bytes.clone()).unwrap(),
                    Some("Ordinary".into()),
                    &mut ExprInternCache::default(),
                )
                .unwrap()
            } else {
                crate::load_parsed_module_with_import_policy(
                    &mut env,
                    &crate::parse_module(&bytes).unwrap(),
                    Some("Ordinary".into()),
                    OleanImportPolicy::allow_unpinned_legacy(),
                )
                .unwrap()
            };
            assert!(summary.skipped_constants.is_empty(), "{summary:?}");
            let targets = names
                .iter()
                .map(ToString::to_string)
                .collect::<BTreeSet<_>>();
            let (passed, failed, errors) =
                crate::verify_batch_full::typecheck_constants_full(&env, &targets, 0);
            if malformed {
                assert_eq!(passed, 0);
                assert_eq!(failed, names.len());
                assert_eq!(errors.len(), names.len());
            } else {
                assert_eq!(passed, names.len(), "{errors:?}");
                assert_eq!(failed, 0);
            }
        }
    }
}

#[test]
fn compiler_name_payload_owner_cannot_inherit_unsafe_mirror_exclusion() {
    use crate::replay_census::{
        replay_declaration_census, CensusFailure, DeclarationReplayVerdict,
    };
    use clean_kernel::env::{ConstantInfo, TrustedEnvExt};
    use clean_kernel::expr::{BinderInfo, Expr};
    use std::collections::BTreeSet;
    for name in [
        Name::from_string("PayloadRoles._spec_1"),
        Name::anon().str("PayloadRoles").str("Quoted._spec_1"),
    ] {
        let ty = Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_());
        let identity = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
        for malformed in [false, true] {
            for mirror_present in [false, true] {
                let mut mirror = Environment::default();
                if mirror_present {
                    mirror.extend_constants_unchecked(
                        [ConstantInfo::new(
                            name.clone(),
                            vec![],
                            ty.clone(),
                            Some(identity.clone()),
                            true,
                        )]
                        .into_iter(),
                    );
                    mirror.mark_unsafe(name.clone());
                }
                let payload = crate::CleanPayload {
                    constants: vec![ConstantInfo::new(
                        name.clone(),
                        vec![],
                        ty.clone(),
                        Some(if malformed {
                            Expr::prop()
                        } else {
                            identity.clone()
                        }),
                        true,
                    )],
                    ..crate::CleanPayload::default()
                };
                let bytes = crate::OleanExporter::export_with_env_and_payload(
                    &mirror,
                    &[],
                    &[],
                    "0000000000000000000000000000000000000000",
                    &payload,
                )
                .unwrap();
                for direct in [false, true] {
                    let mut env = Environment::default();
                    if !direct && Name::from_string(&name.to_string()) != name {
                        let error = crate::load_parsed_module(
                            &mut env,
                            &crate::parse_module(&bytes).unwrap(),
                            Some("PayloadRoles".into()),
                        )
                        .expect_err("legacy payload identity must remain exact");
                        assert!(matches!(error, ImportError::LossyParsedPayloadName { .. }));
                        assert_eq!(env.constants().count(), 0);
                        continue;
                    }
                    let summary = if direct {
                        let module = parse_load_module(bytes.clone()).unwrap();
                        assert_eq!(module.constants.len(), usize::from(mirror_present));
                        if mirror_present {
                            assert_eq!(
                                module.constants[0].definition_safety,
                                Some(DefinitionSafety::Unsafe)
                            );
                        }
                        super::super::load_register::load_module_direct_with_cache(
                            &mut env,
                            &module,
                            Some("PayloadRoles".into()),
                            &mut ExprInternCache::default(),
                        )
                        .unwrap()
                    } else {
                        crate::load_parsed_module(
                            &mut env,
                            &crate::parse_module(&bytes).unwrap(),
                            Some("PayloadRoles".into()),
                        )
                        .unwrap()
                    };
                    assert!(summary.skipped_not_replayable.is_empty());
                    assert!(summary.skipped_constants.is_empty());
                    assert_eq!(
                        summary.stored_declarations.as_ref().unwrap().declarations,
                        vec![(name.clone(), None)]
                    );
                    assert!(env.get_const(&name).is_some());
                    assert!(!env.is_unsafe(&name));
                    let targets = BTreeSet::from([name.to_string()]);
                    let constant = env.get_const(&name).unwrap();
                    let checker = clean_kernel::TypeChecker::new(&env);
                    let checked =
                        checker.check_type(constant.value.as_ref().unwrap(), &constant.type_);
                    assert_eq!(
                        checked.is_err(),
                        malformed,
                        "the exact typed payload body is checked"
                    );
                    for requested in [&targets, &BTreeSet::new()] {
                        let census = replay_declaration_census(
                            &env,
                            std::slice::from_ref(&summary),
                            &BTreeSet::from(["PayloadRoles".to_string()]),
                            requested,
                            0,
                        );
                        assert_eq!(
                            census.seen(),
                            1,
                            "payload source never vanishes from the original roster"
                        );
                        assert_eq!(census.not_replayable(), 0);
                        assert!(matches!(
                            census.verdicts()[&name.to_string()],
                            DeclarationReplayVerdict::Failed(CensusFailure::UnknownStoredSafety)
                        ));
                        assert!(!census.is_complete());
                    }
                }
            }
        }
    }
}
