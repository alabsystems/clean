// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Existing real Lean-minted replay artifacts exercise the public census path.

use super::*;
use crate::import::{load_module_with_deps_shared_with_policy, OleanImportPolicy};
use crate::test_support::compiled_fixture_dir;
use clean_kernel::name::Name;

fn loaded(
    module: &str,
) -> (
    Environment,
    Vec<LoadSummary>,
    BTreeSet<String>,
    BTreeSet<String>,
) {
    let paths = vec![
        compiled_fixture_dir("replay_forged"),
        crate::pinned_lean_lib_path().expect("actual pinned Lean library"),
    ];
    let mut env = Environment::for_lean_replay();
    env.set_kernel_theory(clean_kernel::env::KernelTheory::Lean);
    let summaries = load_module_with_deps_shared_with_policy(
        &mut env,
        module,
        &paths,
        &mut hashbrown::HashSet::new(),
        OleanImportPolicy::default()
            .with_kernel_only()
            .with_replay_refusals(),
    )
    .expect("real replay artifact loads");
    let modules = BTreeSet::from([module.to_owned()]);
    let targets = summaries
        .iter()
        .filter_map(|s| s.stored_declarations.as_ref())
        .filter(|part| part.artifact.as_deref() == Some(module))
        .flat_map(|part| part.declarations.iter().map(|(n, _)| n.to_string()))
        .collect();
    (env, summaries, modules, targets)
}

#[test]
fn original_unsafe_is_refused_without_authority_and_safe_neighbor_admitted() {
    let (env, summaries, modules, targets) = loaded("ReplayHonestUnsafe");
    let census = replay_declaration_census(&env, &summaries, &modules, &targets, 0);
    assert!(census.is_complete(), "{census:?}");
    assert_eq!(
        (
            census.seen(),
            census.admitted(),
            census.not_replayable(),
            census.failed_declarations()
        ),
        (2, 1, 1, 0)
    );
    assert!(matches!(
        &census.verdicts()["honest_unsafe_val"],
        DeclarationReplayVerdict::NotReplayable {
            safety: DefinitionSafety::Unsafe,
            refusal: ReplayRefusal::NotReplayable { .. }
        }
    ));
    assert!(matches!(
        census.verdicts()["honest_safe"],
        DeclarationReplayVerdict::Admitted
    ));
}

#[test]
fn safe_declaration_marked_unsafe_by_loader_is_still_a_failure() {
    let (mut env, summaries, modules, targets) = loaded("ReplayHonestUnsafe");
    env.mark_unsafe(Name::from_string("honest_safe"));
    let census = replay_declaration_census(&env, &summaries, &modules, &targets, 0);
    assert!(!census.is_complete());
    assert_eq!(
        census.not_replayable(),
        1,
        "only the original unsafe declaration qualifies"
    );
    assert!(matches!(
        &census.verdicts()["honest_safe"],
        DeclarationReplayVerdict::Failed(CensusFailure::Replay(
            ReplayRefusal::NotReplayable { .. }
        ))
    ));
}

#[test]
fn safe_use_of_unsafe_remains_refused() {
    let (env, summaries, mut modules, mut targets) = loaded("ReplayForged5");
    // Include the actual imported unsafe declaration in THIS replay graph,
    // rather than relying only on the kernel's unsafe-import check.
    modules.insert("Init.Prelude".into());
    targets.extend(
        summaries
            .iter()
            .filter_map(|s| s.stored_declarations.as_ref())
            .filter(|p| p.artifact.as_deref() == Some("Init.Prelude"))
            .flat_map(|p| p.declarations.iter().map(|(n, _)| n.to_string())),
    );
    let census = replay_declaration_census(&env, &summaries, &modules, &targets, 0);
    assert!(!census.is_complete(), "{census:?}");
    assert!(census.seen() > 1);
    assert!(matches!(
        census.verdicts()["unsafeCast"],
        DeclarationReplayVerdict::NotReplayable { .. }
    ));
    assert!(matches!(
        census.verdicts()["forged5_unsafe"],
        DeclarationReplayVerdict::Failed(CensusFailure::Replay(
            ReplayRefusal::DependsOnRefused { .. }
        ))
    ));
}

#[test]
fn full_roster_missing_extra_duplicate_and_unknown_records_are_fatal() {
    let (env, summaries, modules, targets) = loaded("ReplayHonestUnsafe");
    let mut missing = targets.clone();
    missing.remove("honest_safe");
    let census = replay_declaration_census(&env, &summaries, &modules, &missing, 0);
    assert_eq!(census.seen(), 2, "omitted names remain in the same graph");
    assert!(census
        .accounting_errors()
        .contains(&CensusAccountingError::MissingTarget("honest_safe".into())));
    assert!(!census.is_complete());
    let mut extra = targets.clone();
    extra.insert("not_stored".into());
    let census = replay_declaration_census(&env, &summaries, &modules, &extra, 0);
    assert_eq!(census.seen(), 3);
    assert!(matches!(
        census.verdicts()["not_stored"],
        DeclarationReplayVerdict::Failed(CensusFailure::MissingStoredDeclaration)
    ));
    let mut duplicate = summaries.clone();
    duplicate.push(
        summaries
            .iter()
            .find(|s| {
                s.stored_declarations
                    .as_ref()
                    .is_some_and(|p| p.artifact.as_deref() == Some("ReplayHonestUnsafe"))
            })
            .expect("own artifact")
            .clone(),
    );
    let census = replay_declaration_census(&env, &duplicate, &modules, &targets, 0);
    assert!(!census.is_complete());
    assert!(census
        .accounting_errors()
        .iter()
        .any(|e| matches!(e, CensusAccountingError::DuplicateDeclaration(_))));
    let mut unknown = summaries.clone();
    for part in unknown
        .iter_mut()
        .filter_map(|s| s.stored_declarations.as_mut())
        .filter(|p| p.artifact.as_deref() == Some("ReplayHonestUnsafe"))
    {
        for (_, safety) in &mut part.declarations {
            *safety = None;
        }
    }
    let census = replay_declaration_census(&env, &unknown, &modules, &targets, 0);
    assert_eq!(census.not_replayable(), 0);
    assert_eq!(census.failed_declarations(), 2);
    assert!(!census.is_complete());
}

#[test]
fn refused_safe_completion_cannot_be_reclassified_as_runtime() {
    let (env, summaries, modules, targets) = loaded("ReplayStubRefused");
    let census = replay_declaration_census(&env, &summaries, &modules, &targets, 0);
    assert!(!census.is_complete(), "{census:?}");
    assert_eq!(census.not_replayable(), 0);
    assert!(matches!(
        census.verdicts()["sr_t"],
        DeclarationReplayVerdict::Failed(_)
    ));
    assert!(matches!(
        census.verdicts()["sr_u"],
        DeclarationReplayVerdict::Failed(_)
    ));
    let (env, summaries, modules, targets) = loaded("ReplayStubHonest");
    let census = replay_declaration_census(&env, &summaries, &modules, &targets, 0);
    assert!(
        census.is_complete(),
        "honest authoritative completion remains admitted: {census:?}"
    );
    assert_eq!(census.admitted(), 2);
}

#[test]
fn missing_original_module_evidence_is_fatal_even_for_empty_target_set() {
    let (env, summaries, modules, targets) = loaded("ReplayHonestUnsafe");
    let census = replay_declaration_census(
        &env,
        &summaries,
        &BTreeSet::from(["AbsentArtifact".into()]),
        &BTreeSet::new(),
        0,
    );
    assert!(!census.is_complete());
    assert_eq!(
        census.accounting_errors(),
        &[CensusAccountingError::MissingModule(
            "AbsentArtifact".into()
        )]
    );
    let diagnostic = LoadSummary {
        module_name: Some("ReplayHonestUnsafe".into()),
        added_names: targets.iter().map(|n| Name::from_string(n)).collect(),
        ..LoadSummary::default()
    };
    let census = replay_declaration_census(&env, &[diagnostic], &modules, &targets, 0);
    assert!(
        !census.is_complete(),
        "public diagnostic fields cannot fabricate original evidence"
    );
    assert_eq!((census.admitted(), census.not_replayable()), (0, 0));
    assert_eq!(census.failed_declarations(), targets.len());
    assert!(census
        .accounting_errors()
        .contains(&CensusAccountingError::MissingModule(
            "ReplayHonestUnsafe".into()
        )));
}

#[test]
fn genuine_compiler_records_do_not_enlarge_the_logical_census() {
    let (env, summaries, _, _) = loaded("ReplayForged5");
    let own: Vec<_> = summaries
        .iter()
        .filter(|s| {
            s.stored_declarations
                .as_ref()
                .is_some_and(|p| p.artifact.as_deref() == Some("Init.Prelude"))
        })
        .collect();
    let compiler: BTreeSet<_> = own
        .iter()
        .flat_map(|s| s.skipped_constants.iter())
        .filter(|row| crate::import::is_compiler_ir_name(&row.name))
        .map(|row| row.name.clone())
        .collect();
    assert!(
        !compiler.is_empty(),
        "actual Lean fixture must contain excluded compiler records"
    );
    let targets = own
        .iter()
        .flat_map(|s| s.added_names.iter().map(ToString::to_string))
        .collect();
    let census = replay_declaration_census(
        &env,
        &summaries,
        &BTreeSet::from(["Init.Prelude".into()]),
        &targets,
        0,
    );
    // Other Prelude replay findings remain fatal. This specifically observes
    // the logical population, not a claim that Prelude is admitted in full.
    for name in compiler {
        assert!(
            !census.verdicts().contains_key(&name),
            "compiler record enlarged the logical census: {name}"
        );
        assert!(!census
            .accounting_errors()
            .contains(&CensusAccountingError::MissingTarget(name)));
    }
}

#[test]
fn unavailable_original_evidence_refuses_actual_proof_chain_users() {
    use clean_kernel::env::Declaration;
    use clean_kernel::expr::{BinderInfo, Expr};
    use clean_kernel::level::Level;

    // Self-contained, kernel-checked proof DATA, serialized through Clean's
    // real exporter/parser/loader. No claimed Lean producer or assumed axiom.
    let mut source = Environment::default();
    let type_ = Expr::pi(
        BinderInfo::Default,
        Expr::sort(Level::zero()),
        Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
    );
    let proof = Expr::lam(
        BinderInfo::Default,
        Expr::sort(Level::zero()),
        Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
    );
    for (name, value) in [
        ("Census.base", proof),
        (
            "Census.direct",
            Expr::const_(Name::from_string("Census.base"), vec![]),
        ),
        (
            "Census.transitive",
            Expr::const_(Name::from_string("Census.direct"), vec![]),
        ),
    ] {
        source
            .add_decl(Declaration::Theorem {
                name: Name::from_string(name),
                level_params: vec![],
                type_: type_.clone(),
                value,
            })
            .expect("actual kernel checks every proof before export");
    }
    let bytes = crate::export::OleanExporter::export_with_env(
        &source,
        &[],
        &[],
        "0000000000000000000000000000000000000000",
    )
    .expect("serialize checked proof data");
    let parsed = crate::parse_module(&bytes).expect("parse actual serialized artifact");
    let mut env = Environment::default();
    let summary = crate::load_parsed_module(&mut env, &parsed, Some("Census.Chain".into()))
        .expect("capture original evidence through real parsed-module loader");
    let modules = BTreeSet::from(["Census.Chain".to_owned()]);
    let targets = summary
        .added_names
        .iter()
        .map(ToString::to_string)
        .collect();
    let baseline =
        replay_declaration_census(&env, std::slice::from_ref(&summary), &modules, &targets, 0);
    assert!(baseline.is_complete(), "{baseline:?}");
    assert_eq!(baseline.admitted(), 3);
    for mutation in 0..3 {
        let mut changed = summary.clone();
        let records = &mut changed
            .stored_declarations
            .as_mut()
            .expect("actual stored part")
            .declarations;
        match mutation {
            0 => {
                records
                    .iter_mut()
                    .find(|(n, _)| n.to_string() == "Census.base")
                    .expect("stored base")
                    .1 = None
            }
            1 => records.retain(|(n, _)| n.to_string() != "Census.base"),
            2 => {
                let repeated = records
                    .iter()
                    .find(|(n, _)| n.to_string() == "Census.base")
                    .expect("stored base")
                    .clone();
                records.push(repeated);
            }
            _ => unreachable!(),
        }
        let census = replay_declaration_census(&env, &[changed], &modules, &targets, 0);
        assert!(!census.is_complete(), "mutation {mutation}: {census:?}");
        assert_eq!(
            census.admitted(),
            0,
            "invalid source evidence must not supply authority"
        );
        assert!(matches!(
            census.verdicts()["Census.base"],
            DeclarationReplayVerdict::Failed(_)
        ));
        for (name, dependency) in [
            ("Census.direct", "Census.base"),
            ("Census.transitive", "Census.direct"),
        ] {
            assert!(
                matches!(&census.verdicts()[name], DeclarationReplayVerdict::Failed(
                CensusFailure::Replay(ReplayRefusal::DependsOnRefused { dependency: actual, .. })
            ) if actual.to_string() == dependency),
                "mutation {mutation}: {census:?}"
            );
        }
    }
}

#[test]
fn dotted_unsafe_identity_cannot_hide_registry_accounting_failure() {
    use crate::import::{load_module_direct_with_cache, parse_load_module, ExprInternCache};
    use clean_kernel::expr::Expr;
    use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
    use clean_kernel::level::Level;

    let mut source = Environment::default();
    let name = Name::anon().str("Census.literal");
    assert_ne!(name, Name::from_string(&name.to_string()));
    source
        .add_inductive_core(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: name.clone(),
                type_: Expr::sort(Level::succ(Level::zero())),
                constructors: vec![Constructor {
                    name: name.clone().str("mk"),
                    type_: Expr::const_(name.clone(), vec![]),
                }],
            }],
        })
        .expect("actual kernel-checked family data");
    let original_names: Vec<_> = source.constants().map(|c| c.name.clone()).collect();
    assert_eq!(original_names.len(), 3);
    // Explicit runtime-safety fixture DATA, never logical/proof authority.
    for member in &original_names {
        source.mark_unsafe(member.clone());
    }
    let bytes = crate::export::OleanExporter::export_with_env(
        &source,
        &[],
        &[],
        "0000000000000000000000000000000000000000",
    )
    .expect("serialize original runtime records");
    let parsed = parse_load_module(bytes).expect("typed parsing preserves exact Name components");
    let mut env = Environment::default();
    let summary = load_module_direct_with_cache(
        &mut env,
        &parsed,
        Some("Census.Registry".into()),
        &mut ExprInternCache::default(),
    )
    .expect("actual typed artifact load");
    assert!(
        env.get_inductive(&name).is_some(),
        "actual dotted-component identity survived loading"
    );
    let targets = summary
        .added_names
        .iter()
        .map(ToString::to_string)
        .collect();
    let modules = BTreeSet::from(["Census.Registry".to_owned()]);
    let baseline =
        replay_declaration_census(&env, std::slice::from_ref(&summary), &modules, &targets, 0);
    assert!(baseline.is_complete(), "{baseline:?}");
    assert_eq!((baseline.admitted(), baseline.not_replayable()), (0, 3));
    let mut corrupt = env
        .get_const(&name)
        .expect("ordinary family mirror")
        .clone();
    corrupt.type_ = Expr::sort(Level::zero());
    // SOUNDNESS: existing dev-only corruption seam; this negative environment
    // never escapes the test and its malformed mirror is not admission.
    env.add_constant_unchecked_for_test(corrupt);
    let census = replay_declaration_census(&env, &[summary], &modules, &targets, 0);
    assert!(!census.is_complete(), "{census:?}");
    assert!(matches!(
        census.verdicts()[&name.to_string()],
        DeclarationReplayVerdict::Failed(CensusFailure::RegistryAccounting)
    ));
}

#[derive(Clone, Copy)]
enum PairCase {
    Honest,
    IncomingAxiom,
    CanonicalAxiom,
    TypeMismatch,
    UniverseMismatch,
    BadCanonicalValue,
    NonPropCanonical,
    LiteralPrivateName,
}

fn restatement_pair(
    case: PairCase,
    elide: bool,
) -> Result<
    (
        Environment,
        Vec<LoadSummary>,
        BTreeSet<String>,
        BTreeSet<String>,
    ),
    crate::ImportError,
> {
    use clean_kernel::env::{Declaration, ProofValueElision};
    use clean_kernel::expr::{BinderInfo, Expr};
    use clean_kernel::level::Level;
    let name = Name::from_string("Pair.shared");
    let user = Name::from_string("Pair.user");
    let type_ = Expr::pi(
        BinderInfo::Default,
        Expr::sort(Level::zero()),
        Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
    );
    let value = Expr::lam(
        BinderInfo::Default,
        Expr::sort(Level::zero()),
        Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
    );
    let mut canonical = Environment::default();
    let mut alias = Environment::default();
    if matches!(case, PairCase::CanonicalAxiom) {
        canonical
            .add_decl(Declaration::Axiom {
                name: name.clone(),
                level_params: vec![],
                type_: type_.clone(),
            })
            .unwrap();
    } else {
        canonical
            .add_decl(Declaration::Theorem {
                name: name.clone(),
                level_params: vec![],
                type_: type_.clone(),
                value: value.clone(),
            })
            .unwrap();
    }
    if matches!(case, PairCase::IncomingAxiom) {
        alias
            .add_decl(Declaration::Axiom {
                name: name.clone(),
                level_params: vec![],
                type_: type_.clone(),
            })
            .unwrap();
    } else if matches!(case, PairCase::TypeMismatch) {
        let other_type = Expr::pi(
            BinderInfo::Default,
            Expr::sort(Level::zero()),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(0),
                Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::bvar(2)),
            ),
        );
        let other_value = Expr::lam(
            BinderInfo::Default,
            Expr::sort(Level::zero()),
            Expr::lam(
                BinderInfo::Default,
                Expr::bvar(0),
                Expr::lam(BinderInfo::Default, Expr::bvar(1), Expr::bvar(0)),
            ),
        );
        alias
            .add_decl(Declaration::Theorem {
                name: name.clone(),
                level_params: vec![],
                type_: other_type,
                value: other_value,
            })
            .unwrap();
    } else {
        let params = if matches!(case, PairCase::UniverseMismatch) {
            vec![Name::from_string("unused_u")]
        } else {
            vec![]
        };
        alias
            .add_decl(Declaration::Theorem {
                name: name.clone(),
                level_params: params,
                type_: type_.clone(),
                value: value.clone(),
            })
            .unwrap();
        if !matches!(case, PairCase::UniverseMismatch) {
            alias
                .add_decl(Declaration::Theorem {
                    name: user.clone(),
                    level_params: vec![],
                    type_: type_.clone(),
                    value: Expr::const_(name.clone(), vec![]),
                })
                .unwrap();
        }
    }
    // Start with genuine kernel-checked proofs. Only the negative DATA below
    // bypasses checking, to test that later replay refuses it and all users.
    if matches!(
        case,
        PairCase::BadCanonicalValue | PairCase::NonPropCanonical
    ) {
        let mut bad = canonical.get_const(&name).unwrap().clone();
        if matches!(case, PairCase::NonPropCanonical) {
            bad.type_ = Expr::sort(Level::zero());
            bad.value = Some(type_.clone());
        } else {
            bad.value = Some(Expr::sort(Level::zero()));
        }
        canonical.add_constant_unchecked_for_test(bad);
        if matches!(case, PairCase::NonPropCanonical) {
            let mut bad = alias.get_const(&name).unwrap().clone();
            bad.type_ = Expr::sort(Level::zero());
            bad.value = Some(type_.clone());
            alias.add_constant_unchecked_for_test(bad);
        }
    }
    let dir = tempfile::tempdir().unwrap();
    let canonical_module = if matches!(case, PairCase::LiteralPrivateName) {
        "Canonical._private"
    } else {
        "Canonical"
    };
    for (module, source, imports) in [
        (canonical_module, &canonical, vec![]),
        ("Alias", &alias, vec![(canonical_module, false)]),
    ] {
        let bytes = crate::export::OleanExporter::export_with_env(
            source,
            &imports,
            &[],
            "0000000000000000000000000000000000000000",
        )
        .unwrap();
        let path = dir
            .path()
            .join(format!("{}.olean", module.replace('.', "/")));
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, bytes).unwrap();
    }
    let mut env = Environment::default();
    let policy = OleanImportPolicy::default()
        .with_replay_refusals()
        .with_proof_elision(if elide {
            ProofValueElision::OpaqueAndTheorem
        } else {
            ProofValueElision::None
        });
    let summaries = crate::import::load_modules_with_deps_with_import_policy(
        &mut env,
        &["Alias".into()],
        &[dir.path().to_owned()],
        policy,
    )?;
    let modules = BTreeSet::from([canonical_module.into(), "Alias".into()]);
    let targets = summaries
        .iter()
        .flat_map(|s| s.added_names.iter().map(ToString::to_string))
        .collect();
    Ok((env, summaries, modules, targets))
}

#[test]
fn completed_theorem_restatement_replays_one_canonical_proof_and_its_user() {
    let (env, summaries, modules, targets) = restatement_pair(PairCase::Honest, false).unwrap();
    let census = replay_declaration_census(&env, &summaries, &modules, &targets, 0);
    assert!(census.is_complete(), "{census:?}");
    assert_eq!(
        (census.seen(), census.admitted(), census.not_replayable()),
        (2, 2, 0)
    );
    assert_eq!(census.restatements().len(), 1);
    let occurrence = &census.restatements()[0];
    assert_eq!(
        (&*occurrence.artifact, &*occurrence.canonical_artifact),
        ("Alias", "Canonical")
    );
    assert!(occurrence.canonical_admitted && occurrence.incoming_theorem);
}

#[test]
fn restatement_never_grants_axiom_mismatch_or_elided_proof_authority() {
    for case in [
        PairCase::IncomingAxiom,
        PairCase::CanonicalAxiom,
        PairCase::TypeMismatch,
        PairCase::UniverseMismatch,
    ] {
        let (env, summaries, modules, targets) = restatement_pair(case, false)
            .expect("replay-refusal policy retains actual conflicting records for diagnosis");
        let census = replay_declaration_census(&env, &summaries, &modules, &targets, 0);
        assert!(!census.is_complete(), "{census:?}");
        assert!(census
            .restatements()
            .iter()
            .all(|row| !row.canonical_admitted));
    }
    let (env, summaries, modules, targets) = restatement_pair(PairCase::Honest, true).unwrap();
    for label in ["Pair.shared", "Pair.user"] {
        let row = env.get_const(&Name::from_string(label)).unwrap();
        assert_eq!(row.kind, clean_kernel::env::ConstantKind::Theorem);
        assert!(row.value.is_none(), "actual proof-elided theorem: {label}");
    }
    let census = replay_declaration_census(&env, &summaries, &modules, &targets, 0);
    assert!(!census.is_complete(), "{census:?}");
    assert_eq!(census.admitted(), 0, "elided proof census: {census:?}");
}

#[test]
fn restatement_canonical_kernel_refusal_still_refuses_its_user() {
    for case in [PairCase::BadCanonicalValue, PairCase::NonPropCanonical] {
        let (env, summaries, modules, targets) = restatement_pair(case, false).unwrap();
        let census = replay_declaration_census(&env, &summaries, &modules, &targets, 0);
        assert!(!census.is_complete(), "{census:?}");
        assert_eq!(census.admitted(), 0);
        assert!(matches!(
            &census.verdicts()["Pair.user"],
            DeclarationReplayVerdict::Failed(CensusFailure::Replay(
                ReplayRefusal::DependsOnRefused { .. }
            ))
        ));
        assert!(census
            .restatements()
            .iter()
            .all(|row| !row.canonical_admitted));
    }
}

#[test]
fn public_metadata_missing_private_evidence_or_nonselected_canonical_cannot_certify() {
    let (env, summaries, modules, targets) = restatement_pair(PairCase::Honest, false).unwrap();
    for mutation in 0..7 {
        let mut changed = summaries.clone();
        let alias = changed
            .iter_mut()
            .find(|s| s.module_name.as_deref() == Some("Alias"))
            .unwrap();
        let part = alias.stored_declarations.as_mut().unwrap();
        match mutation {
            0 => part.certified_restatements.clear(),
            1 => alias.restated_declarations[0].2 = false,
            2 => {
                let row = part
                    .declarations
                    .iter()
                    .find(|(name, _)| name.to_string() == "Pair.shared")
                    .unwrap()
                    .clone();
                part.declarations.push(row);
            }
            3 => {
                part.declarations
                    .iter_mut()
                    .find(|(n, _)| n.to_string() == "Pair.shared")
                    .unwrap()
                    .1 = Some(DefinitionSafety::Unsafe);
            }
            4 => {
                part.declarations
                    .iter_mut()
                    .find(|(n, _)| n.to_string() == "Pair.shared")
                    .unwrap()
                    .1 = None;
            }
            5 => alias.restated_declarations.push((
                Name::from_string("Pair.user"),
                "spoofed public DATA".into(),
                true,
            )),
            6 => {
                part.declarations
                    .iter_mut()
                    .find(|(n, _)| n.to_string() == "Pair.shared")
                    .unwrap()
                    .1 = Some(DefinitionSafety::Partial);
            }
            _ => unreachable!(),
        }
        let census = replay_declaration_census(&env, &changed, &modules, &targets, 0);
        assert!(!census.is_complete(), "mutation {mutation}: {census:?}");
    }
    let census = replay_declaration_census(
        &env,
        &summaries,
        &BTreeSet::from(["Alias".into()]),
        &targets,
        0,
    );
    assert!(
        !census.is_complete(),
        "foreign canonical owner is outside this graph"
    );
    for mutation in 0..7 {
        let mut changed = env.clone();
        let name = Name::from_string("Pair.shared");
        if mutation == 4 {
            // Genuine local proofs still cannot stand in for the captured
            // artifact-owned canonical declarations. Do not promote an import.
            changed = Environment::default();
            for label in ["Pair.shared", "Pair.user"] {
                let row = env.get_const(&Name::from_string(label)).unwrap();
                changed
                    .add_decl(clean_kernel::Declaration::Theorem {
                        name: row.name.clone(),
                        level_params: row.level_params.clone(),
                        type_: row.type_.clone(),
                        value: row.value.clone().unwrap(),
                    })
                    .unwrap();
            }
        } else if mutation >= 5 {
            // Unpinned origin metadata is negative DATA, never proof authority.
            let origin = if mutation == 5 {
                clean_kernel::env::ConstantOrigin::olean_import(None)
            } else {
                clean_kernel::env::ConstantOrigin::olean_import(Some("UnselectedArtifact".into()))
            };
            assert!(changed.set_constant_origin(name, origin));
        } else if mutation == 3 {
            changed = Environment::default();
        } else if mutation == 0 {
            changed.mark_unsafe(name);
        } else {
            let mut row = changed.get_const(&name).unwrap().clone();
            if mutation == 1 {
                row.value = None;
            } else {
                row.kind = clean_kernel::env::ConstantKind::Axiom;
            }
            changed.add_constant_unchecked_for_test(row);
        }
        let census = replay_declaration_census(&changed, &summaries, &modules, &targets, 0);
        assert!(
            !census.is_complete(),
            "changed canonical snapshot: {census:?}"
        );
        assert_eq!(census.admitted(), 0);
    }
}

#[test]
fn foreign_public_added_names_never_erase_earlier_loader_failures() {
    let (env, summaries, modules, targets) = restatement_pair(PairCase::Honest, false).unwrap();
    let baseline = replay_declaration_census(&env, &summaries, &modules, &targets, 0);
    assert!(baseline.is_complete(), "{baseline:?}");
    for mutation in 0..3 {
        let mut changed = summaries.clone();
        let name = Name::from_string("Pair.shared");
        let canonical = changed
            .iter_mut()
            .find(|s| s.module_name.as_deref() == Some("Canonical"))
            .unwrap();
        match mutation {
            0 => canonical.skipped_constants.push(crate::SkippedConstant {
                name: name.to_string(),
                reason: "declared earlier loader refusal DATA".into(),
            }),
            1 => canonical.refused_completions.push((
                name.clone(),
                "declared earlier incomplete value DATA".into(),
            )),
            2 => canonical.restated_declarations.push((
                name.clone(),
                "uncertified earlier occurrence DATA".into(),
                true,
            )),
            _ => unreachable!(),
        }
        changed
            .iter_mut()
            .find(|s| s.module_name.as_deref() == Some("Alias"))
            .unwrap()
            .added_names
            .push(name);
        let census = replay_declaration_census(&env, &changed, &modules, &targets, 0);
        assert!(!census.is_complete(), "mutation {mutation}: {census:?}");
        assert_eq!(census.admitted(), 0);
        assert!(matches!(
            &census.verdicts()["Pair.user"],
            DeclarationReplayVerdict::Failed(CensusFailure::Replay(
                ReplayRefusal::DependsOnRefused { .. }
            ))
        ));
    }
}

#[test]
fn real_private_part_completion_certifies_only_the_final_theorem_occurrence() {
    let paths = vec![crate::pinned_lean_lib_path().expect("actual pinned Lean library")];
    let mut env = Environment::default();
    let summaries = crate::import::load_modules_with_deps_with_import_policy(
        &mut env,
        &["Init.Data.String.Search".into()],
        &paths,
        OleanImportPolicy::default().with_replay_refusals(),
    )
    .expect("genuine base/server/private module family");
    let modules = BTreeSet::from([
        "Init.Data.String.Lemmas.Basic".into(),
        "Init.Data.String.Search".into(),
    ]);
    let targets = summaries
        .iter()
        .filter(|summary| {
            summary.stored_declarations.as_ref().is_some_and(|part| {
                part.artifact
                    .as_ref()
                    .is_some_and(|artifact| modules.contains(artifact))
            })
        })
        .flat_map(|summary| summary.added_names.iter().map(ToString::to_string))
        .collect();
    let census = replay_declaration_census(&env, &summaries, &modules, &targets, 0);
    let name = "String.pos.congr_simp";
    assert!(
        matches!(
            census.verdicts().get(name),
            Some(DeclarationReplayVerdict::Admitted)
        ),
        "{census:?}"
    );
    let occurrences: Vec<_> = census
        .restatements()
        .iter()
        .filter(|row| row.name == name)
        .collect();
    assert!(
        occurrences.iter().any(|row| !row.incoming_theorem),
        "exported axiom-shaped part"
    );
    assert!(
        occurrences.iter().any(|row| row.incoming_theorem),
        "actual authoritative private theorem"
    );
    assert!(occurrences.iter().all(|row| row.canonical_admitted));
    let mut incomplete = summaries.clone();
    incomplete.retain(|summary| {
        !summary.stored_declarations.as_ref().is_some_and(|part| {
            part.artifact.as_deref() == Some("Init.Data.String.Search")
                && part.certified_restatements.iter().any(|certificate| {
                    certificate.name().to_string() == name && certificate.incoming_theorem()
                })
        })
    });
    let refused = replay_declaration_census(&env, &incomplete, &modules, &targets, 0);
    assert!(
        !refused.is_complete(),
        "missing actual final private part cannot authorize its public stub"
    );
    assert!(
        matches!(
            refused.verdicts().get(name),
            Some(DeclarationReplayVerdict::Failed(_))
        ),
        "public stub must not borrow absent final-part authority: {refused:?}"
    );
}

#[test]
fn literal_private_named_artifact_is_not_its_namesakes_completion_part() {
    let (env, summaries, modules, targets) =
        restatement_pair(PairCase::LiteralPrivateName, false).unwrap();
    let census = replay_declaration_census(&env, &summaries, &modules, &targets, 0);
    assert!(census.is_complete(), "{census:?}");
    assert_eq!(
        census.restatements()[0].canonical_artifact,
        "Canonical._private"
    );
    let wrong_owner = BTreeSet::from(["Canonical".into(), "Alias".into()]);
    let refused = replay_declaration_census(&env, &summaries, &wrong_owner, &targets, 0);
    assert!(
        !refused.is_complete(),
        "a literal module name is not a suffix-based family"
    );
    assert_eq!(refused.admitted(), 0);
}

#[test]
fn partial_registration_cannot_mint_whole_artifact_restatement_evidence() {
    let (mut env, summaries, mut modules, targets) =
        restatement_pair(PairCase::Honest, false).unwrap();
    let bytes = crate::export::OleanExporter::export_with_env(
        &env,
        &[],
        &[],
        "0000000000000000000000000000000000000000",
    )
    .unwrap();
    let parsed = crate::parse_module(&bytes).unwrap();
    let partial = crate::load_parsed_module_with_import_policy(
        &mut env,
        &parsed,
        Some("Partial".into()),
        OleanImportPolicy::default().with_replay_refusals(),
    )
    .unwrap();
    assert!(partial
        .stored_declarations
        .as_ref()
        .unwrap()
        .certified_restatements
        .is_empty());
    modules.insert("Partial".into());
    let mut unfinished = summaries.clone();
    unfinished.push(partial);
    let refused = replay_declaration_census(&env, &unfinished, &modules, &targets, 0);
    assert!(
        !refused.is_complete(),
        "a partial registration has no active completed-family receipt"
    );
    assert_eq!(refused.admitted(), 0);
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("Partial.olean");
    std::fs::write(&path, &bytes).unwrap();
    let completed = crate::import::load_olean_file_with_import_policy(
        &mut env,
        &path,
        OleanImportPolicy::default().with_replay_refusals(),
    )
    .unwrap();
    let artifact = completed
        .stored_declarations
        .as_ref()
        .unwrap()
        .artifact
        .clone()
        .unwrap();
    let mut finished_modules = BTreeSet::from(["Canonical".into(), "Alias".into()]);
    finished_modules.insert(artifact);
    let mut finished = summaries;
    finished.push(completed);
    let census = replay_declaration_census(&env, &finished, &finished_modules, &targets, 0);
    assert!(
        census.is_complete(),
        "actual successful whole-artifact load seals its original occurrences: {census:?}"
    );
    assert_eq!(census.admitted(), 2);
}
