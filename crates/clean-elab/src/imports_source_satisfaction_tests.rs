// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A completed source import must not also install its on-disk artifact.

use std::path::Path;

use clean_kernel::env::csimp::{self, InlineMode};
use clean_kernel::env::DeclarationVerification;
use clean_kernel::{Environment, Expr, Name};
use clean_olean::{CleanPayload, CompilerContextKind, OleanExporter};

use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabError, FileContext,
};

const MODULE: &str = "SourceSide";
// The actual Clean-owned producer header, not a claimed Lean SDK artifact.
const CLEAN_HASH: &str = "1ea5000000000000000000000000000000000000";

#[derive(Clone, Copy)]
enum Artifact {
    Matching,
    ConflictingValue,
    StaleIdentity,
}

fn name(text: &str) -> Name {
    Name::from_string(text)
}

fn apply_source(
    env: &mut Environment,
    context: &mut FileContext,
    source: &str,
) -> Result<(), ElabError> {
    for declaration in clean_parser::parse_file(source).expect("source fixture parses") {
        let declaration = preprocess_decl_with_context(&declaration, context);
        let result = elaborate_decl_and_register_with_context(env, &declaration, context)?;
        assert!(result.source_error_message().is_none(), "{result:?}");
    }
    Ok(())
}

fn module_context(module: &str) -> FileContext {
    let mut context = FileContext::new();
    context.set_main_module(name(module));
    context
}

fn declare_module(env: &mut Environment, conflicting: bool, sentinel: bool) {
    let body = if conflicting { "Nat.succ n" } else { "n" };
    let source = format!(
        "def SourceSide.slow (n : Nat) : Nat := {body}\n\
         def SourceSide.fast (n : Nat) : Nat := {body}\n\
         @[csimp] theorem SourceSide.rule : SourceSide.slow = SourceSide.fast := rfl\n\
         @[macro_inline] def SourceSide.helper (n : Nat) : Nat := n\n\
         def SourceSide.wrap (n : Nat) : Nat := SourceSide.helper n\n"
    );
    let mut context = module_context(MODULE);
    apply_source(env, &mut context, &source).expect("checked source module");
    if sentinel {
        apply_source(
            env,
            &mut context,
            "def SourceSide.artifactOnly : Nat := 17\n",
        )
        .expect("artifact-only declaration is checked");
    }
}

fn write_artifact(base: &Environment, directory: &Path, artifact: Artifact) {
    let mut producer = base.clone();
    declare_module(
        &mut producer,
        matches!(artifact, Artifact::ConflictingValue),
        true,
    );
    let mut constants: Vec<_> = producer
        .constants()
        .filter(|info| info.name.to_string().starts_with("SourceSide."))
        .cloned()
        .collect();
    constants.sort_by_key(|info| info.name.clone());
    let mut payload = CleanPayload {
        constants,
        csimp: csimp::export_compilation_snapshot(&producer),
        compiler_context: CompilerContextKind::Source,
        ..CleanPayload::default()
    };
    if matches!(artifact, Artifact::StaleIdentity) {
        // The declaration remains well typed; its source compiler packet is
        // deliberately stale and must still refuse an actual artifact import.
        payload
            .constants
            .iter_mut()
            .find(|info| info.name == name("SourceSide.artifactOnly"))
            .expect("sentinel")
            .value = Some(Expr::nat_lit(18));
    }
    let bytes = OleanExporter::export_with_payload(&[], &[], &[], CLEAN_HASH, &payload)
        .expect("real source-context payload exports");
    std::fs::write(directory.join("SourceSide.olean"), bytes).expect("write artifact");
}

fn importer(directory: &Path, satisfied: bool) -> FileContext {
    let mut context = module_context("Consumer");
    context.set_import_search_paths(vec![directory.to_path_buf()]);
    if satisfied {
        context.mark_import_satisfied_from_source(&name(MODULE));
        // Availability alone must not make this module's rules visible.
        context.mark_import_satisfied_from_source(&name("AvailableOnly"));
    }
    context
}

fn assert_source_retained(artifact: Option<Artifact>) {
    let directory = tempfile::tempdir().expect("artifact directory");
    let base = Environment::with_prelude();
    let mut env = base.clone();
    declare_module(&mut env, false, false);
    let names = [
        "SourceSide.slow",
        "SourceSide.fast",
        "SourceSide.rule",
        "SourceSide.helper",
        "SourceSide.wrap",
    ];
    let before: Vec<_> = names
        .iter()
        .map(|text| {
            let n = name(text);
            (
                n.clone(),
                env.get_const(&n)
                    .expect("source declaration")
                    .compiler_identity_digest(),
                env.declaration_verification(&n),
                env.get_constant_origin(&n).cloned(),
            )
        })
        .collect();
    let mut sibling = module_context("AvailableOnly");
    sibling.set_import_search_paths(vec![directory.path().to_path_buf()]);
    sibling.mark_import_satisfied_from_source(&name(MODULE));
    apply_source(
        &mut env,
        &mut sibling,
        "import SourceSide\n\
         def AvailableOnly.fast (n : Nat) : Nat := n\n\
         @[csimp] theorem AvailableOnly.rule : SourceSide.slow = AvailableOnly.fast := rfl\n\
         @[macro_inline] def AvailableOnly.helper (n : Nat) : Nat := n\n",
    )
    .expect("available sibling is genuinely checked");
    if let Some(artifact) = artifact {
        write_artifact(&base, directory.path(), artifact);
    }
    let mut context = importer(directory.path(), true);
    apply_source(&mut env, &mut context, "import SourceSide\n").expect("source import");
    assert!(
        !csimp::has_invalid_metadata(&env),
        "unselected artifact poisoned source context"
    );
    assert!(env.get_const(&name("SourceSide.artifactOnly")).is_none());
    assert!(!context.import_visited().contains(MODULE));
    for (n, digest, verification, origin) in before {
        assert_eq!(
            env.get_const(&n)
                .expect("source retained")
                .compiler_identity_digest(),
            digest
        );
        assert_eq!(verification, Some(DeclarationVerification::FullKernelCheck));
        assert_eq!(env.declaration_verification(&n), verification);
        assert_eq!(env.get_constant_origin(&n), origin.as_ref());
    }
    assert!(csimp::rules_for(&env, Some(&name("SourceSide.wrap")))
        .iter()
        .any(|rule| rule.theorem == name("SourceSide.rule")));
    assert_eq!(
        csimp::inline_mode_at(
            &env,
            Some(&name("SourceSide.wrap")),
            &name("SourceSide.helper")
        ),
        Some(InlineMode::MacroInline)
    );
    apply_source(
        &mut env,
        &mut context,
        "def Consumer.call (n : Nat) : Nat := SourceSide.slow n\n\
         theorem Consumer.proof : Consumer.call 2 = 2 := rfl\n",
    )
    .expect("real caller and proof after import");
    let rules = csimp::rules_for(&env, Some(&name("Consumer.call")));
    assert!(rules
        .iter()
        .any(|rule| rule.theorem == name("SourceSide.rule")));
    assert!(!rules
        .iter()
        .any(|rule| rule.theorem == name("AvailableOnly.rule")));
    assert_eq!(
        csimp::inline_mode_at(
            &env,
            Some(&name("Consumer.call")),
            &name("AvailableOnly.helper")
        ),
        None
    );
    assert_eq!(
        env.declaration_verification(&name("Consumer.proof")),
        Some(DeclarationVerification::FullKernelCheck)
    );
}

#[test]
fn checked_source_precedes_a_matching_artifact() {
    assert_source_retained(Some(Artifact::Matching));
}

#[test]
fn checked_source_precedes_a_conflicting_value_artifact() {
    assert_source_retained(Some(Artifact::ConflictingValue));
}

#[test]
fn checked_source_precedes_a_stale_compiler_packet() {
    assert_source_retained(Some(Artifact::StaleIdentity));
}

#[test]
fn checked_source_without_an_artifact_retains_import_visibility() {
    assert_source_retained(None);
}

#[test]
fn a_satisfied_member_does_not_skip_an_unsatisfied_import() {
    let directory = tempfile::tempdir().expect("directory");
    let base = Environment::with_prelude();
    write_artifact(&base, directory.path(), Artifact::Matching);
    let mut env = base;
    declare_module(&mut env, false, false);
    let mut context = importer(directory.path(), true);
    let error = apply_source(
        &mut env,
        &mut context,
        "import SourceSide MissingSourceMember\n",
    )
    .expect_err("the second import remains unresolved");
    assert!(error.to_string().contains("MissingSourceMember"), "{error}");
    assert!(!csimp::has_invalid_metadata(&env));
    assert!(env.get_const(&name("SourceSide.artifactOnly")).is_none());
}

#[test]
fn a_refused_source_stays_refused_even_with_a_valid_artifact() {
    let directory = tempfile::tempdir().expect("directory");
    let mut env = Environment::with_prelude();
    write_artifact(&env, directory.path(), Artifact::Matching);
    let mut context = importer(directory.path(), false);
    context.mark_import_refused_from_source(&name(MODULE), "source was rejected".into());
    context.mark_import_satisfied_from_source(&name(MODULE));
    let error = apply_source(&mut env, &mut context, "import SourceSide\n")
        .expect_err("a partial source module is not available");
    assert!(error.to_string().contains("source was rejected"), "{error}");
    assert!(env.get_const(&name("SourceSide.artifactOnly")).is_none());
    assert!(!csimp::has_invalid_metadata(&env));
}

#[test]
fn an_unmarked_import_still_loads_a_valid_source_artifact() {
    let directory = tempfile::tempdir().expect("directory");
    let mut env = Environment::with_prelude();
    write_artifact(&env, directory.path(), Artifact::Matching);
    let mut context = importer(directory.path(), false);
    apply_source(&mut env, &mut context, "import SourceSide\n").expect("artifact import");
    apply_source(
        &mut env,
        &mut context,
        "theorem Consumer.artifactProof : SourceSide.artifactOnly = 17 := rfl\n",
    )
    .expect("the imported artifact has its actual logical value");
    assert_eq!(
        env.declaration_verification(&name("Consumer.artifactProof")),
        Some(DeclarationVerification::FullKernelCheck)
    );
    assert!(context.import_visited().contains(MODULE));
    assert!(!csimp::has_invalid_metadata(&env));
    assert_eq!(
        env.get_constant_origin(&name("SourceSide.helper"))
            .and_then(|origin| origin.module_name()),
        Some(MODULE)
    );
}

#[test]
fn an_unmarked_import_still_refuses_a_stale_compiler_packet() {
    let directory = tempfile::tempdir().expect("directory");
    let mut env = Environment::with_prelude();
    write_artifact(&env, directory.path(), Artifact::StaleIdentity);
    let mut context = importer(directory.path(), false);
    let error = apply_source(&mut env, &mut context, "import SourceSide\n")
        .expect_err("stale metadata remains a refusal");
    assert!(
        error.to_string().contains("invalid compiler context"),
        "{error}"
    );
    assert!(csimp::has_invalid_metadata(&env));
}

#[test]
fn a_resident_source_is_not_artifact_provenance_without_its_source_marker() {
    let directory = tempfile::tempdir().expect("directory");
    let base = Environment::with_prelude();
    write_artifact(&base, directory.path(), Artifact::Matching);
    let mut env = base;
    declare_module(&mut env, false, false);
    let mut context = importer(directory.path(), false);
    apply_source(&mut env, &mut context, "import SourceSide\n")
        .expect_err("source must not acquire a foreign artifact's compiler provenance");
    assert!(csimp::has_invalid_metadata(&env));
}

#[test]
fn artifact_only_import_still_requires_an_artifact_for_checked_source() {
    let directory = tempfile::tempdir().expect("directory");
    let mut env = Environment::with_prelude();
    declare_module(&mut env, false, false);
    let satisfied_from_source = std::collections::HashSet::from([name(MODULE)]);
    let error = super::process_imports_shared_inner(
        &mut env,
        &[clean_parser::SurfaceName::generated_path(MODULE)],
        Ok(vec![directory.path().to_path_buf()]),
        &mut hashbrown::HashSet::new(),
        super::ImportResolution {
            policy: super::ImportPolicy::FailClosed,
            requires_artifact: true,
            satisfied_from_source: &satisfied_from_source,
        },
    )
    .expect_err("artifact-only import requires its own artifact");
    assert!(matches!(&error, ElabError::UnresolvedImport { module, .. } if module == MODULE));
    assert!(!csimp::has_invalid_metadata(&env));
}
