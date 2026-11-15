// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::import::load_parse::parse_load_module;
use crate::import::load_register::load_module_direct_with_cache;
use crate::import::{
    load_module_with_deps_cached, load_olean_file, load_parsed_module, parse_module,
    ExprInternCache, ModuleCache,
};
use crate::{CleanPayload, OleanExporter};
use clean_kernel::{Declaration, Expr};
use std::path::Path;

const HASH: &str = "0000000000000000000000000000000000000000";

fn clean(name: &str) -> Vec<u8> {
    let mut env = Environment::default();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("fixture declaration");
    let payload = CleanPayload {
        constants: env.constants().cloned().collect(),
        ..CleanPayload::default()
    };
    OleanExporter::export_with_env_and_payload(&env, &[], &[], HASH, &payload)
        .expect("Clean payload fixture")
}

fn genuine() -> Vec<u8> {
    std::fs::read(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/fixtures/olean/v4.13.0/custom/Minimal.olean"),
    )
    .expect("tracked genuine Lean fixture")
}

fn refused(error: ImportError, label: &str) {
    assert!(error.is_inconsistent_artifact(), "no warning/stub fallback");
    assert!(matches!(error, ImportError::CleanPayloadRequired { module } if module == label));
}

#[test]
fn clean_payload_requirement_unmarked_genuine_and_marked_clean_load() {
    let mut ordinary = Environment::with_prelude();
    let part = parse_load_module(genuine()).expect("genuine parsed object");
    assert!(part.clean_payload.is_none());
    load_module_direct_with_cache(
        &mut ordinary,
        &part,
        Some("Genuine".into()),
        &mut ExprInternCache::default(),
    )
    .expect("genuine remains admitted in an ordinary environment");
    assert!(ordinary.get_const(&Name::from_string("identity")).is_some());

    let mut bootstrap = Environment::default();
    require_clean_payload_imports(&mut bootstrap);
    let part = parse_load_module(clean("Clean.accepted")).expect("Clean parsed object");
    load_module_direct_with_cache(
        &mut bootstrap,
        &part,
        Some("Clean".into()),
        &mut ExprInternCache::default(),
    )
    .expect("marked environment accepts validated Clean payload");
    assert!(bootstrap
        .get_const(&Name::from_string("Clean.accepted"))
        .is_some());
}

#[test]
fn clean_payload_requirement_direct_rejects_consumed_genuine_object_without_mutation() {
    let dir = tempfile::tempdir().expect("fixture");
    let path = dir.path().join("Library.olean");
    std::fs::write(&path, genuine()).expect("genuine replacement");
    let consumed = parse_load_module(std::fs::read(&path).expect("read consumed bytes"))
        .expect("actual genuine parse")
        .read_from(&path);
    // A later clean pathname must not license the already parsed object.
    std::fs::write(&path, clean("Library.after")).expect("restore pathname");
    let mut env = Environment::default();
    require_clean_payload_imports(&mut env);
    let before = env.generation();
    refused(
        load_module_direct_with_cache(
            &mut env,
            &consumed,
            Some("Library".into()),
            &mut ExprInternCache::default(),
        )
        .expect_err("actual consumed bytes govern"),
        "Library",
    );
    assert_eq!(env.generation(), before);
    assert!(crate::import::world_gate::environment_world(&env).is_none());
    assert!(env.get_const(&Name::from_string("identity")).is_none());
    load_olean_file(&mut env, &path).expect("refusal left no poisoned artifact binding");
    assert!(env.get_const(&Name::from_string("Library.after")).is_some());
}

#[test]
fn clean_payload_requirement_parsed_projection_refuses_before_registration() {
    let parsed = parse_module(&genuine()).expect("legacy ParsedModule");
    let mut env = Environment::default();
    require_clean_payload_imports(&mut env);
    let before = env.generation();
    refused(
        load_parsed_module(&mut env, &parsed, Some("Projected".into()))
            .expect_err("legacy entry cannot bypass local requirement"),
        "Projected",
    );
    assert_eq!(env.generation(), before);
    let clean = parse_module(&clean("Projected.accepted")).expect("Clean projection");
    load_parsed_module(&mut env, &clean, Some("Projected".into()))
        .expect("Clean projection still loads after refusal");
}

#[test]
fn clean_payload_requirement_clones_retain_nonexported_monotonic_policy() {
    let mut source = Environment::default();
    require_clean_payload_imports(&mut source);
    require_clean_payload_imports(&mut source);
    let mut cloned = source.clone();
    cloned.materialize_extension_states();
    let state = cloned
        .get_ext_state::<CleanPayloadRequirement>(requirement_idx())
        .expect("local requirement cloned");
    assert!(state.required);
    assert!(state.export_entries().is_empty());
    let projected = parse_module(&genuine()).expect("genuine projection");
    refused(
        load_parsed_module(&mut cloned, &projected, Some("Clone".into()))
            .expect_err("clone retains requirement"),
        "Clone",
    );
    let fresh = Environment::default();
    assert!(check_parsed_module(&fresh, &projected, Some("Unmarked")).is_ok());
}

#[test]
fn clean_payload_requirement_warm_cache_does_not_grant_permission() {
    let dir = tempfile::tempdir().expect("fixture");
    let path = dir.path().join("Library.olean");
    // A valid payloadless Clean layout has no dependencies and can warm the
    // same production typed cache without invoking unrelated SDK lookup.
    let bytes = OleanExporter::export_minimal(&[], &[], &[], HASH).expect("payloadless layout");
    std::fs::write(&path, &bytes).expect("payloadless library");
    let paths = [dir.path().to_path_buf()];
    let cache = ModuleCache::new();
    load_module_with_deps_cached(&mut Environment::default(), "Library", &paths, &cache)
        .expect("ordinary warm population");
    assert_eq!(cache.len(), 1);
    let mut marked = Environment::default();
    require_clean_payload_imports(&mut marked);
    let mut clone = marked.clone();
    for env in [&mut marked, &mut clone] {
        let before = env.generation();
        refused(
            load_module_with_deps_cached(env, "Library", &paths, &cache)
                .expect_err("same cache hit must enforce environment requirement"),
            "Library",
        );
        assert_eq!(env.generation(), before);
        assert!(crate::import::world_gate::environment_world(env).is_none());
    }
    std::fs::write(&path, clean("Library.changed")).expect("change captured identity");
    load_module_with_deps_cached(&mut marked, "Library", &paths, &cache)
        .expect("changed Clean content does not retain a stale refusal");
    assert!(marked
        .get_const(&Name::from_string("Library.changed"))
        .is_some());
}

#[test]
fn clean_payload_requirement_companion_checks_actual_parts() {
    let base_bytes = clean("Library.base");
    let mut companion_bytes = OleanExporter::export_with_payload_after(
        &base_bytes,
        &[],
        &[],
        &[],
        HASH,
        &CleanPayload::default(),
    )
    .expect("canonical sequential companion");
    let footer = crate::encode_clean_payload(&CleanPayload::default()).expect("empty footer");
    assert!(companion_bytes.ends_with(&footer));
    companion_bytes.truncate(companion_bytes.len() - footer.len());
    let base = parse_load_module(base_bytes.clone()).expect("base actual parse");
    let companion = crate::import::load_parse::parse_load_module_incremental(
        &base_bytes,
        None,
        companion_bytes,
    )
    .expect("valid payloadless companion actual parse");
    assert!(base.clean_payload.is_some());
    assert!(companion.clean_payload.is_none());
    let mut marked = Environment::default();
    require_clean_payload_imports(&mut marked);
    refused(
        check_artifact_parts(&marked, "Library", &base, Some(&companion), None)
            .expect_err("server cannot inherit base permission"),
        "Library._server",
    );
    refused(
        check_artifact_parts(&marked, "Library", &base, None, Some(&companion))
            .expect_err("private cannot inherit base permission"),
        "Library._private",
    );
}

#[test]
fn clean_payload_requirement_cached_companion_refuses_before_base_and_allows_retry() {
    let dir = tempfile::tempdir().expect("fixture");
    let path = dir.path().join("Library.olean");
    let base = clean("Library.base");
    let complete_server = OleanExporter::export_with_payload_after(
        &base,
        &[],
        &[],
        &[],
        HASH,
        &CleanPayload::default(),
    )
    .expect("canonical server");
    let mut payloadless_server = complete_server.clone();
    let footer = crate::encode_clean_payload(&CleanPayload::default()).expect("footer");
    assert!(payloadless_server.ends_with(&footer));
    payloadless_server.truncate(payloadless_server.len() - footer.len());
    std::fs::write(&path, &base).expect("base");
    std::fs::write(path.with_extension("olean.server"), payloadless_server).expect("server");
    let paths = [dir.path().to_path_buf()];
    let mut ordinary_marked = Environment::default();
    require_clean_payload_imports(&mut ordinary_marked);
    let ordinary_before = ordinary_marked.generation();
    refused(
        crate::load_module_with_deps(&mut ordinary_marked, "Library", &paths)
            .expect_err("ordinary loader checks every part before registering the base"),
        "Library._server",
    );
    assert_eq!(ordinary_marked.generation(), ordinary_before);
    assert!(ordinary_marked
        .get_const(&Name::from_string("Library.base"))
        .is_none());
    let cache = ModuleCache::new();
    load_module_with_deps_cached(&mut Environment::default(), "Library", &paths, &cache)
        .expect("identical parts are structurally valid in an unmarked environment");
    let mut marked = Environment::default();
    require_clean_payload_imports(&mut marked);
    let before = marked.generation();
    refused(
        load_module_with_deps_cached(&mut marked, "Library", &paths, &cache)
            .expect_err("warm complete artifact cannot register its base first"),
        "Library._server",
    );
    assert_eq!(marked.generation(), before);
    assert!(marked
        .get_const(&Name::from_string("Library.base"))
        .is_none());
    std::fs::write(path.with_extension("olean.server"), &complete_server).expect("restore payload");
    crate::load_module_with_deps(&mut ordinary_marked, "Library", &paths)
        .expect("ordinary loader also retries successfully after its clean refusal");
    assert!(ordinary_marked
        .get_const(&Name::from_string("Library.base"))
        .is_some());
    load_module_with_deps_cached(&mut marked, "Library", &paths, &cache)
        .expect("no partial base/ledger mutation poisoned the retry");
    assert!(marked
        .get_const(&Name::from_string("Library.base"))
        .is_some());
}
