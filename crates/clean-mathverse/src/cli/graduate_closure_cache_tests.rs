// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the content-addressed cached closure loader. Seeded by the committed
//! `tests/fixtures/olean/v4.13.0/custom/Minimal.olean` (def `identity` + theorem
//! `id_id`, imports exactly `Init`) so they run with no Mathlib checkout — the same
//! fixture the v3 closure-binding tests use.
//!
//! `#[path]`-included submodule of `graduate_closure_cache`, so `super::*` resolves
//! to that module's private items (including the private `CachePlan` fields).

use super::*;
use clean_kernel::env::ConstantInfo;
use clean_kernel::Environment;

/// Serializes the two tests that touch the process-global `$CLEAN_CLOSURE_CACHE_DIR`.
static ENV_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

/// Path to the committed `Minimal.olean` fixture.
fn minimal_olean() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|p| p.parent())
        .map(|root| root.join("tests/fixtures/olean/v4.13.0/custom/Minimal.olean"))
        .expect("workspace root")
}

/// Lay out a resolvable closure under `root`: `Init.olean` + `Target.olean` (both
/// copies of the fixture). `Target` imports `Init`, so the closure is `{Target, Init}`.
fn layout_minimal_closure(root: &Path) -> PathBuf {
    std::fs::create_dir_all(root).unwrap();
    std::fs::copy(minimal_olean(), root.join("Init.olean")).expect("copy Init.olean");
    let target = root.join("Target.olean");
    std::fs::copy(minimal_olean(), &target).expect("copy Target.olean");
    target
}

/// Build a `CachePlan` for the `{Target, Init}` closure rooted at `root`, with the
/// per-digest entry directory nested under `cache_root`.
fn plan_for(root: &Path, cache_root: &Path) -> CachePlan {
    let search_paths = vec![root.to_path_buf()];
    let modules = vec!["Target".to_string()];
    let target_oleans = vec![root.join("Target.olean")];
    let (closure_modules, closure_oleans) = closure_bfs(&modules, &search_paths);
    let union_digest_hex = compute_union_digest(&closure_oleans).expect("union digest");
    let entry_dir = cache_root.join(&union_digest_hex);
    CachePlan {
        search_paths,
        root: root.to_path_buf(),
        target_oleans,
        closure_modules,
        closure_oleans,
        union_digest_hex,
        entry_dir,
    }
}

/// The eager (cold) env graduate would build today: `load_modules_with_deps` over
/// the declared modules + search paths into a bare default env.
fn cold_env(root: &Path) -> Environment {
    let mut env = Environment::default();
    clean_olean::load_modules_with_deps(&mut env, &["Target".to_string()], &[root.to_path_buf()])
        .expect("cold load");
    env
}

/// `(kind, level_params, has_value)` plus structural type/value equality, the same
/// MData-peeling oracle the round-trip uses. Minimal has ZERO MData, so this is an
/// exact structural compare here.
fn const_equal(a: &ConstantInfo, b: &ConstantInfo) -> bool {
    a.kind == b.kind
        && a.level_params == b.level_params
        && a.value.is_some() == b.value.is_some()
        && crate::inductive_replay::types_equal_ignoring_binder_info(&a.type_, &b.type_)
        && match (&a.value, &b.value) {
            (Some(av), Some(bv)) => {
                crate::inductive_replay::types_equal_ignoring_binder_info(av, bv)
            }
            (None, None) => true,
            _ => false,
        }
}

// -- (a) round-trip faithfulness ----------------------------------------------

/// The warm fast-load is byte/structurally FAITHFUL to the cold reconstruction:
/// same constant-name set, and every shared constant is structurally equal
/// (kind, level params, type, value).
#[test]
fn test_warm_load_is_faithful_to_cold() {
    let root = tempfile::tempdir().unwrap();
    let cache = tempfile::tempdir().unwrap();
    layout_minimal_closure(root.path());
    let plan = plan_for(root.path(), cache.path());

    // First load is a MISS: nothing populated yet.
    assert!(
        fast_load(&plan).is_none(),
        "an unpopulated entry must be a MISS"
    );

    // Cold-load, then populate the cache (what graduate does on a miss).
    let cold = cold_env(root.path());
    populate(&plan);

    // Warm fast-load must now hit.
    let warm = fast_load(&plan).expect("warm load must hit after populate");

    // Same constant-name set.
    let cold_names: BTreeSet<String> = cold.constants().map(|c| c.name.to_string()).collect();
    let warm_names: BTreeSet<String> = warm.constants().map(|c| c.name.to_string()).collect();
    assert_eq!(
        cold_names, warm_names,
        "warm closure must carry exactly the cold closure's constants"
    );
    assert!(
        cold_names.contains("identity") && cold_names.contains("id_id"),
        "the Minimal fixture's own decls must be present (non-vacuous): {cold_names:?}"
    );

    // Every shared constant is structurally identical.
    for c in cold.constants() {
        let w = warm.get_const(&c.name).expect("warm has the name");
        assert!(
            const_equal(c, w),
            "constant `{}` diverges warm-vs-cold",
            c.name
        );
    }
}

// -- (b) fail-closed: tampered cache ------------------------------------------

/// A manifest whose recorded union digest does not match the plan's (a swapped /
/// foreign / recipe-mismatched entry) is REJECTED => fast_load falls back.
#[test]
fn test_tampered_manifest_digest_rejected() {
    let root = tempfile::tempdir().unwrap();
    let cache = tempfile::tempdir().unwrap();
    layout_minimal_closure(root.path());
    let plan = plan_for(root.path(), cache.path());
    populate(&plan);
    assert!(fast_load(&plan).is_some(), "control: populated entry hits");

    // Corrupt the manifest's union digest in place.
    let manifest_path = plan.entry_dir.join("manifest.json");
    let raw = std::fs::read_to_string(&manifest_path).unwrap();
    let mut m: serde_json::Value = serde_json::from_str(&raw).unwrap();
    m["union_digest"] = serde_json::Value::String("deadbeef".repeat(8));
    std::fs::write(&manifest_path, serde_json::to_vec(&m).unwrap()).unwrap();

    assert!(
        fast_load(&plan).is_none(),
        "a digest-mismatched manifest must fail closed to reconstruction"
    );
}

/// Tampering the underlying `.olean` AFTER populate breaks the per-shard
/// source-olean binding for that module => its shard goes unverified => the
/// coverage gate fails => fast_load falls back (the binding catches a stale/swapped
/// olean even though the manifest digest still matches the precomputed plan).
#[test]
fn test_tampered_shard_binding_rejected() {
    let root = tempfile::tempdir().unwrap();
    let cache = tempfile::tempdir().unwrap();
    layout_minimal_closure(root.path());
    let plan = plan_for(root.path(), cache.path());
    populate(&plan);
    assert!(fast_load(&plan).is_some(), "control: populated entry hits");

    // Append bytes to Init.olean: its live source digest no longer matches the
    // shard header's stamped digest.
    let init = root.path().join("Init.olean");
    let mut bytes = std::fs::read(&init).unwrap();
    bytes.extend_from_slice(b"TAMPER");
    std::fs::write(&init, bytes).unwrap();

    assert!(
        fast_load(&plan).is_none(),
        "a shard bound to a now-mismatched .olean must fail closed"
    );
}

/// A corrupt shard FILE (truncated arena) cannot serve its constants => fast_load
/// falls back (decode/materialize tripwire).
#[test]
fn test_corrupt_shard_bytes_rejected() {
    let root = tempfile::tempdir().unwrap();
    let cache = tempfile::tempdir().unwrap();
    layout_minimal_closure(root.path());
    let plan = plan_for(root.path(), cache.path());
    populate(&plan);
    assert!(fast_load(&plan).is_some(), "control: populated entry hits");

    // Truncate every shard file to a stub — no valid header/arena remains.
    for entry in std::fs::read_dir(&plan.entry_dir).unwrap() {
        let p = entry.unwrap().path();
        if p.extension().is_some_and(|x| x == "mathverse") {
            std::fs::write(&p, b"\x00\x01\x02").unwrap();
        }
    }

    assert!(
        fast_load(&plan).is_none(),
        "corrupt shard bytes must fail closed (no silent wrong closure)"
    );
}

// -- (c) cache OFF by default + content-addressing ----------------------------

/// With `$CLEAN_CLOSURE_CACHE_DIR` UNSET, `decide` is `Disabled` (the caller runs
/// the unchanged eager load); with it SET, the first decision is a `Miss` and, after
/// populating from its plan, the second decision is a `Hit`.
#[test]
fn test_cache_off_by_default_then_opt_in_roundtrip() {
    let _guard = ENV_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let root = tempfile::tempdir().unwrap();
    let cache = tempfile::tempdir().unwrap();
    layout_minimal_closure(root.path());
    let modules = vec!["Target".to_string()];
    let search_paths = vec![root.path().to_path_buf()];

    // All CACHE_DIR_ENV manipulation is scoped: `with_env_edits` restores the
    // ambient value on exit (even on panic).
    crate::process_env::with_env_edits(|env| {
        // OFF by default: no env var => Disabled, regardless of fixtures on disk.
        env.remove(CACHE_DIR_ENV);
        assert!(
            matches!(
                decide(&modules, &search_paths, None),
                CacheDecision::Disabled
            ),
            "unset $CLEAN_CLOSURE_CACHE_DIR must bypass the cache"
        );

        // Opt in: first decision is a MISS carrying a plan.
        env.set(CACHE_DIR_ENV, &cache.path().to_string_lossy());
        let plan = match decide(&modules, &search_paths, None) {
            CacheDecision::Miss(plan) => plan,
            _ => panic!("first decision with an empty cache must be a MISS"),
        };
        populate(&plan);

        // Second decision is a HIT.
        let hit = matches!(decide(&modules, &search_paths, None), CacheDecision::Hit(_));
        assert!(hit, "after populate, the same closure must be a cache HIT");
    });
}

/// The union digest is deterministic for identical inputs and content-sensitive:
/// mutating any closure `.olean` changes the key.
#[test]
fn test_union_digest_is_content_addressed() {
    let root = tempfile::tempdir().unwrap();
    layout_minimal_closure(root.path());
    let (_m, oleans) = closure_bfs(&["Target".to_string()], &[root.path().to_path_buf()]);

    let d1 = compute_union_digest(&oleans).expect("digest");
    let d2 = compute_union_digest(&oleans).expect("digest");
    assert_eq!(d1, d2, "same olean set must yield the same key");

    // Mutate Init.olean: the key must change (content-addressing).
    let init = root.path().join("Init.olean");
    let mut bytes = std::fs::read(&init).unwrap();
    bytes.extend_from_slice(b"X");
    std::fs::write(&init, bytes).unwrap();
    let d3 = compute_union_digest(&oleans).expect("digest");
    assert_ne!(d1, d3, "a changed olean must change the content-address");
}
