// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the "lazy default-on" closure-serve auto-discovery precedence
//! ([`super::decide_closure_serve`] / [`super::ClosureServeInputs`]).
//!
//! The PURE decision (`decide_closure_serve`) reads only directory contents, so
//! every precedence case is exercised with no env-var races and no `unsafe`
//! `set_var`. One serialized test wires `ClosureServeInputs::from_args_and_env`
//! to prove the `CLEAN_LAZY_CLOSURE=0` env override reaches `force_eager`.
//!
//! `#[path]`-included submodule of `stamp_verified_dispatch`, so `super::*`
//! resolves to that module's private items.

use super::*;
use std::sync::Mutex;

/// Make a populated cache dir (one `.mathverse` file) under `parent`.
fn populated_cache(parent: &Path, name: &str) -> PathBuf {
    let dir = parent.join(name);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("Init.mathverse"), b"\x00\x01\x02").unwrap();
    dir
}

/// Default inputs: nothing forced, no explicit dir, an EMPTY default cache, no
/// opt-in build. `default_dir` is a path under `parent` that does not exist.
fn base_inputs(parent: &Path) -> ClosureServeInputs {
    ClosureServeInputs {
        force_eager: false,
        explicit: None,
        default_dir: parent.join(".clean-closure-shards"),
        build_opt_in: false,
    }
}

// -- (3) auto-discover ---------------------------------------------------------

#[test]
fn test_autodiscover_populated_default_serves_lazily() {
    let tmp = tempfile::tempdir().unwrap();
    let cache = populated_cache(tmp.path(), ".clean-closure-shards");
    let mut inputs = base_inputs(tmp.path());
    inputs.default_dir = cache.clone();
    assert_eq!(decide_closure_serve(&inputs), ClosureServe::Lazy(cache));
}

// -- (5) eager when absent -----------------------------------------------------

#[test]
fn test_autodiscover_absent_default_falls_back_to_eager() {
    let tmp = tempfile::tempdir().unwrap();
    // default_dir does not exist -> not populated -> eager.
    let inputs = base_inputs(tmp.path());
    assert_eq!(decide_closure_serve(&inputs), ClosureServe::Eager);
}

#[test]
fn test_autodiscover_empty_default_falls_back_to_eager() {
    let tmp = tempfile::tempdir().unwrap();
    // An EMPTY default dir is not a usable cache -> eager.
    std::fs::create_dir_all(tmp.path().join(".clean-closure-shards")).unwrap();
    let inputs = base_inputs(tmp.path());
    assert_eq!(decide_closure_serve(&inputs), ClosureServe::Eager);
}

// -- (2) explicit override -----------------------------------------------------

#[test]
fn test_explicit_populated_override_wins_over_autodiscover() {
    let tmp = tempfile::tempdir().unwrap();
    let explicit = populated_cache(tmp.path(), "explicit");
    // ALSO populate the default dir; explicit must still win.
    let default = populated_cache(tmp.path(), ".clean-closure-shards");
    let inputs = ClosureServeInputs {
        force_eager: false,
        explicit: Some(explicit.clone()),
        default_dir: default,
        build_opt_in: false,
    };
    assert_eq!(decide_closure_serve(&inputs), ClosureServe::Lazy(explicit));
}

#[test]
fn test_explicit_missing_override_falls_back_to_eager() {
    let tmp = tempfile::tempdir().unwrap();
    let inputs = ClosureServeInputs {
        force_eager: false,
        explicit: Some(tmp.path().join("does-not-exist")),
        default_dir: tmp.path().join(".clean-closure-shards"),
        build_opt_in: false,
    };
    assert_eq!(decide_closure_serve(&inputs), ClosureServe::Eager);
}

// -- (1) force eager — the hard opt-out ----------------------------------------

#[test]
fn test_force_eager_beats_a_populated_explicit_cache() {
    let tmp = tempfile::tempdir().unwrap();
    let explicit = populated_cache(tmp.path(), "explicit");
    let default = populated_cache(tmp.path(), ".clean-closure-shards");
    let inputs = ClosureServeInputs {
        force_eager: true,
        explicit: Some(explicit),
        default_dir: default,
        build_opt_in: false,
    };
    // SOUNDNESS / opt-out: --no-lazy-closure (or CLEAN_LAZY_CLOSURE=0) forces
    // eager even when a populated cache exists.
    assert_eq!(decide_closure_serve(&inputs), ClosureServe::Eager);
}

// -- (4) opt-in build ----------------------------------------------------------

#[test]
fn test_no_cache_with_build_opt_in_requests_build_then_lazy() {
    let tmp = tempfile::tempdir().unwrap();
    let default = tmp.path().join(".clean-closure-shards");
    let inputs = ClosureServeInputs {
        force_eager: false,
        explicit: None,
        default_dir: default.clone(),
        build_opt_in: true,
    };
    assert_eq!(
        decide_closure_serve(&inputs),
        ClosureServe::BuildThenLazy(default)
    );
}

#[test]
fn test_no_cache_without_build_opt_in_is_eager() {
    let tmp = tempfile::tempdir().unwrap();
    let inputs = base_inputs(tmp.path());
    // No cache, no opt-in build -> a one-off run stays eager (never builds).
    assert_eq!(decide_closure_serve(&inputs), ClosureServe::Eager);
}

// -- env wiring (serialized) ---------------------------------------------------

/// Serialize the few tests that mutate the process-global env vars so they do
/// not race each other.
static ENV_LOCK: Mutex<()> = Mutex::new(());

/// Build a minimal `StampVerifiedArgs` with only the closure-serve-relevant
/// fields set; everything else defaulted.
fn args_for(out_dir: &Path) -> StampVerifiedArgs {
    StampVerifiedArgs {
        inputs: vec![],
        out_dir: out_dir.to_path_buf(),
        manifest: None,
        closure_root: Some(PathBuf::from("/unused")),
        closure_elide: crate::cli::ClosureElide::Opaque,
        json: false,
        single_pass: false,
        // PARAGON parallel-verify fields: these closure-serve tests exercise the
        // SEQUENTIAL lazy/eager precedence only, so parallelism is off.
        parallel: false,
        jobs: None,
        incremental: false,
        closure_shards: None,
        build_closure_cache: false,
        no_lazy_closure: false,
        receipt: None,
        receipt_leaves: None,
        receipt_provenance: None,
        source_id: None,
    }
}

/// `CLEAN_LAZY_CLOSURE=0` in the environment must reach `force_eager` and force
/// eager even when a populated co-located cache exists (the env opt-out still
/// works after killing the two-env-var dance).
#[test]
fn test_env_clean_lazy_closure_zero_forces_eager_even_with_cache() {
    let _guard = ENV_LOCK.lock().unwrap_or_else(|p| p.into_inner());
    let tmp = tempfile::tempdir().unwrap();
    // out_dir/stamped so the sibling default cache is out_dir/.clean-closure-shards.
    let out_dir = tmp.path().join("stamped");
    std::fs::create_dir_all(&out_dir).unwrap();
    populated_cache(tmp.path(), ".clean-closure-shards");

    let args = args_for(&out_dir);

    // Sanity: with no env, the populated co-located cache auto-discovers lazily.
    let _g_lazy = crate::process_env::ScopedEnvVar::unset("CLEAN_LAZY_CLOSURE");
    let _g_shards = crate::process_env::ScopedEnvVar::unset("CLEAN_CLOSURE_SHARDS");
    let _g_build = crate::process_env::ScopedEnvVar::unset("CLEAN_BUILD_CLOSURE_CACHE");
    let no_env = ClosureServeInputs::from_args_and_env(&args);
    assert!(
        !no_env.force_eager,
        "no env -> not forced eager (auto-discover should serve lazily)"
    );
    assert!(
        matches!(decide_closure_serve(&no_env), ClosureServe::Lazy(_)),
        "co-located cache must auto-discover to Lazy with no env vars"
    );

    // With CLEAN_LAZY_CLOSURE=0 -> force_eager -> Eager despite the cache.
    // Scoped so the override reverts (to the unset state above) right after.
    let forced = {
        let _g_lazy0 = crate::process_env::ScopedEnvVar::set("CLEAN_LAZY_CLOSURE", "0");
        ClosureServeInputs::from_args_and_env(&args)
    };
    assert!(
        forced.force_eager,
        "CLEAN_LAZY_CLOSURE=0 must set force_eager"
    );
    assert_eq!(
        decide_closure_serve(&forced),
        ClosureServe::Eager,
        "CLEAN_LAZY_CLOSURE=0 must force eager even with a populated cache"
    );
}

/// The `--no-lazy-closure` FLAG (no env) also forces eager — the flag opt-out.
#[test]
fn test_flag_no_lazy_closure_forces_eager_even_with_cache() {
    let _guard = ENV_LOCK.lock().unwrap_or_else(|p| p.into_inner());
    let tmp = tempfile::tempdir().unwrap();
    let out_dir = tmp.path().join("stamped");
    std::fs::create_dir_all(&out_dir).unwrap();
    populated_cache(tmp.path(), ".clean-closure-shards");

    let _g_lazy = crate::process_env::ScopedEnvVar::unset("CLEAN_LAZY_CLOSURE");
    let _g_shards = crate::process_env::ScopedEnvVar::unset("CLEAN_CLOSURE_SHARDS");
    let _g_build = crate::process_env::ScopedEnvVar::unset("CLEAN_BUILD_CLOSURE_CACHE");
    let mut args = args_for(&out_dir);
    args.no_lazy_closure = true;
    let inputs = ClosureServeInputs::from_args_and_env(&args);
    assert!(inputs.force_eager);
    assert_eq!(decide_closure_serve(&inputs), ClosureServe::Eager);
}

/// The `--closure-shards` FLAG (no env) is the explicit override and is read by
/// `from_args_and_env` ahead of auto-discovery.
#[test]
fn test_flag_closure_shards_is_explicit_override() {
    let _guard = ENV_LOCK.lock().unwrap_or_else(|p| p.into_inner());
    let tmp = tempfile::tempdir().unwrap();
    let out_dir = tmp.path().join("stamped");
    std::fs::create_dir_all(&out_dir).unwrap();
    let explicit = populated_cache(tmp.path(), "explicit");

    let _g_lazy = crate::process_env::ScopedEnvVar::unset("CLEAN_LAZY_CLOSURE");
    let _g_shards = crate::process_env::ScopedEnvVar::unset("CLEAN_CLOSURE_SHARDS");
    let _g_build = crate::process_env::ScopedEnvVar::unset("CLEAN_BUILD_CLOSURE_CACHE");
    let mut args = args_for(&out_dir);
    args.closure_shards = Some(explicit.clone());
    let inputs = ClosureServeInputs::from_args_and_env(&args);
    assert_eq!(inputs.explicit.as_deref(), Some(explicit.as_path()));
    assert_eq!(decide_closure_serve(&inputs), ClosureServe::Lazy(explicit));
}

// -- end-to-end build-then-serve over the Minimal fixture ----------------------

/// Path to the committed `Minimal.olean` fixture (imports exactly `Init`).
fn minimal_olean() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|p| p.parent())
        .map(|root| root.join("tests/fixtures/olean/v4.13.0/custom/Minimal.olean"))
        .expect("workspace root")
}

/// The opt-in `--build-closure-cache` path actually BUILDS a populated cache
/// over the Minimal fixture's import closure, after which `resolve_closure_serve`
/// returns a terminal `Lazy(default_dir)` pointing at the freshly-built cache —
/// the re-import workflow end to end (build once, then auto-discover lazily).
#[test]
fn test_resolve_build_opt_in_builds_then_serves_lazily() {
    let _guard = ENV_LOCK.lock().unwrap_or_else(|p| p.into_inner());
    let _g_lazy = crate::process_env::ScopedEnvVar::unset("CLEAN_LAZY_CLOSURE");
    let _g_shards = crate::process_env::ScopedEnvVar::unset("CLEAN_CLOSURE_SHARDS");
    let _g_build = crate::process_env::ScopedEnvVar::unset("CLEAN_BUILD_CLOSURE_CACHE");

    // Resolvable single-module closure: <root>/Init.olean + <root>/Target.olean.
    let root = tempfile::tempdir().unwrap();
    let init = root.path().join("Init.olean");
    std::fs::copy(minimal_olean(), &init).expect("copy Init.olean");
    let target = root.path().join("Target.olean");
    std::fs::copy(minimal_olean(), &target).expect("copy Target.olean");

    // out_dir sibling -> default cache is <out_dir>/../.clean-closure-shards.
    let work = tempfile::tempdir().unwrap();
    let out_dir = work.path().join("stamped");
    std::fs::create_dir_all(&out_dir).unwrap();
    let expected_cache = default_closure_cache_dir(&out_dir);

    let mut args = args_for(&out_dir);
    args.closure_root = Some(root.path().to_path_buf());
    args.build_closure_cache = true;

    // No cache yet -> the pure decision requests a build.
    let inputs = ClosureServeInputs::from_args_and_env(&args);
    assert_eq!(
        decide_closure_serve(&inputs),
        ClosureServe::BuildThenLazy(expected_cache.clone())
    );

    // resolve_closure_serve performs the build, then returns terminal Lazy.
    let oleans = vec![target];
    let decision = resolve_closure_serve(&args, &oleans, root.path());
    assert_eq!(
        decision,
        ClosureServe::Lazy(expected_cache.clone()),
        "opt-in build must populate the default cache and serve lazily"
    );
    assert!(
        cache_dir_is_populated(&expected_cache),
        "the cache must actually have been built (non-empty)"
    );

    // A subsequent run with NO build flag now AUTO-DISCOVERS the same cache.
    let mut rerun = args_for(&out_dir);
    rerun.closure_root = Some(root.path().to_path_buf());
    rerun.build_closure_cache = false;
    let rerun_inputs = ClosureServeInputs::from_args_and_env(&rerun);
    assert_eq!(
        decide_closure_serve(&rerun_inputs),
        ClosureServe::Lazy(expected_cache),
        "re-import auto-discovers the built cache with no flags/env"
    );
}
