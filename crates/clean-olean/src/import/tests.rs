// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for .olean import functionality.

use super::{
    convert_expr, decl_to_constant_info, load_module_direct_with_cache,
    load_module_with_deps_bounded, load_module_with_deps_bounded_shared, load_parsed_module,
    load_parsed_module_with_import_policy, module_name_from_path, parse_load_module,
    read_and_convert_expr, ExprInternCache, ImportError, ModuleCache, OleanImportPolicy,
    UnpinnedOleanImportPolicy,
};
use crate::expr::ParsedExpr;
use crate::module::{
    ParsedExtension, ParsedExtensionEntry, ParsedExtensionEntryData, ParsedModule,
    ReducibilityHintsData,
};
use clean_kernel::env::{Declaration, Environment, OriginTrust, Reducibility, TrustedEnvExt};
use clean_kernel::expr::Expr;
use clean_kernel::name::Name;
use std::collections::HashMap;
use std::env;
use std::fs;
use std::path::Path;
use std::time::Duration;
use tempfile::{NamedTempFile, TempDir};

/// DIAGNOSTIC (ignored, full v4.30 stdlib): load every module two ways —
/// per-module loop with a fresh `visited` each call (legacy) vs the
/// shared-`visited` `load_modules_with_deps` (the fix) — and dump which
/// constants differ to /tmp. Resolves whether the batch summary's 215709→212647
/// drop is real load-level loss (per-loop has constants shared lacks) or the old
/// per-loop path OVER-counting via re-walks (shared lacks nothing real).
#[test]
#[ignore = "diagnostic: full toolchain load, ~1h; requires local v4.30.0 oleans"]
fn diag_full_shared_vs_perloop() {
    use std::collections::HashSet as StdHashSet;
    use std::io::Write;
    use std::path::PathBuf;

    let home = env::var("HOME").expect("HOME");
    let lib = PathBuf::from(&home).join(".elan/toolchains/leanprover--lean4---v4.30.0/lib/lean");
    if !lib.join("Init.olean").exists() {
        eprintln!("SKIP: no v4.30.0 toolchain at {}", lib.display());
        return;
    }
    let paths = vec![lib.clone()];

    fn walk(dir: &Path, out: &mut Vec<std::path::PathBuf>) {
        if let Ok(rd) = fs::read_dir(dir) {
            for e in rd.flatten() {
                let p = e.path();
                if p.is_dir() {
                    walk(&p, out);
                } else if p.extension().and_then(|s| s.to_str()) == Some("olean") {
                    out.push(p);
                }
            }
        }
    }
    let mut files = Vec::new();
    walk(&lib, &mut files);
    let modules: Vec<String> = files
        .iter()
        .map(|p| {
            let rel = p.strip_prefix(&lib).expect("under lib").with_extension("");
            rel.components()
                .filter_map(|c| c.as_os_str().to_str())
                .collect::<Vec<_>>()
                .join(".")
        })
        .collect();
    eprintln!("discovered {} modules", modules.len());

    let names = |env: &Environment| -> StdHashSet<String> {
        let mut s = StdHashSet::new();
        for c in env.constants() {
            s.insert(c.name.to_string());
        }
        for i in env.inductives() {
            s.insert(i.name.to_string());
        }
        for c in env.constructors() {
            s.insert(c.name.to_string());
        }
        for r in env.recursors() {
            s.insert(r.name.to_string());
        }
        s
    };

    let mut env_a = Environment::default();
    for m in &modules {
        let _ = crate::load_module_with_deps(&mut env_a, m, &paths);
    }
    let a = names(&env_a);
    eprintln!("per-loop (fresh visited): {} names", a.len());
    drop(env_a);

    let mut env_b = Environment::default();
    let _ = crate::load_modules_with_deps(&mut env_b, &modules, &paths);
    let b = names(&env_b);
    eprintln!("shared (load_modules):   {} names", b.len());

    let mut only_a: Vec<&String> = a.difference(&b).collect();
    let mut only_b: Vec<&String> = b.difference(&a).collect();
    only_a.sort();
    only_b.sort();
    eprintln!(
        "ONLY in per-loop: {}  | ONLY in shared: {}",
        only_a.len(),
        only_b.len()
    );
    if let Ok(mut f) = fs::File::create("/tmp/diag_only_in_perloop.txt") {
        for n in &only_a {
            let _ = writeln!(f, "{n}");
        }
    }
    for n in only_a.iter().take(60) {
        eprintln!("  - {n}");
    }
    for n in only_b.iter().take(20) {
        eprintln!("  + {n}");
    }
}

fn write_empty_olean(path: &Path) {
    let parent = path.parent().expect("fixture parent");
    fs::create_dir_all(parent).expect("create fixture directories");
    fs::write(path, []).expect("write olean fixture");
}

fn dummy_module() -> ParsedModule {
    ParsedModule {
        const_names: Vec::new(),
        constants: Vec::new(),
        extra_const_names: Vec::new(),
        imports: Vec::new(),
        entries: Vec::new(),
        clean_payload: None,
    }
}

fn module_with_extension(extension_name: &str, entry_name: &str) -> ParsedModule {
    ParsedModule {
        const_names: Vec::new(),
        constants: Vec::new(),
        extra_const_names: Vec::new(),
        imports: Vec::new(),
        entries: vec![ParsedExtension {
            extension_name: extension_name.to_string(),
            entries: vec![ParsedExtensionEntry::Named {
                name: entry_name.to_string(),
                data: ParsedExtensionEntryData::Scalar(0),
            }],
            undecoded_entries: 0,
        }],
        clean_payload: None,
    }
}

/// Build a `ParsedModule` whose `instanceExtension` persistent extension carries
/// the given instances, encoded exactly as the kernel serializes them. This
/// mirrors how a real `.olean` persists `@[instance]` registrations.
fn module_with_instances(instances: &[(&str, &str, u32)]) -> ParsedModule {
    use clean_kernel::env::{EnvExtensionEntryData, InstanceExtEntry, PersistentExtEntry};

    let entries = instances
        .iter()
        .map(|(instance_name, class_name, priority)| {
            let raw = InstanceExtEntry {
                instance_name: Name::from_string(instance_name),
                class_name: Name::from_string(class_name),
                priority: *priority,
            }
            .to_env_entry();
            let data = match raw.data {
                EnvExtensionEntryData::Object(bytes) => ParsedExtensionEntryData::Object(bytes),
                EnvExtensionEntryData::Scalar(v) => ParsedExtensionEntryData::Scalar(v),
            };
            ParsedExtensionEntry::Named {
                name: raw.name.to_string(),
                data,
            }
        })
        .collect();

    ParsedModule {
        const_names: Vec::new(),
        constants: Vec::new(),
        extra_const_names: Vec::new(),
        imports: Vec::new(),
        entries: vec![ParsedExtension {
            extension_name: "instanceExtension".to_string(),
            entries,
            undecoded_entries: 0,
        }],
        clean_payload: None,
    }
}

/// Build a `ParsedModule` whose `simpExtension` persistent extension carries the
/// given `@[simp]` lemmas, encoded exactly as the kernel serializes them. This
/// mirrors how a real `.olean` persists `@[simp]` registrations.
fn module_with_simp_lemmas(lemmas: &[(&str, clean_kernel::env::SimpPriority)]) -> ParsedModule {
    use clean_kernel::env::{EnvExtensionEntryData, PersistentExtEntry, SimpExtEntry};

    let entries = lemmas
        .iter()
        .map(|(lemma_name, priority)| {
            let raw = SimpExtEntry {
                name: Name::from_string(lemma_name),
                priority: *priority,
            }
            .to_env_entry();
            let data = match raw.data {
                EnvExtensionEntryData::Object(bytes) => ParsedExtensionEntryData::Object(bytes),
                EnvExtensionEntryData::Scalar(v) => ParsedExtensionEntryData::Scalar(v),
            };
            ParsedExtensionEntry::Named {
                name: raw.name.to_string(),
                data,
            }
        })
        .collect();

    ParsedModule {
        const_names: Vec::new(),
        constants: Vec::new(),
        extra_const_names: Vec::new(),
        imports: Vec::new(),
        entries: vec![ParsedExtension {
            extension_name: "simpExtension".to_string(),
            entries,
            undecoded_entries: 0,
        }],
        clean_payload: None,
    }
}

/// Build a `ParsedModule` whose `attrExtension` persistent extension carries the
/// given `(decl_name, attr_name, priority)` attribute registrations, encoded
/// exactly as the kernel serializes them. This mirrors how a real `.olean`
/// persists `@[reducible]`/`@[irreducible]`/… registrations.
fn module_with_attributes(attrs: &[(&str, &str, u32)]) -> ParsedModule {
    use clean_kernel::env::{AttrExtEntry, EnvExtensionEntryData, PersistentExtEntry};

    let entries = attrs
        .iter()
        .map(|(decl_name, attr_name, priority)| {
            let raw = AttrExtEntry {
                decl_name: Name::from_string(decl_name),
                attr_name: Name::from_string(attr_name),
                priority: *priority,
            }
            .to_env_entry();
            let data = match raw.data {
                EnvExtensionEntryData::Object(bytes) => ParsedExtensionEntryData::Object(bytes),
                EnvExtensionEntryData::Scalar(v) => ParsedExtensionEntryData::Scalar(v),
            };
            ParsedExtensionEntry::Named {
                name: raw.name.to_string(),
                data,
            }
        })
        .collect();

    ParsedModule {
        const_names: Vec::new(),
        constants: Vec::new(),
        extra_const_names: Vec::new(),
        imports: Vec::new(),
        entries: vec![ParsedExtension {
            extension_name: "attrExtension".to_string(),
            entries,
            undecoded_entries: 0,
        }],
        clean_payload: None,
    }
}

/// Build a single-entry `attrExtension` `ParsedModule` carrying one
/// `(decl_name, attr_name)` registration, paired with a semireducible
/// definition `Declaration` for `decl_name` that a test should add to the
/// environment first (via `add_decl_structural`) so the bridge has a constant
/// to act on.
fn semireducible_def_decl(def_name: &str) -> Declaration {
    Declaration::Definition {
        name: Name::from_string(def_name),
        level_params: vec![],
        type_: Expr::type_(),
        value: Expr::prop(),
        // `is_reducible: false` lands the constant at a `Regular(_)`
        // (semireducible) default height — never `Reducible`; the bridge must
        // override it to `Reducible`/`Irreducible`.
        is_reducible: false,
    }
}

#[test]
fn test_module_name_from_sample_path() {
    let path =
        Path::new("/tmp/.elan/toolchains/leanprover--lean4---v4.3.0/lib/lean/Init/Core.olean");
    let name = module_name_from_path(path);
    assert_eq!(name.as_deref(), Some("Init.Core"));
}

#[test]
fn test_bounded_module_loader_rejects_over_budget_before_io() {
    let mut env = Environment::new();
    let err = load_module_with_deps_bounded(&mut env, "Lean.Elab.Tactic", &[], 0).unwrap_err();

    match err {
        ImportError::UnsupportedModule { module, reason } => {
            assert_eq!(module, "Lean.Elab.Tactic");
            assert!(
                reason.contains("bounded loader limit"),
                "expected bounded-loader diagnostic, got {reason}"
            );
        }
        other => panic!("expected UnsupportedModule, got {other:?}"),
    }
}

#[test]
fn test_shared_loader_skips_module_already_in_visited_set_without_io() {
    // The shared-env closure cache: a module already present in the caller's
    // `visited` set must be skipped WITHOUT touching the filesystem. We seed
    // `visited` with a module name that does not resolve under empty search
    // paths; if the loader honored `visited` it returns Ok with no summaries,
    // and if it ignored `visited` it would fail path resolution. This is the
    // property that lets the closure env be reused across many target modules.
    let mut env = Environment::new();
    let mut visited = hashbrown::HashSet::new();
    visited.insert("Some.Nonexistent.Module".to_string());

    let summaries = load_module_with_deps_bounded_shared(
        &mut env,
        "Some.Nonexistent.Module",
        &[],
        1500,
        &mut visited,
    )
    .expect("a module already in `visited` must be skipped without I/O");
    assert!(
        summaries.is_empty(),
        "skipped module must contribute no LoadSummary"
    );
}

#[test]
fn test_shared_loader_still_enforces_bounded_budget() {
    // The shared loader keeps the per-call bounded guard so any single target's
    // closure depth stays capped even when sharing an env across targets.
    let mut env = Environment::new();
    let mut visited = hashbrown::HashSet::new();
    let err =
        load_module_with_deps_bounded_shared(&mut env, "Lean.Elab.Tactic", &[], 0, &mut visited)
            .unwrap_err();
    match err {
        ImportError::UnsupportedModule { module, reason } => {
            assert_eq!(module, "Lean.Elab.Tactic");
            assert!(
                reason.contains("bounded loader limit"),
                "expected bounded-loader diagnostic, got {reason}"
            );
        }
        other => panic!("expected UnsupportedModule, got {other:?}"),
    }
}

#[test]
fn test_default_search_paths_prefers_lean_path() {
    let temp_home = TempDir::new().expect("tempdir");
    let first = temp_home.path().join("lean_path_first");
    let second = temp_home.path().join("lean_path_second");
    fs::create_dir_all(&first).unwrap();
    fs::create_dir_all(&second).unwrap();

    let lean_path = env::join_paths([&first, &second]).unwrap();
    let mut env_map = HashMap::new();
    env_map.insert("LEAN_PATH", lean_path);
    env_map.insert("HOME", temp_home.path().as_os_str().to_os_string());

    let paths = super::collect_default_search_paths(
        |key| env_map.get(key).cloned(),
        |path| fs::read_dir(path),
    );

    assert!(
        paths.starts_with(&[first.clone(), second.clone()]),
        "LEAN_PATH entries should be first: {paths:?}"
    );
}

#[test]
fn test_default_search_paths_prefers_mathlib_path() {
    let temp_home = TempDir::new().expect("tempdir");
    let mathlib_path = temp_home.path().join("mathlib_path");
    let lean_path_dir = temp_home.path().join("lean_path_dir");
    fs::create_dir_all(&mathlib_path).unwrap();
    fs::create_dir_all(&lean_path_dir).unwrap();

    let mut env_map = HashMap::new();
    env_map.insert("MATHLIB_PATH", mathlib_path.as_os_str().to_os_string());
    env_map.insert("LEAN_PATH", env::join_paths([&lean_path_dir]).unwrap());
    env_map.insert("HOME", temp_home.path().as_os_str().to_os_string());

    let paths = super::collect_default_search_paths(
        |key| env_map.get(key).cloned(),
        |path| fs::read_dir(path),
    );

    assert_eq!(
        paths,
        vec![mathlib_path, lean_path_dir],
        "expected MATHLIB_PATH to precede LEAN_PATH: {paths:?}"
    );
}

#[test]
fn test_default_search_paths_uses_userprofile_when_home_missing() {
    let temp_home = TempDir::new().expect("tempdir");
    let toolchain_lib = temp_home
        .path()
        .join(".elan/toolchains/leanprover--lean4---v4.3.0/lib/lean");
    fs::create_dir_all(&toolchain_lib).unwrap();

    let mut env_map = HashMap::new();
    env_map.insert("USERPROFILE", temp_home.path().as_os_str().to_os_string());

    let paths = super::collect_default_search_paths(
        |key| env_map.get(key).cloned(),
        |path| fs::read_dir(path),
    );

    assert!(
        !paths.is_empty(),
        "expected toolchain path from USERPROFILE to be discovered"
    );
    assert_eq!(paths[0], toolchain_lib);
}

#[test]
fn test_toolchain_versions_from_search_paths_preserves_priority_and_deduplicates() {
    let paths = vec![
        Path::new("/tmp/mathlib/build/lib").to_path_buf(),
        Path::new("./.elan/toolchains/leanprover--lean4---v4.28.0/lib/lean").to_path_buf(),
        Path::new("./.elan/toolchains/leanprover--lean4---nightly-2026-04-21/lib/lean")
            .to_path_buf(),
        Path::new("./.elan/toolchains/leanprover--lean4---v4.28.0/lib/lean").to_path_buf(),
    ];

    let versions = super::toolchain_versions_from_search_paths(&paths);

    assert_eq!(versions, vec!["v4.28.0", "nightly-2026-04-21"]);
}

#[test]
fn test_alias_resolvable_toolchain_versions_fail_closed_on_unversioned_lean_prefix() {
    let temp = TempDir::new().expect("tempdir");
    let unversioned = temp.path().join("overlay/lib/lean");
    let versioned = temp
        .path()
        .join(".elan/toolchains/leanprover--lean4---v4.28.0/lib/lean");
    write_empty_olean(&unversioned.join("Init/Prelude.olean"));
    write_empty_olean(&versioned.join("Init/Prelude.olean"));
    let paths = vec![unversioned.clone(), versioned];

    let versions = super::alias_resolvable_toolchain_versions(&paths);

    assert!(
        versions.is_none(),
        "expected ambiguous stdlib prefix to block alias resolution"
    );
    assert_eq!(
        super::active_stdlib_toolchain(&paths),
        Some(super::ActiveStdlibToolchain::UnversionedPath(unversioned))
    );
}

#[test]
fn test_alias_resolvable_toolchain_versions_ignore_nonstdlib_prefixes() {
    let temp = TempDir::new().expect("tempdir");
    let mathlib = temp.path().join("mathlib/build/lib");
    let versioned = temp
        .path()
        .join(".elan/toolchains/leanprover--lean4---v4.28.0/lib/lean");
    fs::create_dir_all(&mathlib).expect("create mathlib overlay");
    write_empty_olean(&versioned.join("Init/Core.olean"));
    let paths = vec![mathlib, versioned];

    let versions = super::alias_resolvable_toolchain_versions(&paths);

    assert_eq!(versions, Some(vec!["v4.28.0".to_string()]));
}

fn module_with_origin_test_axiom(name: &str) -> ParsedModule {
    use crate::level::ParsedLevel;
    use crate::module::{ConstantKind, ParsedConstant};

    ParsedModule {
        const_names: vec![name.to_string()],
        constants: vec![ParsedConstant {
            name: name.to_string(),
            kind: ConstantKind::Axiom,
            level_params: Vec::new(),
            type_: Some(ParsedExpr::Sort(ParsedLevel::Zero)),
            value: None,
            inductive_val: None,
            constructor_val: None,
            recursor_val: None,
            hints: None,
            definition_safety: None,
            quot_kind: None,
        }],
        extra_const_names: Vec::new(),
        imports: Vec::new(),
        entries: Vec::new(),
        clean_payload: None,
    }
}

#[test]
fn test_load_parsed_module_tags_inserted_olean_constant_origin() {
    let const_name = "OriginAudit.loaded";
    let module_name = "OriginAudit.Module";
    let module = module_with_origin_test_axiom(const_name);
    let mut env = Environment::new();

    let summary = load_parsed_module(&mut env, &module, Some(module_name.to_string()))
        .expect("origin test module should load");

    assert_eq!(summary.added_constants, 1);
    let name = Name::from_string(const_name);
    let origin = env
        .get_constant_origin(&name)
        .expect("inserted .olean constant should be origin-tagged");
    assert_eq!(origin.module_name(), Some(module_name));
    assert_eq!(origin.trust(), OriginTrust::OleanUnpinned);
    assert!(env.is_unpinned_olean_import(&name));
}

#[test]
fn test_reject_unpinned_policy_blocks_parsed_module_before_registration() {
    let const_name = "OriginAudit.rejected";
    let module_name = "OriginAudit.Strict";
    let module = module_with_origin_test_axiom(const_name);
    let mut env = Environment::new();

    let err = load_parsed_module_with_import_policy(
        &mut env,
        &module,
        Some(module_name.to_string()),
        OleanImportPolicy::reject_unpinned_external(),
    )
    .expect_err("strict import policy should reject unpinned .olean constants");

    match err {
        ImportError::UnpinnedExternalOleanRejected {
            module,
            olean_constants,
            clean_payload_constants,
        } => {
            assert_eq!(module, module_name);
            assert_eq!(olean_constants, 1);
            assert_eq!(clean_payload_constants, 0);
        }
        other => panic!("expected UnpinnedExternalOleanRejected, got {other:?}"),
    }
    assert!(
        env.get_const(&Name::from_string(const_name)).is_none(),
        "rejected module must not register constants"
    );
}

#[test]
fn test_default_policy_allows_unpinned_legacy_parsed_module() {
    let const_name = "OriginAudit.legacyAllowed";
    let module_name = "OriginAudit.Legacy";
    let module = module_with_origin_test_axiom(const_name);
    let mut env = Environment::new();

    assert_eq!(
        OleanImportPolicy::default().unpinned_external(),
        UnpinnedOleanImportPolicy::Allow
    );
    let summary = load_parsed_module(&mut env, &module, Some(module_name.to_string()))
        .expect("default policy should preserve legacy allow-unpinned behavior");

    assert_eq!(summary.added_constants, 1);
    let name = Name::from_string(const_name);
    assert!(env.get_const(&name).is_some());
    assert_eq!(
        env.constant_origin_trust(&name),
        Some(OriginTrust::OleanUnpinned)
    );
}

#[test]
fn test_extension_entries_skip_duplicate_module_load() {
    let mut env = Environment::new();
    let module = module_with_extension("Ext.Test", "entry");

    load_parsed_module(&mut env, &module, None).expect("first load");
    load_parsed_module(&mut env, &module, None).expect("second load");

    // Module with 0 imports gets module_idx=0
    let entries = env
        .get_persistent_extension_module_entries(&Name::interned("Ext.Test"), 0)
        .expect("extension entries");
    assert_eq!(entries.len(), 1);
}

#[test]
fn module_cache_returns_entry_when_mtime_matches() {
    let cache = ModuleCache::new();
    let file = NamedTempFile::new().expect("temp file");
    fs::write(file.path(), b"original").unwrap();

    cache.insert("Init.Core", file.path(), dummy_module());

    let cached = cache.get("Init.Core", file.path());
    assert!(cached.is_some(), "expected cache hit for unchanged file");
    assert_eq!(cache.len(), 1, "entry should remain cached");
}

#[test]
fn module_cache_evicts_when_timestamp_changes() {
    use std::fs::FileTimes;
    use std::time::SystemTime;

    let cache = ModuleCache::new();
    let file = NamedTempFile::new().expect("temp file");
    fs::write(file.path(), b"v1").unwrap();

    cache.insert("Init.Changed", file.path(), dummy_module());

    // Explicitly set mtime 2 seconds in the future instead of sleeping.
    // This is deterministic regardless of filesystem mtime granularity
    // (HFS+ has 1-second resolution, NFS can be worse). Part of #1653.
    let future = SystemTime::now() + Duration::from_secs(2);
    let times = FileTimes::new().set_modified(future);
    fs::File::options()
        .write(true)
        .open(file.path())
        .unwrap()
        .set_times(times)
        .unwrap();

    assert!(
        cache.get("Init.Changed", file.path()).is_none(),
        "stale cache entry should be dropped when mtime changes"
    );
    assert_eq!(cache.len(), 0, "stale entry should be removed");
}

#[test]
fn module_cache_evicts_when_file_is_missing() {
    let cache = ModuleCache::new();
    let file = NamedTempFile::new().expect("temp file");
    let path = file.path().to_path_buf();
    fs::write(&path, b"v1").unwrap();

    cache.insert("Init.Missing", &path, dummy_module());
    fs::remove_file(&path).unwrap();

    assert!(
        cache.get("Init.Missing", &path).is_none(),
        "cache should not return entries for missing files"
    );
    assert!(cache.is_empty(), "missing file should clear cache entry");
}

fn sample_definition_decl(is_reducible: bool) -> Declaration {
    Declaration::Definition {
        name: Name::from_string("Test.sample"),
        level_params: vec![],
        type_: Expr::type_(),
        value: Expr::prop(),
        is_reducible,
    }
}

#[test]
fn test_decl_to_constant_info_uses_regular_hint_height() {
    let info = decl_to_constant_info(
        sample_definition_decl(false),
        Some(ReducibilityHintsData::Regular(23)),
    );

    assert_eq!(info.reducibility, Reducibility::Regular(23));
    assert!(
        !info.is_reducible,
        "Regular hints should not mark definition as abbreviation"
    );
}

#[test]
fn test_decl_to_constant_info_uses_abbrev_hint() {
    let info = decl_to_constant_info(
        sample_definition_decl(false),
        Some(ReducibilityHintsData::Abbrev),
    );

    assert_eq!(info.reducibility, Reducibility::Reducible);
    assert!(
        info.is_reducible,
        "Abbrev hints should mark definition as reducible"
    );
}

#[test]
fn test_decl_to_constant_info_falls_back_when_hint_missing() {
    let reducible = decl_to_constant_info(sample_definition_decl(true), None);
    assert_eq!(reducible.reducibility, Reducibility::Reducible);
    assert!(reducible.is_reducible);

    let semireducible = decl_to_constant_info(sample_definition_decl(false), None);
    assert_eq!(semireducible.reducibility, Reducibility::Regular(0));
    assert!(!semireducible.is_reducible);
}

#[test]
fn test_decl_to_constant_info_uses_opaque_hint() {
    let info = decl_to_constant_info(
        sample_definition_decl(true),
        Some(ReducibilityHintsData::Opaque),
    );

    assert_eq!(info.reducibility, Reducibility::Opaque);
    assert!(
        !info.is_reducible,
        "Opaque hints should force non-reducible behavior"
    );
}

/// Build a named definition decl (for the parameter-annotation-abbrev tests).
fn named_definition_decl(name: &str) -> Declaration {
    Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![Name::from_string("u")],
        type_: Expr::type_(),
        value: Expr::prop(),
        is_reducible: false,
    }
}

#[test]
fn test_decl_to_constant_info_forces_param_abbrevs_reducible() {
    // Lean's `optParam`/`autoParam`/`outParam`/`semiOutParam` are
    // `@[reducible] def … := α` identities (`Init/Prelude.lean`). Even when the
    // `.olean` hint surfaces as plain `Regular`, the import must restore the
    // source-true `Reducible` status so a field/binder typed `autoParam X tac`
    // delta-reduces to its bare `X` during `is_def_eq`.
    for abbrev in ["optParam", "autoParam", "outParam", "semiOutParam"] {
        let info = decl_to_constant_info(
            named_definition_decl(abbrev),
            Some(ReducibilityHintsData::Regular(0)),
        );
        assert_eq!(
            info.reducibility,
            Reducibility::Reducible,
            "{abbrev} must be forced Reducible (Lean reducible-identity abbrev)"
        );
        assert!(
            info.is_reducible,
            "{abbrev} is_reducible flag must agree with Reducible reducibility"
        );
    }
}

#[test]
fn test_decl_to_constant_info_param_abbrev_override_is_name_scoped() {
    // A same-shaped but differently-named definition is NOT special-cased: it
    // keeps its olean-declared Regular reducibility. The override is exactly the
    // four Lean parameter-annotation abbrevs, nothing wider.
    let info = decl_to_constant_info(
        named_definition_decl("Some.OtherDef"),
        Some(ReducibilityHintsData::Regular(7)),
    );
    assert_eq!(info.reducibility, Reducibility::Regular(7));
    assert!(!info.is_reducible);
}

#[test]
fn test_convert_expr_bvar_at_max_bvar_range_returns_error() {
    // BVar index = MAX_BVAR_INDEX + 1 (= MAX_BVAR_RANGE = 1,048,575) must fail.
    // ExprMeta::pack computes loose_bvar_range = idx + 1, which would exceed
    // the 20-bit field. Previously this panicked; now it returns an error.
    let too_large = ParsedExpr::BVar(u64::from(Expr::MAX_BVAR_INDEX) + 1);
    let mut cache = ExprInternCache::default();
    let result = convert_expr("test", &too_large, &mut cache).map(|(e, _)| e);
    assert!(
        result.is_err(),
        "BVar index at MAX_BVAR_RANGE should be rejected"
    );

    // Also test a much larger index that previously passed the old u32::MAX check
    let huge = ParsedExpr::BVar(2_000_000);
    let result = convert_expr("test", &huge, &mut cache).map(|(e, _)| e);
    assert!(result.is_err(), "BVar index 2M should be rejected");
}

#[test]
fn test_convert_expr_bvar_at_max_valid_index_succeeds() {
    // BVar at exactly MAX_BVAR_INDEX should succeed
    let at_max = ParsedExpr::BVar(u64::from(Expr::MAX_BVAR_INDEX));
    let mut cache = ExprInternCache::default();
    let result = convert_expr("test", &at_max, &mut cache).map(|(e, _)| e);
    assert!(result.is_ok(), "BVar at MAX_BVAR_INDEX should succeed");
}

#[test]
fn test_convert_expr_bvar_zero_succeeds() {
    let zero = ParsedExpr::BVar(0);
    let mut cache = ExprInternCache::default();
    let result = convert_expr("test", &zero, &mut cache).map(|(e, _)| e);
    assert!(result.is_ok(), "BVar(0) should succeed");
}

/// Hash-consing: identical sub-expressions within a single convert_expr call
/// share the same Arc<Expr> heap allocation (#2383).
#[test]
fn test_convert_expr_shares_identical_subexprs() {
    use crate::expr::ParsedBinderInfo;
    use clean_kernel::expr::ExprKind;
    use std::sync::Arc;

    // Build: ForallE("a", Nat, ForallE("b", Nat, Bool))
    // Both ForallE binder types reference structurally identical Nat constants.
    let nat = || ParsedExpr::Const("Nat".to_string(), vec![]);
    let bool_const = ParsedExpr::Const("Bool".to_string(), vec![]);
    let inner_pi = ParsedExpr::ForallE(
        "b".to_string(),
        Box::new(nat()),
        Box::new(bool_const),
        ParsedBinderInfo::Default,
    );
    let outer_pi = ParsedExpr::ForallE(
        "a".to_string(),
        Box::new(nat()),
        Box::new(inner_pi),
        ParsedBinderInfo::Default,
    );

    let mut cache = ExprInternCache::default();
    let (result, stats) = convert_expr("test", &outer_pi, &mut cache).expect("should convert");

    // Verify sharing stats: at least 1 cache hit for the duplicate Nat
    assert!(
        stats.cache_hits >= 1,
        "expected at least 1 cache hit for duplicate Nat, got {}",
        stats.cache_hits
    );

    // The result is Pi(Default, Nat, Pi(Default, Nat, Bool)).
    // Extract both Nat children and verify they share the same Arc.
    if let ExprKind::Pi(_, outer_ty, outer_body) = result.kind() {
        if let ExprKind::Pi(_, inner_ty, _) = outer_body.kind() {
            assert!(
                Arc::ptr_eq(outer_ty, inner_ty),
                "identical Nat sub-expressions should share the same Arc allocation"
            );
            return;
        }
    }
    panic!("unexpected expression structure");
}

/// Cross-constant sharing: when two convert_expr calls use the same shared
/// intern cache, identical sub-expressions across constants share the same
/// Arc<Expr> allocation (#2383).
#[test]
fn test_convert_expr_cross_constant_sharing() {
    use crate::expr::ParsedBinderInfo;
    use std::sync::Arc;

    let nat = || ParsedExpr::Const("Nat".to_string(), vec![]);

    // Two separate expressions that both contain `Nat` as a sub-expression,
    // simulating two different constants in the same module.
    let expr_a = ParsedExpr::ForallE(
        "x".to_string(),
        Box::new(nat()),
        Box::new(ParsedExpr::BVar(0)),
        ParsedBinderInfo::Default,
    );
    let expr_b = ParsedExpr::ForallE(
        "y".to_string(),
        Box::new(nat()),
        Box::new(ParsedExpr::BVar(0)),
        ParsedBinderInfo::Default,
    );

    // Shared cache across both conversions (simulates module-level cache)
    let mut cache = ExprInternCache::default();
    let (result_a, _stats_a) =
        convert_expr("const_a", &expr_a, &mut cache).expect("should convert");
    let (result_b, stats_b) = convert_expr("const_b", &expr_b, &mut cache).expect("should convert");

    // The second call should see cache hits for `Nat` and `BVar(0)` from the first call
    assert!(
        stats_b.cache_hits >= 2,
        "expected cross-constant cache hits for Nat and BVar(0), got {}",
        stats_b.cache_hits
    );

    // Verify pointer-level sharing: both Pi types reference the same Arc<Nat>
    if let (
        clean_kernel::expr::ExprKind::Pi(_, ty_a, _),
        clean_kernel::expr::ExprKind::Pi(_, ty_b, _),
    ) = (result_a.kind(), result_b.kind())
    {
        assert!(
            Arc::ptr_eq(ty_a, ty_b),
            "Nat in const_a and const_b should share the same Arc allocation"
        );
        return;
    }
    panic!("unexpected expression structure");
}

/// Build a Nonempty-like inductive module for testing is_large_elim (#2242).
fn nonempty_like_module() -> ParsedModule {
    use crate::expr::ParsedBinderInfo;
    use crate::level::ParsedLevel;
    use crate::module::{ConstantKind, ConstructorValData, InductiveValData, ParsedConstant};

    // Nonempty : Sort u → Prop
    let ind_type = ParsedExpr::ForallE(
        "α".to_string(),
        Box::new(ParsedExpr::Sort(ParsedLevel::Param("u".to_string()))),
        Box::new(ParsedExpr::Sort(ParsedLevel::Zero)),
        ParsedBinderInfo::Implicit,
    );
    // Nonempty.intro : {α : Sort u} → α → Nonempty α
    let ctor_type = ParsedExpr::ForallE(
        "α".to_string(),
        Box::new(ParsedExpr::Sort(ParsedLevel::Param("u".to_string()))),
        Box::new(ParsedExpr::ForallE(
            "val".to_string(),
            Box::new(ParsedExpr::BVar(0)),
            Box::new(ParsedExpr::App(
                Box::new(ParsedExpr::Const(
                    "Nonempty".to_string(),
                    vec![ParsedLevel::Param("u".to_string())],
                )),
                Box::new(ParsedExpr::BVar(1)),
            )),
            ParsedBinderInfo::Default,
        )),
        ParsedBinderInfo::Implicit,
    );

    ParsedModule {
        const_names: vec!["Nonempty".to_string(), "Nonempty.intro".to_string()],
        constants: vec![
            ParsedConstant {
                name: "Nonempty".to_string(),
                kind: ConstantKind::Inductive,
                level_params: vec!["u".to_string()],
                type_: Some(ind_type),
                value: None,
                inductive_val: Some(InductiveValData {
                    num_params: 1,
                    num_indices: 0,
                    all: vec!["Nonempty".to_string()],
                    ctors: vec!["Nonempty.intro".to_string()],
                    is_rec: false,
                    is_unsafe: false,
                    is_reflexive: false,
                    is_nested: false,
                }),
                constructor_val: None,
                recursor_val: None,
                hints: None,
                definition_safety: None,
                quot_kind: None,
            },
            ParsedConstant {
                name: "Nonempty.intro".to_string(),
                kind: ConstantKind::Constructor,
                level_params: vec!["u".to_string()],
                type_: Some(ctor_type),
                value: None,
                inductive_val: None,
                constructor_val: Some(ConstructorValData {
                    induct: "Nonempty".to_string(),
                    cidx: 0,
                    num_params: 1,
                    num_fields: 1,
                    is_unsafe: false,
                }),
                recursor_val: None,
                hints: None,
                definition_safety: None,
                quot_kind: None,
            },
        ],
        extra_const_names: Vec::new(),
        imports: Vec::new(),
        entries: Vec::new(),
        clean_payload: None,
    }
}

/// Nonempty-like Prop inductive with a non-Prop field must have is_large_elim=false.
/// This is the bug described in #2242: the old inline logic only checked
/// constructor count, missing the full singleton condition.
#[test]
fn test_nonempty_like_inductive_has_large_elim_false() {
    let module = nonempty_like_module();
    let mut env = Environment::new();
    let summary = load_parsed_module(&mut env, &module, None)
        .expect("loading Nonempty-like module should succeed");
    assert_eq!(summary.added_constants, 2);

    let ind = env
        .get_inductive(&Name::interned("Nonempty"))
        .expect("Nonempty should be registered");
    assert!(
        !ind.is_large_elim,
        "Nonempty (Prop inductive with non-Prop field) must not allow large elimination"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// Direct binary-to-kernel conversion tests (#2428)
// ════════════════════════════════════════════════════════════════════════════

use crate::region::CompactedRegion;

fn get_lean_lib_path() -> Option<std::path::PathBuf> {
    crate::import::default_search_paths()
        .into_iter()
        .find(|p| p.join("Init/Prelude.olean").exists())
}

/// Gate `.olean` integration tests on the matching Lean toolchain being
/// available AND a deliberate opt-in via env var. These tests load real
/// .olean files (Init/Prelude.olean) and compare structural properties
/// constant-by-constant; on a machine with a non-matching Lean toolchain
/// the comparisons surface BinderInfo / type-encoding differences that
/// reflect Lean version drift rather than real bugs in the import
/// pipeline. Opt in with `CLEAN_OLEAN_PRELUDE_INTEGRATION=1`.
fn require_olean_prelude_integration() -> Option<std::path::PathBuf> {
    if std::env::var_os("CLEAN_OLEAN_PRELUDE_INTEGRATION").is_none() {
        eprintln!(
            "TRACE: olean Prelude integration test skipped — set \
             CLEAN_OLEAN_PRELUDE_INTEGRATION=1 to run against the matching \
             Lean toolchain"
        );
        return None;
    }
    get_lean_lib_path()
}

/// Load Prelude and return (region_bytes, base_addr) or None if unavailable.
fn load_prelude_region() -> Option<(Vec<u8>, u64)> {
    let lib_path = get_lean_lib_path()?;
    let prelude_path = lib_path.join("Init/Prelude.olean");
    if !prelude_path.exists() {
        return None;
    }
    let bytes = fs::read(&prelude_path).expect("Failed to read Init/Prelude.olean");
    let header = crate::parse_header(&bytes).expect("Failed to parse header");
    Some((bytes, header.base_addr))
}

/// Compare direct vs two-phase conversion for a single expression offset.
fn compare_expr_at(region: &CompactedRegion, offset: usize) -> (bool, bool, bool) {
    let ptr = region.offset_to_ptr(offset);
    let two_phase = region.read_expr_at(offset).ok().and_then(|pe| {
        let mut c = ExprInternCache::default();
        convert_expr("test", &pe, &mut c).ok().map(|(e, _)| e)
    });
    let mut c = ExprInternCache::default();
    let direct = read_and_convert_expr(region, ptr, "test", &mut c)
        .ok()
        .map(|(e, _)| e);
    match (two_phase, direct) {
        (Some(tp), Some(dr)) => (tp == dr, false, false),
        (None, None) => (true, false, false),
        (None, Some(_)) => (false, true, false),
        (Some(_), None) => (false, false, true),
    }
}

/// Verify direct converter matches two-phase for real .olean expressions (#2428).
#[test]
fn test_direct_converter_matches_two_phase() {
    let Some((bytes, base_addr)) = load_prelude_region() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };
    let region = CompactedRegion::new(&bytes, base_addr);
    let expr_objects = region.find_expr_objects();
    assert!(!expr_objects.is_empty(), "Expected expression objects");

    let (mut matched, mut mismatches) = (0usize, 0usize);
    for (offset, _tag, _) in expr_objects.iter().take(200) {
        let (ok, _, _) = compare_expr_at(&region, *offset);
        if ok {
            matched += 1;
        } else {
            mismatches += 1;
        }
    }

    println!("Direct converter: {matched} matched, {mismatches} mismatches");
    assert!(matched > 50, "Expected at least 50 matches, got {matched}");
    assert_eq!(
        mismatches, 0,
        "Direct converter produced {mismatches} different results"
    );
}

/// Verify that the direct converter produces consistent sharing statistics.
#[test]
fn test_direct_converter_sharing_stats() {
    let Some((bytes, base_addr)) = load_prelude_region() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };
    let region = CompactedRegion::new(&bytes, base_addr);
    let expr_objects = region.find_expr_objects();

    let mut shared_cache = ExprInternCache::default();
    let (mut total_intern, mut total_hits, mut converted) = (0u64, 0u64, 0usize);
    for (offset, _tag, _) in expr_objects.iter().take(100) {
        let ptr = region.offset_to_ptr(*offset);
        if let Ok((_, stats)) = read_and_convert_expr(&region, ptr, "test", &mut shared_cache) {
            total_intern += stats.total_intern_calls;
            total_hits += stats.cache_hits;
            converted += 1;
        }
    }

    let hit_pct = if total_intern > 0 {
        total_hits as f64 / total_intern as f64 * 100.0
    } else {
        0.0
    };
    println!("Direct stats: {converted} exprs, {total_intern} interns, {total_hits} hits ({hit_pct:.1}%)");
    assert!(
        converted > 0,
        "Expected at least some successful conversions"
    );
    assert!(total_hits > 0, "Expected cache hits with shared cache");
}

// ════════════════════════════════════════════════════════════════════════════
// Direct load path tests: LoadModule vs ParsedModule (#2428 Phase 2)
// ════════════════════════════════════════════════════════════════════════════

use crate::import::parse::parse_module;

/// Load an .olean file through both paths and return (env_parsed, env_direct, summaries).
fn load_both_paths(
    path: &Path,
    module_name: &str,
) -> (
    Environment,
    super::LoadSummary,
    Environment,
    super::LoadSummary,
) {
    let bytes = fs::read(path).expect("read .olean");
    let parsed_module = parse_module(&bytes).expect("parse_module failed");
    let mut env_parsed = Environment::new();
    let summary_parsed =
        load_parsed_module(&mut env_parsed, &parsed_module, Some(module_name.into()))
            .expect("ParsedModule load failed");

    let bytes2 = fs::read(path).expect("read .olean again");
    let load_module = parse_load_module(bytes2).expect("parse_load_module failed");
    let mut env_direct = Environment::new();
    let mut intern_cache = ExprInternCache::default();
    let summary_direct = load_module_direct_with_cache(
        &mut env_direct,
        &load_module,
        Some(module_name.into()),
        &mut intern_cache,
    )
    .expect("LoadModule direct load failed");

    (env_parsed, summary_parsed, env_direct, summary_direct)
}

/// Compare environments constant-by-constant, returning the number of checked entries.
fn compare_envs_for_names(
    names: &[String],
    env_parsed: &Environment,
    env_direct: &Environment,
) -> usize {
    let mut checked = 0usize;
    for name in names {
        if name.is_empty() {
            continue;
        }
        let kname = Name::interned(name);
        checked += compare_const(&kname, name, env_parsed, env_direct);
        checked += compare_inductive(&kname, name, env_parsed, env_direct);
        checked += compare_constructor(&kname, name, env_parsed, env_direct);
        checked += compare_recursor(&kname, name, env_parsed, env_direct);
    }
    checked
}

fn compare_const(kname: &Name, name: &str, a: &Environment, b: &Environment) -> usize {
    if let Some(ca) = a.get_const(kname) {
        let cb = b
            .get_const(kname)
            .unwrap_or_else(|| panic!("constant {name} missing from direct env"));
        assert_eq!(ca.type_, cb.type_, "type mismatch for constant {name}");
        1
    } else {
        0
    }
}

fn compare_inductive(kname: &Name, name: &str, a: &Environment, b: &Environment) -> usize {
    if let Some(ia) = a.get_inductive(kname) {
        let ib = b
            .get_inductive(kname)
            .unwrap_or_else(|| panic!("inductive {name} missing from direct env"));
        assert_eq!(ia.type_, ib.type_, "type mismatch for inductive {name}");
        assert_eq!(
            ia.num_params, ib.num_params,
            "num_params mismatch for inductive {name}"
        );
        assert_eq!(
            ia.constructor_names, ib.constructor_names,
            "constructor_names mismatch for {name}"
        );
        1
    } else {
        0
    }
}

fn compare_constructor(kname: &Name, name: &str, a: &Environment, b: &Environment) -> usize {
    if let Some(ca) = a.get_constructor(kname) {
        let cb = b
            .get_constructor(kname)
            .unwrap_or_else(|| panic!("constructor {name} missing from direct env"));
        assert_eq!(ca.type_, cb.type_, "type mismatch for constructor {name}");
        assert_eq!(
            ca.num_fields, cb.num_fields,
            "num_fields mismatch for constructor {name}"
        );
        1
    } else {
        0
    }
}

fn compare_recursor(kname: &Name, name: &str, a: &Environment, b: &Environment) -> usize {
    if let Some(ra) = a.get_recursor(kname) {
        let rb = b
            .get_recursor(kname)
            .unwrap_or_else(|| panic!("recursor {name} missing from direct env"));
        assert_eq!(ra.type_, rb.type_, "type mismatch for recursor {name}");
        assert_eq!(
            ra.arg_order, rb.arg_order,
            "arg_order mismatch for recursor {name}: the two import paths must \
             infer the same RecursorArgOrder"
        );
        assert_eq!(
            ra.num_params, rb.num_params,
            "num_params mismatch for recursor {name}"
        );
        assert_eq!(
            ra.rules.len(),
            rb.rules.len(),
            "rules count mismatch for recursor {name}"
        );
        for (i, (rpa, rpb)) in ra.rules.iter().zip(rb.rules.iter()).enumerate() {
            assert_eq!(
                rpa.rhs, rpb.rhs,
                "rule[{i}] RHS mismatch for recursor {name}"
            );
        }
        1
    } else {
        0
    }
}

/// Load Init/Prelude.olean through both paths and compare constant-by-constant.
#[test]
fn test_direct_load_path_matches_parsed_module_path() {
    let Some(lib_path) = require_olean_prelude_integration() else {
        return;
    };
    let prelude_path = lib_path.join("Init/Prelude.olean");
    let bytes = fs::read(&prelude_path).expect("read Prelude.olean");
    let parsed_module = parse_module(&bytes).expect("parse_module failed");
    let (env_parsed, sp, env_direct, sd) = load_both_paths(&prelude_path, "Init.Prelude");

    assert_eq!(
        sp.added_constants, sd.added_constants,
        "added_constants mismatch"
    );
    assert_eq!(
        sp.duplicate_constants, sd.duplicate_constants,
        "duplicate_constants mismatch"
    );
    assert!(
        sp.added_constants > 100,
        "expected >100 constants from Prelude, got {}",
        sp.added_constants
    );

    let names: Vec<String> = parsed_module
        .constants
        .iter()
        .map(|c| c.name.clone())
        .collect();
    let checked = compare_envs_for_names(&names, &env_parsed, &env_direct);
    println!(
        "Direct load path verified: {checked} constants, {} added (both paths)",
        sp.added_constants
    );
    assert!(
        checked > 100,
        "expected >100 constants checked, only {checked}"
    );
}

/// Verify that parse_load_module produces the correct number of imports and constants.
#[test]
fn test_parse_load_module_basic_fields() {
    let Some(lib_path) = get_lean_lib_path() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };
    let prelude_path = lib_path.join("Init/Prelude.olean");
    let bytes = fs::read(&prelude_path).expect("read Prelude.olean");

    // Parse through both paths
    let parsed_module = parse_module(&bytes).expect("parse_module");
    let bytes2 = fs::read(&prelude_path).expect("read Prelude.olean again");
    let load_module = parse_load_module(bytes2).expect("parse_load_module");

    // Import counts must match
    assert_eq!(
        parsed_module.imports.len(),
        load_module.imports.len(),
        "import count mismatch"
    );
    for (i, (pm, lm)) in parsed_module
        .imports
        .iter()
        .zip(load_module.imports.iter())
        .enumerate()
    {
        assert_eq!(
            pm.module_name, lm.module_name,
            "import[{i}] module_name mismatch"
        );
    }

    // Constant counts must match
    assert_eq!(
        parsed_module.constants.len(),
        load_module.constants.len(),
        "constant count mismatch: parsed={}, load={}",
        parsed_module.constants.len(),
        load_module.constants.len()
    );

    // Constant names must match
    for (i, (pc, lc)) in parsed_module
        .constants
        .iter()
        .zip(load_module.constants.iter())
        .enumerate()
    {
        assert_eq!(
            pc.name, lc.name,
            "constant[{i}] name mismatch: parsed={}, load={}",
            pc.name, lc.name
        );
    }
}

/// Verify the direct load path works correctly with Init.Core (which has
/// imports, more complex inductives/recursors than Prelude).
#[test]
fn test_direct_load_path_with_init_core() {
    let Some(lib_path) = get_lean_lib_path() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };
    let core_path = lib_path.join("Init/Core.olean");
    if !core_path.exists() {
        eprintln!("Skipping test: Init/Core.olean not found");
        return;
    }
    let bytes = fs::read(&core_path).expect("read Core.olean");

    // Parse through both paths
    let parsed_module = parse_module(&bytes).expect("parse_module");
    let mut env_parsed = Environment::new();
    let summary_parsed =
        load_parsed_module(&mut env_parsed, &parsed_module, Some("Init.Core".into()))
            .expect("ParsedModule load failed");

    let bytes2 = fs::read(&core_path).expect("read Core.olean again");
    let load_module = parse_load_module(bytes2).expect("parse_load_module");
    let mut env_direct = Environment::new();
    let mut intern_cache = ExprInternCache::default();
    let summary_direct = load_module_direct_with_cache(
        &mut env_direct,
        &load_module,
        Some("Init.Core".into()),
        &mut intern_cache,
    )
    .expect("LoadModule direct load failed");

    assert_eq!(
        summary_parsed.added_constants, summary_direct.added_constants,
        "Init.Core added_constants mismatch: parsed={}, direct={}",
        summary_parsed.added_constants, summary_direct.added_constants
    );

    // Skipped constants should match (both may skip the same unsupported constants)
    assert_eq!(
        summary_parsed.skipped_constants.len(),
        summary_direct.skipped_constants.len(),
        "Init.Core skipped_constants mismatch: parsed={}, direct={}",
        summary_parsed.skipped_constants.len(),
        summary_direct.skipped_constants.len()
    );

    println!(
        "Init.Core: {} added, {} skipped, {} duplicates (both paths)",
        summary_direct.added_constants,
        summary_direct.skipped_constants.len(),
        summary_direct.duplicate_constants
    );
}

/// Verify that the direct load path populates expression sharing statistics.
#[test]
fn test_direct_load_path_sharing_stats() {
    let Some(lib_path) = get_lean_lib_path() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };
    let prelude_path = lib_path.join("Init/Prelude.olean");
    let bytes = fs::read(&prelude_path).expect("read Prelude.olean");
    let load_module = parse_load_module(bytes).expect("parse_load_module");
    let mut env = Environment::new();
    let mut intern_cache = ExprInternCache::default();
    let summary = load_module_direct_with_cache(
        &mut env,
        &load_module,
        Some("Init.Prelude".into()),
        &mut intern_cache,
    )
    .expect("direct load failed");

    // Should have recorded meaningful sharing statistics
    assert!(
        summary.expr_sharing.total_intern_calls > 0,
        "expected positive intern calls, got 0"
    );
    assert!(
        summary.expr_sharing.cache_hits > 0,
        "expected positive cache hits, got 0"
    );
    assert!(
        summary.expr_sharing.unique_exprs > 0,
        "expected positive unique expressions, got 0"
    );
    let hit_rate = summary.expr_sharing.hit_rate();
    assert!(
        hit_rate > 0.0,
        "expected positive hit rate, got {hit_rate:.4}"
    );
    println!(
        "Direct load sharing: {} intern calls, {} hits ({:.1}% rate), {} unique exprs",
        summary.expr_sharing.total_intern_calls,
        summary.expr_sharing.cache_hits,
        hit_rate * 100.0,
        summary.expr_sharing.unique_exprs
    );
}

#[test]
fn test_load_parsed_module_registers_imported_instance_into_kernel_registry() {
    let mut env = Environment::new();
    let hadd = Name::from_string("HAdd");

    // Before import, the kernel registry has no instances for the class.
    assert!(
        env.get_class_instances(&hadd).is_empty(),
        "fresh environment should have no HAdd instances"
    );

    let module = module_with_instances(&[("instHAddNat", "HAdd", 100)]);
    load_parsed_module(&mut env, &module, Some("Test.Instances".to_string()))
        .expect("load with instance extension");

    // After import, get_class_instances() (read by the elaborator's
    // init_instances_from_env) must see the imported instance.
    let instances = env.get_class_instances(&hadd);
    assert_eq!(instances.len(), 1, "imported instance should be registered");
    assert_eq!(instances[0].name, Name::from_string("instHAddNat"));
    assert_eq!(instances[0].class_name, hadd);
    assert_eq!(instances[0].priority, 100);
    assert!(
        env.is_instance(&Name::from_string("instHAddNat")),
        "imported instance should be recognized by is_instance()"
    );
}

#[test]
fn test_load_parsed_module_preserves_instance_priority_ordering() {
    let mut env = Environment::new();
    let hadd = Name::from_string("HAdd");

    // Two instances for the same class with distinct priorities, supplied in
    // low-then-high order; the registry must order them highest-first.
    let module =
        module_with_instances(&[("instHAddNat", "HAdd", 100), ("instHAddInt", "HAdd", 200)]);
    load_parsed_module(
        &mut env,
        &module,
        Some("Test.PriorityInstances".to_string()),
    )
    .expect("load with two instances");

    let instances = env.get_class_instances(&hadd);
    assert_eq!(instances.len(), 2, "both instances should be registered");
    assert_eq!(
        instances[0].name,
        Name::from_string("instHAddInt"),
        "higher-priority instance should come first"
    );
    assert_eq!(instances[0].priority, 200);
    assert_eq!(instances[1].name, Name::from_string("instHAddNat"));
    assert_eq!(instances[1].priority, 100);
}

#[test]
fn test_load_parsed_module_no_instance_extension_leaves_registry_empty() {
    let mut env = Environment::new();

    // A module carrying only a non-instance extension must not register any
    // instances into the kernel registry.
    let module = module_with_extension("reducibility", "someEntry");
    load_parsed_module(&mut env, &module, Some("Test.NoInstances".to_string()))
        .expect("load without instance extension");

    assert_eq!(
        env.num_instances(),
        0,
        "no instances should be registered when the instance extension is absent"
    );
    assert!(
        env.get_class_instances(&Name::from_string("HAdd"))
            .is_empty(),
        "get_class_instances must be empty without imported instances"
    );
}

#[test]
fn test_load_parsed_module_duplicate_instance_load_is_idempotent() {
    let mut env = Environment::new();
    let hadd = Name::from_string("HAdd");

    let module = module_with_instances(&[("instHAddNat", "HAdd", 100)]);
    load_parsed_module(&mut env, &module, Some("Test.Dup".to_string())).expect("first load");
    // Re-loading the same module (e.g. base + private .olean) must not create
    // a duplicate kernel registration.
    load_parsed_module(&mut env, &module, Some("Test.Dup".to_string())).expect("second load");

    let instances = env.get_class_instances(&hadd);
    assert_eq!(
        instances.len(),
        1,
        "duplicate loads must not register the same instance twice"
    );
}

#[test]
fn test_load_parsed_module_registers_imported_simp_lemma_into_kernel_registry() {
    use clean_kernel::env::SimpPriority;

    let mut env = Environment::new();
    let lemma = Name::from_string("Nat.add_zero");

    // Before import, the kernel simp registry has no lemmas.
    assert!(
        !env.is_simp_lemma(&lemma),
        "fresh environment should have no simp lemmas"
    );

    let module = module_with_simp_lemmas(&[("Nat.add_zero", SimpPriority::Default)]);
    load_parsed_module(&mut env, &module, Some("Test.Simp".to_string()))
        .expect("load with simp extension");

    // After import, the kernel registry (read by the simp tactic) must see the
    // imported lemma.
    assert!(
        env.is_simp_lemma(&lemma),
        "imported simp lemma should be registered"
    );
    let names: Vec<_> = env
        .get_simp_lemmas()
        .map(|info| info.name.clone())
        .collect();
    assert_eq!(
        names.len(),
        1,
        "exactly one simp lemma should be registered"
    );
    assert_eq!(names[0], lemma);
    let info = env
        .get_simp_lemma(&lemma)
        .expect("registered lemma should be retrievable");
    assert_eq!(info.priority, SimpPriority::Default);
}

#[test]
fn test_load_parsed_module_preserves_simp_lemma_custom_priority() {
    use clean_kernel::env::SimpPriority;

    let mut env = Environment::new();
    let lemma = Name::from_string("List.length_nil");

    let module = module_with_simp_lemmas(&[("List.length_nil", SimpPriority::Custom(500))]);
    load_parsed_module(&mut env, &module, Some("Test.SimpPriority".to_string()))
        .expect("load with custom-priority simp lemma");

    let info = env
        .get_simp_lemma(&lemma)
        .expect("imported lemma should be registered");
    assert_eq!(
        info.priority,
        SimpPriority::Custom(500),
        "imported simp lemma priority must be preserved faithfully"
    );
}

#[test]
fn test_load_parsed_module_no_simp_extension_leaves_registry_empty() {
    let mut env = Environment::new();

    // A module carrying only a non-simp extension must not register any simp
    // lemmas into the kernel registry.
    let module = module_with_extension("reducibility", "someEntry");
    load_parsed_module(&mut env, &module, Some("Test.NoSimp".to_string()))
        .expect("load without simp extension");

    assert_eq!(
        env.get_simp_lemmas().count(),
        0,
        "no simp lemmas should be registered when the simp extension is absent"
    );
}

#[test]
fn test_load_parsed_module_duplicate_simp_lemma_load_is_idempotent() {
    use clean_kernel::env::SimpPriority;

    let mut env = Environment::new();

    let module = module_with_simp_lemmas(&[("Nat.add_zero", SimpPriority::Default)]);
    load_parsed_module(&mut env, &module, Some("Test.SimpDup".to_string())).expect("first load");
    // Re-loading the same module (e.g. base + private .olean) must not create a
    // duplicate kernel registration.
    load_parsed_module(&mut env, &module, Some("Test.SimpDup".to_string())).expect("second load");

    assert_eq!(
        env.get_simp_lemmas().count(),
        1,
        "duplicate loads must not register the same simp lemma twice"
    );
}

#[test]
fn test_load_parsed_module_registers_imported_reducible_attr_into_kernel() {
    let mut env = Environment::new();
    let def_name = Name::from_string("Test.myAbbrev");

    // Add a semireducible definition (the default reducibility) so the bridge
    // has a real constant to act on.
    env.add_decl_structural(semireducible_def_decl("Test.myAbbrev"))
        .expect("add semireducible definition");
    assert_ne!(
        env.get_reducibility(&def_name),
        Some(Reducibility::Reducible),
        "freshly added (non-abbrev) definition must not start out Reducible"
    );

    // Import a module whose attrExtension marks the definition `@[reducible]`.
    let module = module_with_attributes(&[("Test.myAbbrev", "reducible", 0)]);
    load_parsed_module(&mut env, &module, Some("Test.ReducibleAttr".to_string()))
        .expect("load with reducible attribute");

    assert_eq!(
        env.get_reducibility(&def_name),
        Some(Reducibility::Reducible),
        "imported @[reducible] attribute must flip the constant to Reducible"
    );
}

#[test]
fn test_load_parsed_module_registers_imported_irreducible_attr_into_kernel() {
    let mut env = Environment::new();
    let def_name = Name::from_string("Test.opaqueDef");

    env.add_decl_structural(semireducible_def_decl("Test.opaqueDef"))
        .expect("add semireducible definition");

    let module = module_with_attributes(&[("Test.opaqueDef", "irreducible", 0)]);
    load_parsed_module(&mut env, &module, Some("Test.IrreducibleAttr".to_string()))
        .expect("load with irreducible attribute");

    assert_eq!(
        env.get_reducibility(&def_name),
        Some(Reducibility::Irreducible),
        "imported @[irreducible] attribute must mark the constant Irreducible"
    );
}

#[test]
fn test_load_parsed_module_no_attr_extension_leaves_reducibility_default() {
    let mut env = Environment::new();
    let def_name = Name::from_string("Test.untouched");

    env.add_decl_structural(semireducible_def_decl("Test.untouched"))
        .expect("add semireducible definition");
    let before = env.get_reducibility(&def_name);

    // A module carrying only a non-attribute extension must not alter any
    // constant's reducibility.
    let module =
        module_with_simp_lemmas(&[("Nat.add_zero", clean_kernel::env::SimpPriority::Default)]);
    load_parsed_module(&mut env, &module, Some("Test.NoAttr".to_string()))
        .expect("load without attribute extension");

    assert_eq!(
        env.get_reducibility(&def_name),
        before,
        "reducibility must stay at the default when no attrExtension is imported"
    );
    assert_ne!(
        before,
        Some(Reducibility::Reducible),
        "sanity: the default for this definition is not Reducible"
    );
}

#[test]
fn test_load_parsed_module_attr_for_absent_constant_is_noop() {
    let mut env = Environment::new();

    // The attribute targets a constant that does not exist in the environment.
    // `set_reducibility` returns false for it and we must not fabricate a
    // constant or otherwise mutate the environment's constant set.
    let module = module_with_attributes(&[("Test.ghost", "reducible", 0)]);
    load_parsed_module(&mut env, &module, Some("Test.GhostAttr".to_string()))
        .expect("load attribute for absent constant");

    assert!(
        env.get_reducibility(&Name::from_string("Test.ghost"))
            .is_none(),
        "no constant should be created for an attribute on an absent declaration"
    );
}

#[test]
fn test_load_parsed_module_duplicate_attr_load_is_idempotent() {
    let mut env = Environment::new();
    let def_name = Name::from_string("Test.dupAbbrev");

    env.add_decl_structural(semireducible_def_decl("Test.dupAbbrev"))
        .expect("add semireducible definition");

    let module = module_with_attributes(&[("Test.dupAbbrev", "reducible", 0)]);
    load_parsed_module(&mut env, &module, Some("Test.AttrDup".to_string())).expect("first load");
    // Re-loading the same module (e.g. base + private .olean) must leave the
    // reducibility at the same level — applying @[reducible] twice is a no-op
    // overwrite.
    load_parsed_module(&mut env, &module, Some("Test.AttrDup".to_string())).expect("second load");

    assert_eq!(
        env.get_reducibility(&def_name),
        Some(Reducibility::Reducible),
        "duplicate attribute loads must keep the constant Reducible"
    );
}

/// Register a synthetic inductive with a chosen `num_params` so the `@[class]`
/// bridge has a real inductive to read `num_params` from — mirroring how an
/// imported structure/inductive is present before its attribute is materialized.
fn register_synthetic_inductive(env: &mut Environment, name: &str, num_params: u32) {
    use clean_kernel::inductive::InductiveVal;

    env.register_inductive(InductiveVal {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::type_(),
        num_params,
        num_indices: 0,
        all_names: vec![Name::from_string(name)],
        constructor_names: vec![],
        is_recursive: false,
        is_reflexive: false,
        is_large_elim: true,
        is_nested: false,
    });
}

#[test]
fn test_load_parsed_module_registers_imported_class_attr_into_kernel() {
    let mut env = Environment::new();
    let class_name = Name::from_string("Test.MyClass");

    // The imported inductive (the class carrier) is present, with two parameters,
    // but starts out as an ordinary inductive — not a registered class.
    register_synthetic_inductive(&mut env, "Test.MyClass", 2);
    assert!(
        !env.is_class(&class_name),
        "an imported inductive must not be a class until the @[class] attr is bridged"
    );

    // Import a module whose attrExtension marks the inductive `@[class]`.
    let module = module_with_attributes(&[("Test.MyClass", "class", 0)]);
    load_parsed_module(&mut env, &module, Some("Test.ClassAttr".to_string()))
        .expect("load with class attribute");

    assert!(
        env.is_class(&class_name),
        "imported @[class] attribute must register the inductive as a typeclass"
    );
    let info = env
        .get_class_info(&class_name)
        .expect("registered class must be retrievable");
    assert_eq!(
        info.num_params, 2,
        "class num_params must be read faithfully from the imported inductive"
    );
    assert!(
        info.out_params.is_empty() && info.semi_out_params.is_empty(),
        "out/semi-out params are not persisted in the attr entry; must default to empty"
    );
}

#[test]
fn test_load_parsed_module_no_class_attr_leaves_inductive_not_class() {
    let mut env = Environment::new();
    let ind_name = Name::from_string("Test.PlainInductive");

    register_synthetic_inductive(&mut env, "Test.PlainInductive", 1);

    // A module carrying only a non-class attribute (`@[reducible]` on some other
    // decl) must not turn the inductive into a class.
    let module = module_with_attributes(&[("Test.PlainInductive", "reducible", 0)]);
    load_parsed_module(&mut env, &module, Some("Test.NoClass".to_string()))
        .expect("load without class attribute");

    assert!(
        !env.is_class(&ind_name),
        "an inductive without @[class] must remain an ordinary inductive"
    );
}

#[test]
fn test_load_parsed_module_class_attr_for_absent_inductive_is_noop() {
    let mut env = Environment::new();
    let ghost = Name::from_string("Test.GhostClass");

    // The `@[class]` attribute targets an inductive that does not exist in the
    // environment. We must not fabricate a class (no inductive => no num_params).
    let module = module_with_attributes(&[("Test.GhostClass", "class", 0)]);
    load_parsed_module(&mut env, &module, Some("Test.GhostClassAttr".to_string()))
        .expect("load class attribute for absent inductive");

    assert!(
        !env.is_class(&ghost),
        "no class should be registered for a @[class] attr on an absent inductive"
    );
}

#[test]
fn test_load_parsed_module_duplicate_class_load_is_idempotent() {
    let mut env = Environment::new();
    let class_name = Name::from_string("Test.DupClass");

    register_synthetic_inductive(&mut env, "Test.DupClass", 3);

    let module = module_with_attributes(&[("Test.DupClass", "class", 0)]);
    load_parsed_module(&mut env, &module, Some("Test.ClassDup".to_string())).expect("first load");
    // Re-loading the same module (e.g. base + private .olean) must keep the class
    // registered exactly once with the same metadata — bridging twice is a no-op.
    load_parsed_module(&mut env, &module, Some("Test.ClassDup".to_string())).expect("second load");

    assert!(
        env.is_class(&class_name),
        "duplicate class loads must keep the inductive registered as a class"
    );
    assert_eq!(
        env.get_class_info(&class_name)
            .expect("class must remain registered")
            .num_params,
        3,
        "duplicate class loads must preserve the original num_params"
    );
}

/// Build a `ParsedModule` carrying BOTH an `attrExtension` `@[class]` entry for
/// `class_name` AND an `instanceExtension` entry registering `instance_name` as
/// an instance of that class. This mirrors a real `.olean` that declares a
/// typeclass and an instance of it in the same module (e.g. a Mathlib file that
/// `class`-declares `Group` and registers an instance for it).
fn module_with_class_and_instance(
    class_name: &str,
    instance_name: &str,
    priority: u32,
) -> ParsedModule {
    use clean_kernel::env::{
        AttrExtEntry, EnvExtensionEntryData, InstanceExtEntry, PersistentExtEntry,
    };

    let class_attr_raw = AttrExtEntry {
        decl_name: Name::from_string(class_name),
        attr_name: Name::from_string("class"),
        priority: 0,
    }
    .to_env_entry();
    let class_attr_data = match class_attr_raw.data {
        EnvExtensionEntryData::Object(bytes) => ParsedExtensionEntryData::Object(bytes),
        EnvExtensionEntryData::Scalar(v) => ParsedExtensionEntryData::Scalar(v),
    };

    let instance_raw = InstanceExtEntry {
        instance_name: Name::from_string(instance_name),
        class_name: Name::from_string(class_name),
        priority,
    }
    .to_env_entry();
    let instance_data = match instance_raw.data {
        EnvExtensionEntryData::Object(bytes) => ParsedExtensionEntryData::Object(bytes),
        EnvExtensionEntryData::Scalar(v) => ParsedExtensionEntryData::Scalar(v),
    };

    ParsedModule {
        const_names: Vec::new(),
        constants: Vec::new(),
        extra_const_names: Vec::new(),
        imports: Vec::new(),
        entries: vec![
            ParsedExtension {
                extension_name: "attrExtension".to_string(),
                entries: vec![ParsedExtensionEntry::Named {
                    name: class_attr_raw.name.to_string(),
                    data: class_attr_data,
                }],
                undecoded_entries: 0,
            },
            ParsedExtension {
                extension_name: "instanceExtension".to_string(),
                entries: vec![ParsedExtensionEntry::Named {
                    name: instance_raw.name.to_string(),
                    data: instance_data,
                }],
                undecoded_entries: 0,
            },
        ],
        clean_payload: None,
    }
}

/// Regression for #olean-class-before-instance-order.
///
/// When a `.olean` declares a typeclass (`@[class]` on an inductive) and an
/// instance of that class in the same module, importing the module must leave
/// the imported class registered in the kernel typeclass registry AND its
/// instance visible to the elaborator's instance synthesis.
///
/// The elaborator's `init_instances_from_env` only surfaces instances whose
/// class is in `env.classes()` (it iterates registered classes and pulls
/// `get_class_instances` per class). So both the class and the instance must be
/// registered for the imported instance to be synthesizable. This test pins
/// that BOTH invariants hold after the import bridges run: the imported class is
/// registered (`is_class`) AND `get_class_instances(class)` is NON-EMPTY — the
/// exact visibility the elaborator depends on for imported typeclasses like
/// Group/Semiring. The import bridges now run `register_classes_from_extension`
/// before `register_instances_from_extension` so the class exists before its
/// instances are associated with it.
#[test]
fn test_load_parsed_module_imported_class_instance_visible_to_synthesis() {
    let mut env = Environment::new();
    let class_name = Name::from_string("Test.MyGroup");
    let inst_name = Name::from_string("Test.instMyGroupNat");

    // The class carrier inductive is imported (present) but starts as a plain
    // inductive, exactly as a real .olean exports the structure before its
    // `@[class]` attribute is materialized.
    register_synthetic_inductive(&mut env, "Test.MyGroup", 1);
    assert!(
        !env.is_class(&class_name),
        "carrier inductive must not be a class before import"
    );
    assert!(
        env.get_class_instances(&class_name).is_empty(),
        "no instances for the class before import"
    );

    let module = module_with_class_and_instance("Test.MyGroup", "Test.instMyGroupNat", 100);
    load_parsed_module(&mut env, &module, Some("Test.GroupModule".to_string()))
        .expect("load module declaring class + instance");

    // The imported `@[class]` attribute must register the carrier as a class so
    // the elaborator's init_instances_from_env iterates it.
    assert!(
        env.is_class(&class_name),
        "imported @[class] must register the carrier as a typeclass"
    );

    // The imported instance must be visible via get_class_instances — this is
    // exactly what the elaborator reads per registered class.
    let instances = env.get_class_instances(&class_name);
    assert_eq!(
        instances.len(),
        1,
        "imported instance of the imported class must be visible to synthesis"
    );
    assert_eq!(instances[0].name, inst_name);
    assert_eq!(instances[0].class_name, class_name);
    assert!(
        env.is_instance(&inst_name),
        "imported instance must be recognized by is_instance()"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// Imported-inductive recursor reducibility (#olean-imported-inductive-reduce)
//
// Validates the end-to-end path: a module imports an inductive together with
// its constructors and recursor (the shape a real `.olean` exports for
// List/Bool/Nat), and the *kernel* can iota-reduce a recursor application on a
// constructor value of that imported type. Without this, imported inductives
// would be inert — registered but not eliminable during elaboration.
//
// These tests build the inductive purely through the import loader
// (`load_parsed_module`), then drive `TypeChecker::whnf` and assert the ACTUAL
// reduced expression, not just that loading succeeded.
// ════════════════════════════════════════════════════════════════════════════

/// Build a `MyBool`-like module: a `Sort 1` enum with two nullary constructors
/// (`MyBool.false`, `MyBool.true`) and its recursor `MyBool.rec`, exactly as a
/// `.olean` exports a simple two-constructor inductive plus eliminator.
///
/// `MyBool.rec : {motive : MyBool → Sort u} → motive MyBool.false →
///               motive MyBool.true → (b : MyBool) → motive b`
///
/// The recursor rule RHS for each nullary constructor selects the corresponding
/// minor premise: `λ motive. λ minor_false. λ minor_true. <minor>` — matching
/// the `λ params. λ motives. λ minors. λ fields. body` shape the kernel's
/// iota reducer applies (see `tc/reduction/mod.rs::try_iota_reduction`).
fn mybool_module() -> ParsedModule {
    use crate::expr::ParsedBinderInfo;
    use crate::level::ParsedLevel;
    use crate::module::{
        ConstantKind, ConstructorValData, InductiveValData, ParsedConstant, RecursorRuleData,
        RecursorValData,
    };

    // MyBool : Sort 1  (i.e. Type)
    let ind_type = ParsedExpr::Sort(ParsedLevel::Succ(Box::new(ParsedLevel::Zero)));
    // Each constructor's type is just `MyBool`.
    let bool_ref = || ParsedExpr::Const("MyBool".to_string(), vec![]);

    // MyBool.rec : {motive : MyBool → Sort u} → motive MyBool.false →
    //              motive MyBool.true → (b : MyBool) → motive b
    let u = || ParsedLevel::Param("u".to_string());
    let motive_dom = ParsedExpr::ForallE(
        "b".to_string(),
        Box::new(bool_ref()),
        Box::new(ParsedExpr::Sort(u())),
        ParsedBinderInfo::Default,
    );
    // motive MyBool.false  (motive is BVar 0 in the minor-premise position)
    let motive_false = ParsedExpr::App(
        Box::new(ParsedExpr::BVar(0)),
        Box::new(ParsedExpr::Const("MyBool.false".to_string(), vec![])),
    );
    // motive MyBool.true  (motive at BVar 1 after the false-minor binder)
    let motive_true = ParsedExpr::App(
        Box::new(ParsedExpr::BVar(1)),
        Box::new(ParsedExpr::Const("MyBool.true".to_string(), vec![])),
    );
    // motive b  (motive at BVar 3 under motive/min_f/min_t/major binders)
    let motive_major =
        ParsedExpr::App(Box::new(ParsedExpr::BVar(3)), Box::new(ParsedExpr::BVar(0)));
    let rec_type = ParsedExpr::ForallE(
        "motive".to_string(),
        Box::new(motive_dom),
        Box::new(ParsedExpr::ForallE(
            "false_case".to_string(),
            Box::new(motive_false),
            Box::new(ParsedExpr::ForallE(
                "true_case".to_string(),
                Box::new(motive_true),
                Box::new(ParsedExpr::ForallE(
                    "b".to_string(),
                    Box::new(bool_ref()),
                    Box::new(motive_major),
                    ParsedBinderInfo::Default,
                )),
                ParsedBinderInfo::Default,
            )),
            ParsedBinderInfo::Default,
        )),
        ParsedBinderInfo::Implicit,
    );

    // RHS for the false rule: λ motive. λ min_f. λ min_t. min_f  (BVar 1)
    let rhs_false = ParsedExpr::Lam(
        "motive".to_string(),
        Box::new(ParsedExpr::Sort(ParsedLevel::Zero)),
        Box::new(ParsedExpr::Lam(
            "min_f".to_string(),
            Box::new(ParsedExpr::Sort(ParsedLevel::Zero)),
            Box::new(ParsedExpr::Lam(
                "min_t".to_string(),
                Box::new(ParsedExpr::Sort(ParsedLevel::Zero)),
                Box::new(ParsedExpr::BVar(1)),
                ParsedBinderInfo::Default,
            )),
            ParsedBinderInfo::Default,
        )),
        ParsedBinderInfo::Default,
    );
    // RHS for the true rule: λ motive. λ min_f. λ min_t. min_t  (BVar 0)
    let rhs_true = ParsedExpr::Lam(
        "motive".to_string(),
        Box::new(ParsedExpr::Sort(ParsedLevel::Zero)),
        Box::new(ParsedExpr::Lam(
            "min_f".to_string(),
            Box::new(ParsedExpr::Sort(ParsedLevel::Zero)),
            Box::new(ParsedExpr::Lam(
                "min_t".to_string(),
                Box::new(ParsedExpr::Sort(ParsedLevel::Zero)),
                Box::new(ParsedExpr::BVar(0)),
                ParsedBinderInfo::Default,
            )),
            ParsedBinderInfo::Default,
        )),
        ParsedBinderInfo::Default,
    );

    ParsedModule {
        const_names: vec![
            "MyBool".to_string(),
            "MyBool.false".to_string(),
            "MyBool.true".to_string(),
            "MyBool.rec".to_string(),
        ],
        constants: vec![
            ParsedConstant {
                name: "MyBool".to_string(),
                kind: ConstantKind::Inductive,
                level_params: vec![],
                type_: Some(ind_type),
                value: None,
                inductive_val: Some(InductiveValData {
                    num_params: 0,
                    num_indices: 0,
                    all: vec!["MyBool".to_string()],
                    ctors: vec!["MyBool.false".to_string(), "MyBool.true".to_string()],
                    is_rec: false,
                    is_unsafe: false,
                    is_reflexive: false,
                    is_nested: false,
                }),
                constructor_val: None,
                recursor_val: None,
                hints: None,
                definition_safety: None,
                quot_kind: None,
            },
            ParsedConstant {
                name: "MyBool.false".to_string(),
                kind: ConstantKind::Constructor,
                level_params: vec![],
                type_: Some(bool_ref()),
                value: None,
                inductive_val: None,
                constructor_val: Some(ConstructorValData {
                    induct: "MyBool".to_string(),
                    cidx: 0,
                    num_params: 0,
                    num_fields: 0,
                    is_unsafe: false,
                }),
                recursor_val: None,
                hints: None,
                definition_safety: None,
                quot_kind: None,
            },
            ParsedConstant {
                name: "MyBool.true".to_string(),
                kind: ConstantKind::Constructor,
                level_params: vec![],
                type_: Some(bool_ref()),
                value: None,
                inductive_val: None,
                constructor_val: Some(ConstructorValData {
                    induct: "MyBool".to_string(),
                    cidx: 1,
                    num_params: 0,
                    num_fields: 0,
                    is_unsafe: false,
                }),
                recursor_val: None,
                hints: None,
                definition_safety: None,
                quot_kind: None,
            },
            ParsedConstant {
                name: "MyBool.rec".to_string(),
                kind: ConstantKind::Recursor,
                level_params: vec!["u".to_string()],
                type_: Some(rec_type),
                value: None,
                inductive_val: None,
                constructor_val: None,
                recursor_val: Some(RecursorValData {
                    all: vec!["MyBool".to_string()],
                    num_params: 0,
                    num_indices: 0,
                    num_motives: 1,
                    num_minors: 2,
                    rules: vec![
                        RecursorRuleData {
                            ctor: "MyBool.false".to_string(),
                            num_fields: 0,
                            rhs: Some(rhs_false),
                        },
                        RecursorRuleData {
                            ctor: "MyBool.true".to_string(),
                            num_fields: 0,
                            rhs: Some(rhs_true),
                        },
                    ],
                    k: false,
                    is_unsafe: false,
                }),
                hints: None,
                definition_safety: None,
                quot_kind: None,
            },
        ],
        extra_const_names: Vec::new(),
        imports: Vec::new(),
        entries: Vec::new(),
        clean_payload: None,
    }
}

/// Apply `MyBool.rec` to `motive`, the two minor premises, and `major`,
/// returning the recursor application expression for the kernel to reduce.
fn mybool_rec_app(motive: Expr, minor_false: Expr, minor_true: Expr, major: Expr) -> Expr {
    use clean_kernel::level::Level;
    let rec = Expr::const_(Name::from_string("MyBool.rec"), vec![Level::zero()]);
    Expr::apps(rec, [motive, minor_false, minor_true, major])
}

#[test]
fn test_imported_inductive_recursor_reduces_on_false_constructor() {
    use clean_kernel::expr::ExprKind;
    use clean_kernel::level::Level;
    use clean_kernel::TypeChecker;

    let mut env = Environment::new();
    let summary = load_parsed_module(&mut env, &mybool_module(), Some("Test.MyBool".to_string()))
        .expect("loading the MyBool inductive module should succeed");
    assert_eq!(
        summary.added_constants, 4,
        "MyBool, its two constructors, and MyBool.rec must all register"
    );

    // The import path must have registered the recursor and constructors so the
    // kernel's iota reducer can find them.
    assert!(
        env.get_recursor(&Name::from_string("MyBool.rec")).is_some(),
        "imported MyBool.rec must be registered as a recursor"
    );
    assert!(
        env.get_constructor(&Name::from_string("MyBool.false"))
            .is_some(),
        "imported MyBool.false must be registered as a constructor"
    );

    // motive := λ _ : MyBool. Prop  (a valid Sort-valued motive)
    let bool_ref = Expr::const_(Name::from_string("MyBool"), vec![]);
    let motive = Expr::lam(
        clean_kernel::expr::BinderInfo::Default,
        bool_ref,
        Expr::prop(),
    );
    let minor_false = Expr::const_(Name::from_string("ResultF"), vec![]);
    let minor_true = Expr::const_(Name::from_string("ResultT"), vec![]);
    let major = Expr::const_(Name::from_string("MyBool.false"), vec![]);

    let app = mybool_rec_app(motive, minor_false.clone(), minor_true, major);

    let tc = TypeChecker::new(&env);
    let reduced = tc.whnf(&app);

    // The recursor on `MyBool.false` must iota-reduce to the false minor premise.
    assert_eq!(
        reduced, minor_false,
        "kernel must reduce MyBool.rec _ ResultF ResultT MyBool.false to ResultF"
    );
    // Sanity: the result is exactly the constant `ResultF`, not a stuck redex.
    assert!(
        matches!(reduced.kind(), ExprKind::Const(name, levels)
            if name == &Name::from_string("ResultF") && levels.is_empty()),
        "reduced form must be the bare ResultF constant, got {reduced:?}"
    );
    let _ = Level::zero(); // keep Level import meaningful across cfgs
}

#[test]
fn test_imported_inductive_recursor_reduces_on_true_constructor() {
    use clean_kernel::TypeChecker;

    let mut env = Environment::new();
    load_parsed_module(&mut env, &mybool_module(), Some("Test.MyBool".to_string()))
        .expect("loading the MyBool inductive module should succeed");

    let bool_ref = Expr::const_(Name::from_string("MyBool"), vec![]);
    let motive = Expr::lam(
        clean_kernel::expr::BinderInfo::Default,
        bool_ref,
        Expr::prop(),
    );
    let minor_false = Expr::const_(Name::from_string("ResultF"), vec![]);
    let minor_true = Expr::const_(Name::from_string("ResultT"), vec![]);
    let major = Expr::const_(Name::from_string("MyBool.true"), vec![]);

    let app = mybool_rec_app(motive, minor_false, minor_true.clone(), major);

    let tc = TypeChecker::new(&env);
    let reduced = tc.whnf(&app);

    assert_eq!(
        reduced, minor_true,
        "kernel must reduce MyBool.rec _ ResultF ResultT MyBool.true to ResultT"
    );
}

#[test]
fn test_imported_inductive_recursor_stuck_on_non_constructor_major() {
    use clean_kernel::TypeChecker;

    // An imported recursor applied to a non-constructor major premise (a free
    // variable / opaque constant of the right type) must remain stuck — iota
    // reduction only fires on a constructor head. This pins that the imported
    // recursor does not over-reduce.
    let mut env = Environment::new();
    load_parsed_module(&mut env, &mybool_module(), Some("Test.MyBool".to_string()))
        .expect("loading the MyBool inductive module should succeed");

    let bool_ref = Expr::const_(Name::from_string("MyBool"), vec![]);
    let motive = Expr::lam(
        clean_kernel::expr::BinderInfo::Default,
        bool_ref,
        Expr::prop(),
    );
    let minor_false = Expr::const_(Name::from_string("ResultF"), vec![]);
    let minor_true = Expr::const_(Name::from_string("ResultT"), vec![]);
    // `someBool` is an opaque constant, not a constructor of MyBool.
    let major = Expr::const_(Name::from_string("someBool"), vec![]);

    let app = mybool_rec_app(motive, minor_false, minor_true, major);

    let tc = TypeChecker::new(&env);
    let reduced = tc.whnf(&app);

    assert_eq!(
        reduced, app,
        "MyBool.rec on a non-constructor major premise must stay stuck (no iota)"
    );
}

/// Build a `MyNat`-like module with a recursive constructor to validate that
/// imported recursors reduce on the *recursive* case, exercising the induction
/// hypothesis (IH) recursion inside the rule RHS — the path that List/Nat
/// recursion relies on.
///
/// `MyNat : Type`, `MyNat.zero : MyNat`, `MyNat.succ : MyNat → MyNat`.
/// `MyNat.rec : {motive : MyNat → Sort u} → motive MyNat.zero →
///              ((n : MyNat) → motive n → motive (MyNat.succ n)) →
///              (m : MyNat) → motive m`
fn mynat_module() -> ParsedModule {
    use crate::expr::ParsedBinderInfo;
    use crate::level::ParsedLevel;
    use crate::module::{
        ConstantKind, ConstructorValData, InductiveValData, ParsedConstant, RecursorRuleData,
        RecursorValData,
    };

    let nat_ref = || ParsedExpr::Const("MyNat".to_string(), vec![]);
    let u = || ParsedLevel::Param("u".to_string());
    let dummy = || ParsedExpr::Sort(ParsedLevel::Zero);

    // MyNat : Type
    let ind_type = ParsedExpr::Sort(ParsedLevel::Succ(Box::new(ParsedLevel::Zero)));
    // MyNat.succ : MyNat → MyNat
    let succ_type = ParsedExpr::ForallE(
        "n".to_string(),
        Box::new(nat_ref()),
        Box::new(nat_ref()),
        ParsedBinderInfo::Default,
    );

    // MyNat.rec type. Structure (outer → inner):
    //   {motive : MyNat → Sort u} → motive zero →
    //   ((n : MyNat) → motive n → motive (succ n)) → (m : MyNat) → motive m
    let motive_dom = ParsedExpr::ForallE(
        "m".to_string(),
        Box::new(nat_ref()),
        Box::new(ParsedExpr::Sort(u())),
        ParsedBinderInfo::Default,
    );
    // motive MyNat.zero  (motive at BVar 0)
    let motive_zero = ParsedExpr::App(
        Box::new(ParsedExpr::BVar(0)),
        Box::new(ParsedExpr::Const("MyNat.zero".to_string(), vec![])),
    );
    // succ minor: (n : MyNat) → motive n → motive (MyNat.succ n)
    //   under [motive, zero_case]: motive is BVar 1 at this depth.
    let succ_minor = ParsedExpr::ForallE(
        "n".to_string(),
        Box::new(nat_ref()),
        Box::new(ParsedExpr::ForallE(
            "ih".to_string(),
            // motive n : motive (BVar 2) applied to n (BVar 0)
            Box::new(ParsedExpr::App(
                Box::new(ParsedExpr::BVar(2)),
                Box::new(ParsedExpr::BVar(0)),
            )),
            // motive (succ n): motive (BVar 3) applied to (succ n) where n is BVar 1
            Box::new(ParsedExpr::App(
                Box::new(ParsedExpr::BVar(3)),
                Box::new(ParsedExpr::App(
                    Box::new(ParsedExpr::Const("MyNat.succ".to_string(), vec![])),
                    Box::new(ParsedExpr::BVar(1)),
                )),
            )),
            ParsedBinderInfo::Default,
        )),
        ParsedBinderInfo::Default,
    );
    // (m : MyNat) → motive m  under [motive, zero_case, succ_case]: motive is BVar 3.
    let major_part = ParsedExpr::ForallE(
        "m".to_string(),
        Box::new(nat_ref()),
        Box::new(ParsedExpr::App(
            Box::new(ParsedExpr::BVar(3)),
            Box::new(ParsedExpr::BVar(0)),
        )),
        ParsedBinderInfo::Default,
    );
    let rec_type = ParsedExpr::ForallE(
        "motive".to_string(),
        Box::new(motive_dom),
        Box::new(ParsedExpr::ForallE(
            "zero_case".to_string(),
            Box::new(motive_zero),
            Box::new(ParsedExpr::ForallE(
                "succ_case".to_string(),
                Box::new(succ_minor),
                Box::new(major_part),
                ParsedBinderInfo::Default,
            )),
            ParsedBinderInfo::Default,
        )),
        ParsedBinderInfo::Implicit,
    );

    // zero rule RHS: λ motive. λ z. λ s. z   (z = BVar 1)
    let rhs_zero = ParsedExpr::Lam(
        "motive".to_string(),
        Box::new(dummy()),
        Box::new(ParsedExpr::Lam(
            "z".to_string(),
            Box::new(dummy()),
            Box::new(ParsedExpr::Lam(
                "s".to_string(),
                Box::new(dummy()),
                Box::new(ParsedExpr::BVar(1)),
                ParsedBinderInfo::Default,
            )),
            ParsedBinderInfo::Default,
        )),
        ParsedBinderInfo::Default,
    );

    // succ rule RHS: λ motive. λ z. λ s. λ field_n.
    //   s field_n (MyNat.rec@{u} motive z s field_n)
    // Binders (outer→inner): motive(BVar3 in body), z(BVar2), s(BVar1), field_n(BVar0).
    let ih = ParsedExpr::App(
        Box::new(ParsedExpr::App(
            Box::new(ParsedExpr::App(
                Box::new(ParsedExpr::App(
                    Box::new(ParsedExpr::Const("MyNat.rec".to_string(), vec![u()])),
                    Box::new(ParsedExpr::BVar(3)), // motive
                )),
                Box::new(ParsedExpr::BVar(2)), // z
            )),
            Box::new(ParsedExpr::BVar(1)), // s
        )),
        Box::new(ParsedExpr::BVar(0)), // field_n
    );
    let succ_body = ParsedExpr::App(
        Box::new(ParsedExpr::App(
            Box::new(ParsedExpr::BVar(1)), // s
            Box::new(ParsedExpr::BVar(0)), // field_n
        )),
        Box::new(ih),
    );
    let rhs_succ = ParsedExpr::Lam(
        "motive".to_string(),
        Box::new(dummy()),
        Box::new(ParsedExpr::Lam(
            "z".to_string(),
            Box::new(dummy()),
            Box::new(ParsedExpr::Lam(
                "s".to_string(),
                Box::new(dummy()),
                Box::new(ParsedExpr::Lam(
                    "field_n".to_string(),
                    Box::new(dummy()),
                    Box::new(succ_body),
                    ParsedBinderInfo::Default,
                )),
                ParsedBinderInfo::Default,
            )),
            ParsedBinderInfo::Default,
        )),
        ParsedBinderInfo::Default,
    );

    ParsedModule {
        const_names: vec![
            "MyNat".to_string(),
            "MyNat.zero".to_string(),
            "MyNat.succ".to_string(),
            "MyNat.rec".to_string(),
        ],
        constants: vec![
            ParsedConstant {
                name: "MyNat".to_string(),
                kind: ConstantKind::Inductive,
                level_params: vec![],
                type_: Some(ind_type),
                value: None,
                inductive_val: Some(InductiveValData {
                    num_params: 0,
                    num_indices: 0,
                    all: vec!["MyNat".to_string()],
                    ctors: vec!["MyNat.zero".to_string(), "MyNat.succ".to_string()],
                    is_rec: true,
                    is_unsafe: false,
                    is_reflexive: false,
                    is_nested: false,
                }),
                constructor_val: None,
                recursor_val: None,
                hints: None,
                definition_safety: None,
                quot_kind: None,
            },
            ParsedConstant {
                name: "MyNat.zero".to_string(),
                kind: ConstantKind::Constructor,
                level_params: vec![],
                type_: Some(nat_ref()),
                value: None,
                inductive_val: None,
                constructor_val: Some(ConstructorValData {
                    induct: "MyNat".to_string(),
                    cidx: 0,
                    num_params: 0,
                    num_fields: 0,
                    is_unsafe: false,
                }),
                recursor_val: None,
                hints: None,
                definition_safety: None,
                quot_kind: None,
            },
            ParsedConstant {
                name: "MyNat.succ".to_string(),
                kind: ConstantKind::Constructor,
                level_params: vec![],
                type_: Some(succ_type),
                value: None,
                inductive_val: None,
                constructor_val: Some(ConstructorValData {
                    induct: "MyNat".to_string(),
                    cidx: 1,
                    num_params: 0,
                    num_fields: 1,
                    is_unsafe: false,
                }),
                recursor_val: None,
                hints: None,
                definition_safety: None,
                quot_kind: None,
            },
            ParsedConstant {
                name: "MyNat.rec".to_string(),
                kind: ConstantKind::Recursor,
                level_params: vec!["u".to_string()],
                type_: Some(rec_type),
                value: None,
                inductive_val: None,
                constructor_val: None,
                recursor_val: Some(RecursorValData {
                    all: vec!["MyNat".to_string()],
                    num_params: 0,
                    num_indices: 0,
                    num_motives: 1,
                    num_minors: 2,
                    rules: vec![
                        RecursorRuleData {
                            ctor: "MyNat.zero".to_string(),
                            num_fields: 0,
                            rhs: Some(rhs_zero),
                        },
                        RecursorRuleData {
                            ctor: "MyNat.succ".to_string(),
                            num_fields: 1,
                            rhs: Some(rhs_succ),
                        },
                    ],
                    k: false,
                    is_unsafe: false,
                }),
                hints: None,
                definition_safety: None,
                quot_kind: None,
            },
        ],
        extra_const_names: Vec::new(),
        imports: Vec::new(),
        entries: Vec::new(),
        clean_payload: None,
    }
}

#[test]
fn test_imported_recursive_inductive_recursor_reduces_on_zero() {
    use clean_kernel::level::Level;
    use clean_kernel::TypeChecker;

    let mut env = Environment::new();
    load_parsed_module(&mut env, &mynat_module(), Some("Test.MyNat".to_string()))
        .expect("loading the MyNat inductive module should succeed");

    // motive := λ _ : MyNat. MyNat   (a Type-valued motive, so the result is a MyNat)
    let nat_ref = Expr::const_(Name::from_string("MyNat"), vec![]);
    let motive = Expr::lam(
        clean_kernel::expr::BinderInfo::Default,
        nat_ref.clone(),
        nat_ref.clone(),
    );
    // zero_case := MyNat.zero ; succ_case := λ n ih. MyNat.succ ih
    let zero_ctor = Expr::const_(Name::from_string("MyNat.zero"), vec![]);
    let succ_ctor = Expr::const_(Name::from_string("MyNat.succ"), vec![]);
    let zero_case = zero_ctor.clone();
    let succ_case = Expr::lam(
        clean_kernel::expr::BinderInfo::Default,
        nat_ref.clone(),
        Expr::lam(
            clean_kernel::expr::BinderInfo::Default,
            nat_ref.clone(),
            Expr::app(succ_ctor.clone(), Expr::bvar(0)),
        ),
    );

    let rec = Expr::const_(
        Name::from_string("MyNat.rec"),
        vec![Level::succ(Level::zero())],
    );
    let app = Expr::apps(rec, [motive, zero_case, succ_case, zero_ctor.clone()]);

    let tc = TypeChecker::new(&env);
    let reduced = tc.whnf(&app);

    // MyNat.rec ... MyNat.zero must iota-reduce to the zero case = MyNat.zero.
    assert_eq!(
        reduced, zero_ctor,
        "MyNat.rec on MyNat.zero must reduce to the zero case (MyNat.zero)"
    );
}

#[test]
fn test_imported_recursive_inductive_recursor_reduces_on_succ_with_ih() {
    use clean_kernel::level::Level;
    use clean_kernel::TypeChecker;

    let mut env = Environment::new();
    load_parsed_module(&mut env, &mynat_module(), Some("Test.MyNat".to_string()))
        .expect("loading the MyNat inductive module should succeed");

    let nat_ref = Expr::const_(Name::from_string("MyNat"), vec![]);
    // motive := λ _. MyNat (so the recursor computes a MyNat)
    let motive = Expr::lam(
        clean_kernel::expr::BinderInfo::Default,
        nat_ref.clone(),
        nat_ref.clone(),
    );
    let zero_ctor = Expr::const_(Name::from_string("MyNat.zero"), vec![]);
    let succ_ctor = Expr::const_(Name::from_string("MyNat.succ"), vec![]);
    // succ_case := λ n ih. MyNat.succ ih   (build succ of the IH result)
    let succ_case = Expr::lam(
        clean_kernel::expr::BinderInfo::Default,
        nat_ref.clone(),
        Expr::lam(
            clean_kernel::expr::BinderInfo::Default,
            nat_ref.clone(),
            Expr::app(succ_ctor.clone(), Expr::bvar(0)),
        ),
    );
    // major := MyNat.succ MyNat.zero  (the number 1)
    let one = Expr::app(succ_ctor.clone(), zero_ctor.clone());

    let rec = Expr::const_(
        Name::from_string("MyNat.rec"),
        vec![Level::succ(Level::zero())],
    );
    let app = Expr::apps(rec, [motive, zero_ctor.clone(), succ_case, one]);

    // Expected fully-reduced value: succ_case applied to (0, IH on 0).
    // IH on MyNat.zero reduces to zero_case = MyNat.zero, so the result is
    // MyNat.succ MyNat.zero — i.e. the recursion preserves the value through
    // one IH step. We assert against `is_def_eq` to allow any residual redex
    // in the un-forced subterm, then confirm the head shape via whnf.
    let expected = Expr::app(succ_ctor.clone(), zero_ctor.clone());

    let tc = TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(&app, &expected),
        "MyNat.rec on (succ zero) with succ_case=λ n ih. succ ih must compute to (succ zero)"
    );

    // And the whnf head must be the succ constructor (iota actually fired and
    // exposed the constructor head — the imported recursor is not stuck).
    let reduced = tc.whnf(&app);
    let head = reduced.get_app_fn();
    assert!(
        matches!(head.kind(), clean_kernel::expr::ExprKind::Const(name, _)
            if name == &Name::from_string("MyNat.succ")),
        "whnf of MyNat.rec on (succ zero) must expose MyNat.succ at the head, got {reduced:?}"
    );
}

// =============================================================================
// Unqualified name resolution over an imported namespace (`open List`).
//
// Real-Mathlib gate: after a `.olean` module declaring the qualified names
// `List.map` / `List.filter` is imported into an `Environment`, a downstream
// `open List` must let a user write the unqualified `map` and have it resolve
// to the imported `List.map` constant.
//
// The resolver itself (`NamespaceState` / `process_open`) lives in `clean-elab`,
// which `clean-olean` does not (and must not) depend on. What `clean-olean` is
// responsible for — and what these tests pin — is the *registration contract*
// that `process_open` relies on:
//
//   1. selective open (`open List (map)`): `process_open` calls
//      `env.get_const(List.map)` and aliases the survivors. So an imported
//      qualified name must be reachable via `env.get_const`.
//   2. full open (`open List`): `process_open` scans `env.constants()` for the
//      `List.` prefix, keeps direct children, and builds `short -> qualified`
//      aliases. So imported qualified names must appear in `env.constants()`
//      under their fully-qualified name.
//
// To validate end-to-end without depending on `clean-elab`, these tests
// reproduce `process_open`'s full-open algorithm verbatim against the real
// imported environment and assert the *actual resolved constant name*
// (`List.map`), not merely that resolution succeeded.
// =============================================================================

/// Build a `ParsedModule` declaring the given names as closed `Definition`
/// constants (closed `Sort 1` type and `Sort 0` value), mirroring how an
/// imported `.olean` carries qualified declarations such as `List.map`.
///
/// `Definition`s route through the same `extend_constants_structural` path as a
/// real `.olean` import, so they land in `env.constants()` / `env.get_const`
/// exactly like the genuine article — which is what the namespace resolver
/// reads.
fn module_with_definitions(names: &[&str]) -> ParsedModule {
    use crate::level::ParsedLevel;
    use crate::module::{ConstantKind, ParsedConstant};

    let constants = names
        .iter()
        .map(|name| ParsedConstant {
            name: (*name).to_string(),
            kind: ConstantKind::Definition,
            level_params: Vec::new(),
            // Closed type and value: structurally valid (no free vars / metavars).
            type_: Some(ParsedExpr::Sort(ParsedLevel::Succ(Box::new(
                ParsedLevel::Zero,
            )))),
            value: Some(ParsedExpr::Sort(ParsedLevel::Zero)),
            inductive_val: None,
            constructor_val: None,
            recursor_val: None,
            hints: None,
            definition_safety: None,
            quot_kind: None,
        })
        .collect();

    ParsedModule {
        const_names: names.iter().map(|n| (*n).to_string()).collect(),
        constants,
        extra_const_names: Vec::new(),
        imports: Vec::new(),
        entries: Vec::new(),
        clean_payload: None,
    }
}

/// Resolve `short` against an opened namespace exactly as `clean-elab`'s
/// `process_open` does for a full `open <ns>`: scan every constant in `env`,
/// keep the direct children of `<ns>.`, and map each child's short tail to its
/// fully-qualified [`Name`]. Returns the qualified `Name` an unqualified
/// reference would resolve to, or `None` if no opened-namespace child matches.
///
/// This mirrors `clean_elab::namespace_open::process_single_open` (full-open
/// branch) so the test exercises the real registration contract end-to-end
/// without taking a dependency on `clean-elab`.
fn resolve_via_open(env: &Environment, namespace: &str, short: &str) -> Option<Name> {
    let prefix_dot = format!("{namespace}.");
    let mut aliases: HashMap<String, Name> = HashMap::new();
    for ci in env.constants() {
        let ci_str = ci.name.to_string();
        if let Some(suffix) = ci_str.strip_prefix(&prefix_dot) {
            // Only direct children participate in a full `open` (no nested dots).
            if !suffix.contains('.') {
                aliases.insert(suffix.to_string(), ci.name.clone());
            }
        }
    }
    aliases.get(short).cloned()
}

#[test]
fn test_open_imported_namespace_resolves_unqualified_name_to_qualified_const() {
    let mut env = Environment::new();
    let module = module_with_definitions(&["List.map", "List.filter"]);

    let summary = load_parsed_module(&mut env, &module, Some("Init.Data.List".to_string()))
        .expect("module declaring List.map / List.filter should load");
    assert_eq!(
        summary.added_constants, 2,
        "both qualified definitions must be registered"
    );

    // Selective-open contract (`open List (map)`): `process_open` reaches the
    // imported constant via `env.get_const` on the fully-qualified name.
    let qualified_map = Name::from_string("List.map");
    assert!(
        env.get_const(&qualified_map).is_some(),
        "imported List.map must be reachable via get_const for selective opens"
    );

    // Full-open contract (`open List`): the unqualified `map` must resolve to
    // the imported `List.map`. Assert the ACTUAL resolved constant name.
    let resolved_map = resolve_via_open(&env, "List", "map")
        .expect("after `open List`, unqualified `map` must resolve");
    assert_eq!(
        resolved_map, qualified_map,
        "unqualified `map` must resolve to the imported `List.map`, got {resolved_map}"
    );

    let resolved_filter = resolve_via_open(&env, "List", "filter")
        .expect("after `open List`, unqualified `filter` must resolve");
    assert_eq!(
        resolved_filter,
        Name::from_string("List.filter"),
        "unqualified `filter` must resolve to the imported `List.filter`, got {resolved_filter}"
    );
}

#[test]
fn test_open_imported_namespace_does_not_resolve_unrelated_or_unopened_names() {
    let mut env = Environment::new();
    let module = module_with_definitions(&["List.map", "List.filter"]);
    load_parsed_module(&mut env, &module, Some("Init.Data.List".to_string()))
        .expect("module declaring List.map / List.filter should load");

    // A name not declared under `List` must not resolve via `open List`.
    assert!(
        resolve_via_open(&env, "List", "foldr").is_none(),
        "unqualified `foldr` was never imported under List and must not resolve"
    );

    // Opening an unrelated (empty) namespace contributes no aliases, so the
    // imported `List.map` does not leak in under `map`.
    assert!(
        resolve_via_open(&env, "Array", "map").is_none(),
        "opening Array (no imported children) must not resolve `map` to List.map"
    );
}

#[test]
fn test_open_imported_namespace_excludes_nested_grandchildren() {
    // A full `open List` aliases only direct children (`List.map`), not
    // grandchildren (`List.Internal.aux`) — matching `process_open`'s
    // "no nested dots" rule. This guards against an importer or resolver that
    // would over-eagerly expose deeper names unqualified.
    let mut env = Environment::new();
    let module = module_with_definitions(&["List.map", "List.Internal.aux"]);
    load_parsed_module(&mut env, &module, Some("Init.Data.List".to_string()))
        .expect("module with a nested grandchild should load");

    assert_eq!(
        resolve_via_open(&env, "List", "map"),
        Some(Name::from_string("List.map")),
        "direct child `map` must resolve under `open List`"
    );
    assert!(
        resolve_via_open(&env, "List", "aux").is_none(),
        "grandchild `List.Internal.aux` must not resolve as bare `aux` under `open List`"
    );
    // But it is still a direct child of the (deeper) `List.Internal` namespace.
    assert_eq!(
        resolve_via_open(&env, "List.Internal", "aux"),
        Some(Name::from_string("List.Internal.aux")),
        "`aux` must resolve under `open List.Internal`"
    );
}
