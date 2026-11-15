// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Actual public cached/parallel callers. Legacy assumed loading is explicit;
//! these tests do not attest an external dependency closure or authorize it.

use clean_kernel::env::{Declaration, Environment};
use clean_kernel::expr::{BinderInfo, Expr};
use clean_kernel::level::Level;
use clean_kernel::name::{Name, NameInner};
use clean_olean::test_support::compiled_fixture_dir;
use clean_olean::{
    load_module_with_deps_cached, load_module_with_deps_parallel, ModuleCache, OleanExporter,
};
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

fn define(env: &mut Environment, name: Name, levels: Vec<Name>, ty: Expr, value: Expr) {
    env.add_decl(Declaration::Definition {
        name,
        level_params: levels,
        type_: ty,
        value,
        is_reducible: true,
    })
    .expect("fresh checked fixture declaration");
}

fn fixture(alternate: bool) -> Environment {
    let mut env = Environment::default();
    let ty = Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_());
    for (i, name) in [
        Name::anon().str("Alias").str("value"),
        Name::anon().str("Alias.value"),
        Name::anon().str("7"),
        Name::anon().str("07"),
        Name::anon().num(7),
        Name::anon().str(""),
    ]
    .into_iter()
    .enumerate()
    {
        let value = Expr::lam(
            BinderInfo::Default,
            Expr::type_(),
            if (i % 2 == 0) != alternate {
                Expr::bvar(0)
            } else {
                Expr::prop()
            },
        );
        define(&mut env, name.clone(), vec![], ty.clone(), value);
        define(
            &mut env,
            Name::anon().str("reader").num(i as u64),
            vec![],
            ty.clone(),
            Expr::const_(name, vec![]),
        );
    }
    for (i, name) in [
        Name::anon().str("u.dot"),
        Name::anon().str("u").str("dot"),
        Name::anon().str("07"),
        Name::anon().num(7),
    ]
    .into_iter()
    .enumerate()
    {
        let sort = Expr::sort(Level::param(name.clone()));
        define(
            &mut env,
            Name::anon().str("keep").num(i as u64),
            vec![name],
            Expr::pi(
                BinderInfo::Default,
                sort.clone(),
                Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
            ),
            Expr::lam(
                BinderInfo::Default,
                sort,
                Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
            ),
        );
    }
    env
}

fn write_fixture(path: &Path, env: &Environment) {
    let bytes =
        OleanExporter::export_with_env(env, &[], &[], "0000000000000000000000000000000000000000")
            .expect("export");
    std::fs::write(path, bytes).expect("write fixture");
    let time = std::time::UNIX_EPOCH + std::time::Duration::from_secs(1_700_000_000);
    std::fs::File::options()
        .write(true)
        .open(path)
        .expect("open fixture")
        .set_times(std::fs::FileTimes::new().set_modified(time))
        .expect("fixed mtime");
}

fn ordinary_fixture(alternate: bool) -> Environment {
    let mut env = Environment::default();
    define(
        &mut env,
        Name::anon().str("stable"),
        vec![],
        Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_()),
        Expr::lam(
            BinderInfo::Default,
            Expr::type_(),
            if alternate {
                Expr::prop()
            } else {
                Expr::bvar(0)
            },
        ),
    );
    env
}

fn load(
    parallel: bool,
    path: &Path,
    cache: &ModuleCache,
) -> Result<Environment, clean_olean::ImportError> {
    // The pinned toolchain's `lib/lean` follows the fixture's own directory so a
    // fixture that imports `Init` resolves its closure against the exact pin.
    // Until 2026-09-15 this read `CLEAN_OLEAN_PINNED_LEAN_LIB` with
    // `std::env::var_os` at RUNTIME, where cargo never sets it (build.rs emits
    // it as a compile-time `cargo:rustc-env` only), so the push was dead code in
    // every cargo run; `pinned_lean_lib_path()` honours the compile-time value
    // and falls back to resolving the workspace `lean-toolchain` pin, and the
    // `expect` is the owner's fail-closed spelling (`companion_root_tests`).
    let mut paths = vec![path.parent().expect("fixture parent").to_path_buf()];
    paths.push(
        clean_olean::pinned_lean_lib_path().expect("explicit pinned Lean fixture is required"),
    );
    let name = path
        .file_stem()
        .expect("stem")
        .to_str()
        .expect("UTF8 fixture name");
    let mut env = Environment::default();
    let summaries = if parallel {
        load_module_with_deps_parallel(&mut env, name, &paths, cache)
    } else {
        load_module_with_deps_cached(&mut env, name, &paths, cache)
    }?;
    assert!(
        summaries.iter().all(|s| s.skipped_constants.is_empty()),
        "{summaries:?}"
    );
    Ok(env)
}

fn exact(expected: &Environment, actual: &Environment) {
    assert_eq!(actual.constants().count(), expected.constants().count());
    for item in expected.constants() {
        let found = actual
            .get_const(&item.name)
            .expect("exact typed declaration identity");
        assert_eq!(found.name, item.name);
        assert_eq!(found.level_params, item.level_params);
        assert_eq!(found.type_, item.type_);
        assert_eq!(found.value, item.value);
    }
}

#[test]
fn cached_and_parallel_cold_warm_preserve_owners_references_and_universes() {
    let dir = tempfile::tempdir().expect("private directory");
    let path = dir.path().join("Fixture.olean");
    let expected = fixture(false);
    write_fixture(&path, &expected);
    for parallel in [false, true] {
        let cache = ModuleCache::new();
        for _ in 0..2 {
            exact(
                &expected,
                &load(parallel, &path, &cache).expect("cached import"),
            );
        }
        assert_eq!(cache.len(), 1);
        cache.clear();
        assert!(cache.is_empty());
    }
}

#[test]
fn same_module_name_and_mtime_in_distinct_paths_do_not_alias() {
    let first = tempfile::tempdir().expect("first root");
    let second = tempfile::tempdir().expect("second root");
    let one = first.path().join("Fixture.olean");
    let two = second.path().join("Fixture.olean");
    let expected_one = ordinary_fixture(false);
    let expected_two = ordinary_fixture(true);
    write_fixture(&one, &expected_one);
    write_fixture(&two, &expected_two);
    for parallel in [false, true] {
        let cache = ModuleCache::new();
        // The first load's exactness is tested above; this control isolates reuse.
        let _ = load(parallel, &one, &cache).expect("first import");
        exact(
            &expected_two,
            &load(parallel, &two, &cache).expect("other root import"),
        );
    }
}

#[test]
fn same_path_and_mtime_content_change_invalidates_cache() {
    for parallel in [false, true] {
        let dir = tempfile::tempdir().expect("private root");
        let path = dir.path().join("Fixture.olean");
        let cache = ModuleCache::new();
        write_fixture(&path, &ordinary_fixture(false));
        let _ = load(parallel, &path, &cache).expect("initial import");
        let expected = ordinary_fixture(true);
        write_fixture(&path, &expected);
        exact(
            &expected,
            &load(parallel, &path, &cache).expect("changed import"),
        );
    }
}

#[test]
fn malformed_present_server_is_an_error_in_both_cached_paths() {
    for parallel in [false, true] {
        let dir = tempfile::tempdir().expect("private root");
        let path = dir.path().join("Fixture.olean");
        write_fixture(&path, &ordinary_fixture(false));
        let cache = ModuleCache::new();
        let _ = load(parallel, &path, &cache).expect("initial import without server");
        std::fs::write(path.with_extension("olean.server"), b"malformed").expect("server bytes");
        assert!(load(parallel, &path, &cache).is_err());
    }
}

#[test]
fn present_private_part_is_not_silently_ignored_when_server_is_absent() {
    for parallel in [false, true] {
        let dir = tempfile::tempdir().expect("private root");
        let path = dir.path().join("Fixture.olean");
        write_fixture(&path, &ordinary_fixture(false));
        let cache = ModuleCache::new();
        let _ = load(parallel, &path, &cache).expect("initial import without private part");
        std::fs::write(path.with_extension("olean.private"), b"malformed").expect("private bytes");
        assert!(load(parallel, &path, &cache).is_err());
    }
}

/// Copy one pinned-Lean artifact of a fixture family under
/// `tests/fixtures/lean/<pin>/` (compiled or generated on first use, fail-closed
/// when the toolchain is absent) into a private root as `Fixture.olean`, so the
/// cached loaders see a fresh path and mtime per test.
fn actual_fixture(family: &str, file: &str) -> (tempfile::TempDir, PathBuf) {
    let source = compiled_fixture_dir(family).join(file);
    assert!(source.is_file(), "missing fixture: {}", source.display());
    let dir = tempfile::tempdir().expect("private fixture root");
    let path = dir.path().join("Fixture.olean");
    std::fs::copy(&source, &path).expect("copy exact pinned Lean fixture");
    (dir, path)
}

/// `typed_names/TypedNames.olean` (fixture family F3): a `prelude` module with
/// no imports, so its closure under the cached loaders is the module alone.
#[test]
fn real_quoted_identity_and_all_three_local_theorem_checks_survive_cached_loading() {
    let (_dir, path) = actual_fixture("typed_names", "TypedNames.olean");
    for parallel in [false, true] {
        let cache = ModuleCache::new();
        for _ in 0..2 {
            let env = load(parallel, &path, &cache).expect("actual cached import");
            for (reader, target) in [
                ("readNested", Name::anon().str("Alias").str("value")),
                ("readQuoted", Name::anon().str("Alias.value")),
                ("read07", Name::anon().str("07")),
            ] {
                let references = env
                    .get_const(&Name::anon().str(reader))
                    .expect("reader")
                    .value
                    .as_ref()
                    .expect("body")
                    .collect_constants();
                assert!(references.contains(&target), "wrong {reader} reference");
            }
            assert_eq!(
                env.get_const(&Name::anon().str("keep"))
                    .expect("universe owner")
                    .level_params,
                [Name::anon().str("u.dot")]
            );
            let names: BTreeSet<String> = ["nestedExpected", "quotedExpected", "digitExpected"]
                .into_iter()
                .map(str::to_owned)
                .collect();
            let (passed, failed, errors) =
                clean_olean::verify_batch_full::typecheck_constants_full(&env, &names, 100_000);
            assert_eq!((passed, failed), (3, 0), "{errors:?}");
        }
    }
}

/// `numeric_probe/NumericProbeSupported.olean` (fixture family F4), minted by
/// `GenNumericProbe.lean` with `imports = #[]`: the `NumericProbe.*` population
/// filter below is what the lost original needed to separate the six from its
/// Lean dependency closure; on this fixture the closure is empty and the filter
/// is simply the module's whole population.
#[test]
fn real_numeric_and_numeric_string_twins_survive_cached_loading() {
    let (_dir, path) = actual_fixture("numeric_probe", "NumericProbeSupported.olean");
    for parallel in [false, true] {
        let cache = ModuleCache::new();
        for _ in 0..2 {
            let env = load(parallel, &path, &cache).expect("supported actual numeric import");
            let p = Name::anon().str("NumericProbe");
            let numeric_population = env
                .constants()
                .filter(|item| match item.name.inner() {
                    NameInner::Str(parent, _) | NameInner::Num(parent, _) => parent.as_ref() == &p,
                    NameInner::Anon => false,
                })
                .count();
            assert_eq!(
                numeric_population, 6,
                "all six generator declarations retained through the cached loaders"
            );
            for name in [
                p.clone().num(0),
                p.clone().num(7),
                p.clone().num(1u64 << 63),
                p.clone().str("0"),
                p.clone().str("7"),
                p.str("07"),
            ] {
                let item = env.get_const(&name).expect("exact numeric/string twin");
                assert_eq!(item.type_, Expr::type_());
                assert_eq!(item.value, Some(Expr::prop()));
            }
        }
    }
}

/// `numeric_probe/NumericProbeSeven.olean` (fixture family F5): the six plus
/// `NumericProbe.<2^64>`, a two-limb mpz component both cached paths must refuse.
#[test]
fn original_over_u64_name_is_refused_by_both_cached_paths() {
    let (_dir, path) = actual_fixture("numeric_probe", "NumericProbeSeven.olean");
    for parallel in [false, true] {
        let result = load(parallel, &path, &ModuleCache::new());
        let error = match result {
            Ok(_) => panic!("over-u64 name must refuse"),
            Err(error) => error.to_string(),
        };
        assert!(error.contains("Nat"), "{error}");
    }
}
