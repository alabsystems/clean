// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The import world gate, through every public module loader
//! (`load_olean_file`, `load_module_with_deps*`) and through
//! `LeanWorldScope`, which a loader that reads parts itself (the
//! `load_parsed_module*` callers) holds (`formats-import-world-gate`,
//! docs/DECISIONS.md R38, R81).
//!
//! Pinned `lean` reads an `.olean` part only when its header carries its own
//! build's identity: version, flags and githash. Until 2026-10-17 Clean read
//! any part whose header parsed, and mixed parts of different Lean builds in
//! one environment without a word. Every fixture here is tracked and every
//! foreign identity is a rewrite of one, so nothing needs an installed
//! toolchain.
//!
//! The refusals are matched on their Debug spelling, so that this file
//! compiles against the importer from before the gate and shows what it did.

use clean_kernel::env::Environment;
use clean_olean::{
    load_module_with_deps, load_module_with_deps_bounded, load_module_with_deps_cached,
    load_module_with_deps_parallel, load_modules_with_deps, load_olean_file, ImportError,
    LeanWorldScope, ModuleCache, OleanExporter,
};
use std::fs;
use std::path::{Path, PathBuf};

/// The Lean v4.33.1 release's githash (its `Init/Prelude.olean` header).
const V4_33_1_GITHASH: &[u8; 40] = b"819816b2e0a3bf405af45ae5c7af2491d8f5bee6";
/// The pinned (v4.30.0-rc2) build's githash, which the fixtures carry.
const PINNED_GITHASH: &str = "3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc";
/// The githash `clean lake` hands Clean's exporter.
const CLEAN_GITHASH: &str = "1ea5000000000000000000000000000000000000";

fn fixtures() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/olean")
}

fn read(rel: &str) -> Vec<u8> {
    let path = fixtures().join(rel);
    fs::read(&path).unwrap_or_else(|e| panic!("fixture {}: {e}", path.display()))
}

/// `bytes` (a v2 header) as Lean v4.33.1 wrote it: header bytes 7..80, the
/// version string and the githash, rewritten.
fn as_v4_33_1(mut bytes: Vec<u8>) -> Vec<u8> {
    let mut version = [0u8; 33];
    version[..6].copy_from_slice(b"4.33.1");
    bytes[7..40].copy_from_slice(&version);
    bytes[40..80].copy_from_slice(V4_33_1_GITHASH);
    bytes
}

/// A directory holding the closure-cache pair: the pinned-Lean leaf `Init`
/// and `Target` (`prelude` + `import Init`), `target` standing for Target.
fn closure(target: Vec<u8>) -> tempfile::TempDir {
    let dir = tempfile::tempdir().expect("tmp");
    fs::write(
        dir.path().join("Init.olean"),
        read("v4.30.0/closure_cache/Init.olean"),
    )
    .expect("Init");
    fs::write(dir.path().join("Target.olean"), target).expect("Target");
    dir
}

/// The Debug spelling of the error `result` must be.
fn error_of<T: std::fmt::Debug>(what: &str, result: Result<T, ImportError>) -> (String, String) {
    match result {
        Ok(loaded) => panic!("{what}: loaded, but must be refused: {loaded:?}"),
        Err(e) => (format!("{e:?}"), e.to_string()),
    }
}

/// `result` is an `UnsupportedLeanWorld` refusal of `module` that names
/// `found` and the pinned world it could have been. (`load_olean_file`
/// labels a module by its whole path, so the label need only end with it.)
fn assert_unsupported<T: std::fmt::Debug>(
    what: &str,
    result: Result<T, ImportError>,
    module: &str,
    found: &str,
) {
    let (debug, display) = error_of(what, result);
    assert!(
        debug.starts_with("UnsupportedLeanWorld"),
        "{what}: refused by its Lean world, not by {debug}"
    );
    assert!(
        debug.contains(&format!("{module}\", found: ")),
        "{what}: names {module}: {debug}"
    );
    assert!(display.contains(found), "{what}: names {found}: {display}");
    assert!(
        display.contains("v4.30.0-rc2"),
        "{what}: names the pinned world: {display}"
    );
}

/// Exit (a): pinned Lean's `Target` with header bytes 7..80 rewritten to
/// v4.33.1's is refused by every module loader, by its Lean world, before
/// its import `Init` is loaded.
#[test]
fn test_world_gate_v4_33_1_header_is_refused_by_every_loader() {
    let target = as_v4_33_1(read("v4.30.0/closure_cache/Target.olean"));
    let dir = closure(target);
    let paths = vec![dir.path().to_path_buf()];
    let found = std::str::from_utf8(V4_33_1_GITHASH).expect("ascii");

    assert_unsupported(
        "load_olean_file",
        load_olean_file(&mut Environment::new(), dir.path().join("Target.olean")),
        "Target",
        found,
    );
    assert_unsupported(
        "load_module_with_deps",
        load_module_with_deps(&mut Environment::new(), "Target", &paths),
        "Target",
        found,
    );
    assert_unsupported(
        "load_module_with_deps_bounded",
        load_module_with_deps_bounded(&mut Environment::new(), "Target", &paths, 64),
        "Target",
        found,
    );
    assert_unsupported(
        "load_module_with_deps_cached",
        load_module_with_deps_cached(
            &mut Environment::new(),
            "Target",
            &paths,
            &ModuleCache::new(),
        ),
        "Target",
        found,
    );
    assert_unsupported(
        "load_module_with_deps_parallel",
        load_module_with_deps_parallel(
            &mut Environment::new(),
            "Target",
            &paths,
            &ModuleCache::new(),
        ),
        "Target",
        found,
    );
    assert_unsupported(
        "load_modules_with_deps",
        load_modules_with_deps(&mut Environment::new(), &["Target".to_string()], &paths),
        "Target",
        found,
    );
}

/// Exit (a), second half: flipping the flags byte alone (6) makes another
/// identity, which pinned `lean` refuses too.
#[test]
fn test_world_gate_flipped_flags_byte_is_refused() {
    let mut target = read("v4.30.0/closure_cache/Target.olean");
    assert_eq!(target[6], 1, "the pinned build writes flags 0x01");
    target[6] = 0;
    let dir = closure(target);
    assert_unsupported(
        "load_module_with_deps",
        load_module_with_deps(
            &mut Environment::new(),
            "Target",
            &[dir.path().to_path_buf()],
        ),
        "Target",
        "flags 0x00",
    );
}

/// A rewritten leaf, which imports nothing, is refused as well.
#[test]
fn test_world_gate_rewritten_leaf_is_refused() {
    let dir = tempfile::tempdir().expect("tmp");
    fs::write(
        dir.path().join("Init.olean"),
        as_v4_33_1(read("v4.30.0/closure_cache/Init.olean")),
    )
    .expect("Init");
    let found = std::str::from_utf8(V4_33_1_GITHASH).expect("ascii");
    assert_unsupported(
        "load_olean_file",
        load_olean_file(&mut Environment::new(), dir.path().join("Init.olean")),
        "Init",
        found,
    );
    assert_unsupported(
        "load_module_with_deps",
        load_module_with_deps(&mut Environment::new(), "Init", &[dir.path().to_path_buf()]),
        "Init",
        found,
    );
}

/// A module-system triple of a foreign world is refused by its world before
/// its imports are looked for: none of them is on the search path, so a
/// loader that walked them first would fail on a missing module instead.
#[test]
fn test_world_gate_foreign_triple_is_refused_before_its_imports() {
    let dir = tempfile::tempdir().expect("tmp");
    for part in ["Sigma.olean", "Sigma.olean.server", "Sigma.olean.private"] {
        fs::write(
            dir.path().join(part),
            as_v4_33_1(read(&format!("v4.30.0/module-system/{part}"))),
        )
        .expect("part");
    }
    let found = std::str::from_utf8(V4_33_1_GITHASH).expect("ascii");
    assert_unsupported(
        "load_module_with_deps",
        load_module_with_deps(
            &mut Environment::new(),
            "Sigma",
            &[dir.path().to_path_buf()],
        ),
        "Sigma",
        found,
    );
    assert_unsupported(
        "load_module_with_deps_cached",
        load_module_with_deps_cached(
            &mut Environment::new(),
            "Sigma",
            &[dir.path().to_path_buf()],
            &ModuleCache::new(),
        ),
        "Sigma",
        found,
    );
}

/// Two readable worlds in one environment: v4.8.0's `FactLib` and the
/// pinned build's `Init`, both leaves that load alone, are refused together.
#[test]
fn test_world_gate_two_worlds_in_one_environment_are_mixed() {
    let witness = fixtures().join("v4.8.0/witness");
    let pinned = fixtures().join("v4.30.0/closure_cache");
    for (first, first_dir, second, second_dir, second_world) in [
        ("FactLib", &witness, "Init", &pinned, "v4.30.0-rc2"),
        ("Init", &pinned, "FactLib", &witness, "v4.8.0"),
    ] {
        let mut env = Environment::new();
        load_module_with_deps(&mut env, first, std::slice::from_ref(first_dir))
            .unwrap_or_else(|e| panic!("{first} loads alone: {e}"));
        let (debug, display) = error_of(
            second,
            load_module_with_deps(&mut env, second, std::slice::from_ref(second_dir)),
        );
        assert!(
            debug.starts_with("MixedLeanWorlds"),
            "{second} after {first}: refused as a second world, not by {debug}"
        );
        assert!(
            display.contains(second_world) && display.contains(first),
            "{display}"
        );
    }
}

/// The readable worlds load without a declaration: v4.8.0 (Frontend-only)
/// and v4.13.0 (Historical).
#[test]
fn test_world_gate_readable_worlds_load_without_a_declaration() {
    load_olean_file(
        &mut Environment::new(),
        fixtures().join("v4.8.0/witness/FactLib.olean"),
    )
    .expect("v4.8.0 is Frontend-only: read without a declaration");
    load_olean_file(
        &mut Environment::new(),
        fixtures().join("v4.13.0/custom/Minimal.olean"),
    )
    .expect("v4.13.0 is Historical: read without a declaration");
}

/// A v1 Lean part whose githash is no world's is refused, the same as a v2
/// one: v4.13.0's `Minimal` with another githash.
#[test]
fn test_world_gate_unknown_v1_githash_is_refused() {
    let mut bytes = read("v4.13.0/custom/Minimal.olean");
    bytes[6..46].copy_from_slice(V4_33_1_GITHASH);
    let dir = tempfile::tempdir().expect("tmp");
    fs::write(dir.path().join("Minimal.olean"), bytes).expect("Minimal");
    assert_unsupported(
        "load_olean_file",
        load_olean_file(&mut Environment::new(), dir.path().join("Minimal.olean")),
        "Minimal",
        std::str::from_utf8(V4_33_1_GITHASH).expect("ascii"),
    );
}

/// A v3 header (Lean v4.36.0-rc1's closure format, a Canary per R38) is
/// refused by its Lean world, naming its version, not as an unparsable
/// header.
#[test]
fn test_world_gate_v3_header_is_refused_by_name() {
    let mut target = read("v4.30.0/closure_cache/Target.olean");
    target[5] = 3;
    let mut version = [0u8; 33];
    version[..10].copy_from_slice(b"4.36.0-rc1");
    target[7..40].copy_from_slice(&version);
    let dir = closure(target);
    assert_unsupported(
        "load_module_with_deps",
        load_module_with_deps(
            &mut Environment::new(),
            "Target",
            &[dir.path().to_path_buf()],
        ),
        "Target",
        "4.36.0-rc1",
    );
}

/// Exit (d), the negative control: an artifact Clean's exporter wrote
/// (header v1, githash `1ea5…`) is of no Lean world and loads over the
/// pinned build's `Init`, as it loads over v4.8.0's `FactLib`.
#[test]
fn test_world_gate_clean_written_artifact_loads_over_any_world() {
    for (import, leaf) in [
        ("Init", "v4.30.0/closure_cache/Init.olean"),
        ("FactLib", "v4.8.0/witness/FactLib.olean"),
    ] {
        let dir = tempfile::tempdir().expect("tmp");
        fs::write(dir.path().join(format!("{import}.olean")), read(leaf)).expect("leaf");
        let user = OleanExporter::export_minimal(&[(import, false)], &[], &[], CLEAN_GITHASH)
            .expect("export");
        assert_eq!(&user[6..46], CLEAN_GITHASH.as_bytes());
        fs::write(dir.path().join("CleanUser.olean"), user).expect("CleanUser");
        let mut env = Environment::new();
        let summaries = load_module_with_deps(&mut env, "CleanUser", &[dir.path().to_path_buf()])
            .unwrap_or_else(|e| panic!("CleanUser over {import}: {e}"));
        assert_eq!(summaries.len(), 2, "{import} and CleanUser: {summaries:?}");
    }
    // The pinned build's own pair loads: the control for exit (a).
    let target = read("v4.30.0/closure_cache/Target.olean");
    assert_eq!(&target[40..80], PINNED_GITHASH.as_bytes());
    let dir = closure(target);
    load_module_with_deps(
        &mut Environment::new(),
        "Target",
        &[dir.path().to_path_buf()],
    )
    .expect("the pinned build's closure loads");
}

/// `LeanWorldScope` (R81), the gate of a loader that reads parts itself:
/// the first Lean part binds it, a foreign identity is refused by name, a
/// second readable world is mixed, and a Clean-written part is of no world.
#[test]
fn test_world_scope_binds_refuses_and_mixes_as_an_environment_does() {
    let mut scope = LeanWorldScope::new();
    assert_eq!(scope.world(), None);
    scope
        .admit_part("Init", &read("v4.30.0/closure_cache/Init.olean"))
        .expect("the pinned leaf binds the scope");
    assert_eq!(scope.world(), Some("v4.30.0-rc2"));
    assert_unsupported(
        "LeanWorldScope::admit_part",
        scope.admit_part(
            "Target",
            &as_v4_33_1(read("v4.30.0/closure_cache/Target.olean")),
        ),
        "Target",
        std::str::from_utf8(V4_33_1_GITHASH).expect("ascii"),
    );
    let (debug, display) = error_of(
        "FactLib after Init",
        scope.admit_part("FactLib", &read("v4.8.0/witness/FactLib.olean")),
    );
    assert!(debug.starts_with("MixedLeanWorlds"), "{debug}");
    assert!(
        display.contains("`FactLib` is of Lean v4.8.0") && display.contains("`Init`"),
        "{display}"
    );
    let user =
        OleanExporter::export_minimal(&[("Init", false)], &[], &[], CLEAN_GITHASH).expect("export");
    scope
        .admit_part("CleanUser", &user)
        .expect("a Clean-written part is of no world");
    assert_eq!(scope.world(), Some("v4.30.0-rc2"));
}

/// A file is read only as far as its writer needs: the 88-byte header of a
/// v2 part, the whole of a v1 part (its writer is told by its root
/// `ModuleData`).
#[test]
fn test_world_scope_reads_a_v2_header_alone_and_a_v1_part_whole() {
    let dir = tempfile::tempdir().expect("tmp");
    let header = dir.path().join("Header.olean");
    fs::write(&header, &read("v4.30.0/closure_cache/Init.olean")[..88]).expect("header");
    let mut scope = LeanWorldScope::new();
    scope
        .admit_olean_file("Header", &header)
        .expect("a v2 header alone names its world");
    assert_eq!(scope.world(), Some("v4.30.0-rc2"));

    let mut scope = LeanWorldScope::new();
    scope
        .admit_olean_file("Minimal", &fixtures().join("v4.13.0/custom/Minimal.olean"))
        .expect("a whole v1 part");
    assert_eq!(scope.world(), Some("v4.13.0"));

    let missing = dir.path().join("Missing.olean");
    let (debug, _) = error_of(
        "a missing part",
        LeanWorldScope::new().admit_olean_file("Missing", &missing),
    );
    assert!(debug.starts_with("FileUnreadable"), "{debug}");
}

/// Companions are admitted beside their base, labelled as the module
/// loaders label them; a module with none admits its base alone.
#[test]
fn test_world_scope_admits_companions_by_their_labels() {
    let triple = fixtures().join("v4.30.0/module-system");
    let mut scope = LeanWorldScope::new();
    scope
        .admit_artifact("Sigma", &triple.join("Sigma.olean"))
        .expect("the pinned triple");
    assert_eq!(scope.world(), Some("v4.30.0-rc2"));

    let dir = tempfile::tempdir().expect("tmp");
    for part in ["Sigma.olean", "Sigma.olean.server", "Sigma.olean.private"] {
        let bytes = read(&format!("v4.30.0/module-system/{part}"));
        let bytes = if part.ends_with(".private") {
            as_v4_33_1(bytes)
        } else {
            bytes
        };
        fs::write(dir.path().join(part), bytes).expect("part");
    }
    assert_unsupported(
        "LeanWorldScope::admit_artifact",
        LeanWorldScope::new().admit_artifact("Sigma", &dir.path().join("Sigma.olean")),
        "Sigma._private",
        std::str::from_utf8(V4_33_1_GITHASH).expect("ascii"),
    );

    let mut scope = LeanWorldScope::new();
    scope
        .admit_artifact("Init", &fixtures().join("v4.30.0/closure_cache/Init.olean"))
        .expect("no companions");
    assert_eq!(scope.world(), Some("v4.30.0-rc2"));
}

/// A scope starts from an environment's binding and carries its own onto
/// one: an environment bound by a scope refuses a part of another world.
#[test]
fn test_world_scope_and_environment_share_one_binding() {
    let mut env = Environment::new();
    load_olean_file(
        &mut env,
        fixtures().join("v4.30.0/closure_cache/Init.olean"),
    )
    .expect("pinned leaf");
    assert_eq!(
        LeanWorldScope::of_environment(&env).world(),
        Some("v4.30.0-rc2")
    );

    let mut v4_8_0 = LeanWorldScope::new();
    v4_8_0
        .admit_part("FactLib", &read("v4.8.0/witness/FactLib.olean"))
        .expect("v4.8.0 leaf");
    let (debug, _) = error_of(
        "a v4.8.0 scope onto a pinned environment",
        v4_8_0.bind_environment(&mut env),
    );
    assert!(debug.starts_with("MixedLeanWorlds"), "{debug}");

    let mut fresh = Environment::new();
    v4_8_0
        .bind_environment(&mut fresh)
        .expect("an unbound environment takes the scope's world");
    assert_eq!(clean_olean::environment_world(&fresh), Some("v4.8.0"));
    let (debug, _) = error_of(
        "the pinned leaf into an environment a v4.8.0 scope bound",
        load_olean_file(
            &mut fresh,
            fixtures().join("v4.30.0/closure_cache/Init.olean"),
        ),
    );
    assert!(debug.starts_with("MixedLeanWorlds"), "{debug}");
}
