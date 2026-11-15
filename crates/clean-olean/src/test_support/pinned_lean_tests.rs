// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit tests of the pinned-Lean fixture helper (`pinned_lean.rs`, which
//! declares this file as its child module so private items are in scope).
//! The last test compiles a real family and shells out to the pinned Lean;
//! like every helper here it fails closed when the toolchain is absent.

use super::*;

/// Cargo accepts a relative target directory. A child Lean invocation changes its working
/// directory, so its search path must still find the already compiled sibling modules.
/// Isolate environment and cwd in child test processes instead of mutating the parent.
#[test]
fn test_relative_target_dir_preserves_real_pinned_sibling_imports() {
    let cwd = tempfile::tempdir().expect("isolated fixture caller");
    let oracle_test = "test_support::pinned_lean::pinned_lean_tests::test_selftest_family_compiles_and_the_oracle_reads_it_in_both_modes";
    for target in [
        PathBuf::from("relative build cache"),
        cwd.path().join("absolute build cache"),
    ] {
        let output = Command::new(std::env::current_exe().expect("current test binary"))
            .args(["--exact", oracle_test, "--nocapture", "--test-threads=1"])
            .current_dir(cwd.path())
            .env("CARGO_TARGET_DIR", &target)
            .output()
            .expect("isolated real pinned fixture test");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            output.status.success(),
            "target={target:?}: {}\n{stdout}\n{stderr}",
            output.status
        );
        assert!(
            stdout.contains("test result: ok. 1 passed; 0 failed;"),
            "the original oracle test must actually execute: {stdout}\n{stderr}"
        );
        let cache = cwd.path().join(&target).join(CACHE_DIR_NAME);
        assert!(cache.is_dir(), "fixture cache absent: {}", cache.display());
    }
}

const VERSION: &str = "Lean (version 4.30.0-rc2)";

fn family(entries: &[(&str, &[u8])]) -> FamilyFiles {
    entries
        .iter()
        .map(|(path, bytes)| ((*path).to_string(), bytes.to_vec()))
        .collect()
}

#[test]
fn test_parse_order_accepts_stems_run_lines_comments_and_blanks() {
    let steps = parse_order(
        "# twins first\nModule.part\n\nModule/part\nRoot\nrun GenNumericProbe.lean out.olean --over-u64\n",
    );
    assert_eq!(
        steps,
        vec![
            OrderStep::Compile("Module.part".to_string()),
            OrderStep::Compile("Module/part".to_string()),
            OrderStep::Compile("Root".to_string()),
            OrderStep::Run(vec![
                "GenNumericProbe.lean".to_string(),
                "out.olean".to_string(),
                "--over-u64".to_string(),
            ]),
        ]
    );
}

#[test]
fn test_parse_order_accepts_a_theory_line() {
    assert_eq!(
        parse_order("theory chk_lia\nChkLIAPlanted\n"),
        vec![
            OrderStep::Theory("chk_lia".to_string()),
            OrderStep::Compile("ChkLIAPlanted".to_string()),
        ]
    );
}

#[test]
fn test_parse_order_accepts_a_from_line() {
    assert_eq!(
        parse_order("from semr SemR\nVF5Sem\n"),
        vec![
            OrderStep::From {
                family: "semr".to_string(),
                stem: "SemR".to_string(),
            },
            OrderStep::Compile("VF5Sem".to_string()),
        ]
    );
}

#[test]
#[should_panic(expected = "`from` needs a sibling family name and a module stem")]
fn test_parse_order_rejects_a_from_path() {
    let _ = parse_order("from ../semr SemR\n");
}

#[test]
#[should_panic(expected = "`theory` needs a theory directory name")]
fn test_parse_order_rejects_a_theory_path() {
    let _ = parse_order("theory ../escape\n");
}

#[test]
fn test_the_chk_lia_theory_lists_its_modules_only() {
    let (source, files, stems) = theory_files_and_stems("chk_lia");
    assert!(source.ends_with("theories/chk_lia"), "{}", source.display());
    assert_eq!(stems, ["ChkLIA", "ChkLIASpec", "ChkLIACases"]);
    assert!(files.contains_key("lakefile.toml") && files.contains_key("ChkLIA.lean"));
}

#[test]
#[should_panic(expected = "bare module path stem")]
fn test_parse_order_rejects_a_stem_carrying_an_extension() {
    let _ = parse_order("Root.lean\n");
}

#[test]
#[should_panic(expected = "lists no steps")]
fn test_parse_order_rejects_an_empty_order() {
    let _ = parse_order("# nothing here\n\n");
}

#[test]
fn test_content_hash_moves_with_version_order_path_and_bytes() {
    let files = family(&[("ORDER", b"Root\n"), ("Root.lean", b"prelude\n")]);
    let base = content_hash(VERSION, &files);
    assert_eq!(base.len(), 32);
    assert_eq!(base, content_hash(VERSION, &files));
    assert_ne!(base, content_hash("Lean (version 4.31.0)", &files));
    assert_ne!(
        base,
        content_hash(
            VERSION,
            &family(&[("ORDER", b"Root\n# x\n"), ("Root.lean", b"prelude\n")])
        ),
        "an ORDER edit moves the key"
    );
    assert_ne!(
        base,
        content_hash(
            VERSION,
            &family(&[("ORDER", b"Root\n"), ("Other.lean", b"prelude\n")])
        ),
        "a renamed source moves the key"
    );
    assert_ne!(
        base,
        content_hash(
            VERSION,
            &family(&[("ORDER", b"Root\n"), ("Root.lean", b"prelude\n\n")])
        ),
        "an edited source moves the key"
    );
}

/// The 2026-09-15 finding: the key covered `ORDER` and `*.lean` only, so a
/// README, a `CONSTANTS` design file or a `tools/*.lean` inspector could change
/// under a cache directory that kept being served. Every regular file is in
/// the key now, and so is the recipe version the code cannot otherwise expose.
#[test]
fn test_content_hash_covers_every_family_file_and_the_recipe_version() {
    let files = family(&[
        ("ORDER", b"Root\n"),
        ("Root.lean", b"prelude\n"),
        ("README.md", b"# family\n"),
        ("CONSTANTS", b"Alias.value\n"),
        ("tools/Inspect.lean", b"import Lean\n"),
    ]);
    let base = content_hash(VERSION, &files);

    let mut readme = files.clone();
    readme
        .get_mut("README.md")
        .expect("README.md is in the family")
        .push(b'\n');
    assert_ne!(base, content_hash(VERSION, &readme), "one README byte");

    let mut constants = files.clone();
    constants.insert("CONSTANTS".to_string(), b"Alias.value\nextra\n".to_vec());
    assert_ne!(base, content_hash(VERSION, &constants), "CONSTANTS bytes");

    let mut tool = files.clone();
    tool.insert(
        "tools/Inspect.lean".to_string(),
        b"import Lean\n-- v2\n".to_vec(),
    );
    assert_ne!(base, content_hash(VERSION, &tool), "a tools/ file");

    let mut added = files.clone();
    added.insert("NOTES".to_string(), Vec::new());
    assert_ne!(base, content_hash(VERSION, &added), "an added empty file");

    assert_eq!(
        base,
        content_hash_with_recipe(RECIPE_VERSION, VERSION, &files),
        "content_hash is content_hash_with_recipe at RECIPE_VERSION"
    );
    assert_ne!(
        base,
        content_hash_with_recipe(RECIPE_VERSION.wrapping_add(1), VERSION, &files),
        "a recipe bump moves every key"
    );
}

#[test]
fn test_collect_family_files_lists_every_regular_file_by_relative_path() {
    let dir = tempfile::tempdir().expect("temp family directory");
    let root = dir.path();
    for (path, bytes) in [
        ("ORDER", &b"Root\nSub/part\n"[..]),
        ("Root.lean", b"prelude\n"),
        ("README.md", b"# family\n"),
        ("CONSTANTS", b"a\nb\n"),
        ("Sub/part.lean", b"prelude\n"),
        ("tools/Inspect.lean", b"import Lean\n"),
    ] {
        let file = root.join(path);
        if let Some(parent) = file.parent() {
            fs::create_dir_all(parent).expect("create fixture sub-directory");
        }
        fs::write(&file, bytes).expect("write fixture file");
    }
    let mut files = FamilyFiles::new();
    collect_family_files(root, root, &mut files);
    let listed: Vec<&str> = files.keys().map(String::as_str).collect();
    assert_eq!(
        listed,
        [
            "CONSTANTS",
            "ORDER",
            "README.md",
            "Root.lean",
            "Sub/part.lean",
            "tools/Inspect.lean",
        ]
    );
    assert_eq!(files["ORDER"], b"Root\nSub/part\n");
    assert_eq!(files["Sub/part.lean"], b"prelude\n");
}

#[cfg(unix)]
#[test]
#[should_panic(expected = "is a symlink")]
fn test_collect_family_files_refuses_a_symlink() {
    let dir = tempfile::tempdir().expect("temp family directory");
    let root = dir.path();
    fs::write(root.join("Root.lean"), b"prelude\n").expect("write fixture file");
    std::os::unix::fs::symlink(root.join("Root.lean"), root.join("Link.lean"))
        .expect("create symlink");
    let mut files = FamilyFiles::new();
    collect_family_files(root, root, &mut files);
}

#[test]
fn test_fixture_root_is_named_by_the_pin_and_holds_the_oracle() {
    let version = pinned_toolchain_version();
    assert!(version.starts_with('v'), "pin version `{version}`");
    assert_eq!(
        fixture_root().file_name().and_then(|name| name.to_str()),
        Some(version.as_str())
    );
    assert!(
        fixture_root().join(ORACLE_SCRIPT).is_file(),
        "missing {}",
        fixture_root().join(ORACLE_SCRIPT).display()
    );
}

/// Fail-closed by design: the pinned toolchain must be installed.
#[test]
fn test_pinned_lean_bin_reports_the_pinned_version() {
    let bin = pinned_lean_bin();
    assert!(bin.is_file(), "{}", bin.display());
    let version = pinned_lean_version();
    let pin = pinned_toolchain_version();
    let bare = pin.strip_prefix('v').unwrap_or(&pin);
    assert!(
        version.contains(bare),
        "`lean --version` = `{version}` does not name the pin `{pin}`"
    );
}

/// End to end: compile the oracle's own probe family (a `prelude` twin, a
/// hierarchical twin, an ordinary module importing both, and a
/// `module`-header source), then read it back through the oracle in both
/// modes. Every number is taken from the oracle, none is typed here.
#[test]
fn test_selftest_family_compiles_and_the_oracle_reads_it_in_both_modes() {
    let dir = compiled_fixture_dir("oracle/selftest");
    for artifact in [
        "Sib.olean",
        "Sub/part.olean",
        "Probe.olean",
        "ModProbe.olean",
        "ModProbe.olean.server",
        "ModProbe.olean.private",
    ] {
        assert!(
            dir.join(artifact).is_file(),
            "missing {artifact} in {}",
            dir.display()
        );
    }
    assert_eq!(
        compiled_fixture_dir("oracle/selftest"),
        dir,
        "second call is a cache hit"
    );

    let probe = dir.join("Probe.olean");
    let raw = run_oracle(&[probe.to_str().expect("utf-8 fixture path")]);
    let part = &raw["parts"][0];
    let constants = part["constants"].as_array().expect("constants array");
    assert!(!constants.is_empty());
    assert_eq!(
        constants.len(),
        part["const_names"]
            .as_array()
            .expect("const_names array")
            .len()
    );
    assert!(
        constants
            .iter()
            .any(|constant| constant["kind"].as_str() == Some("inductive")
                && constant["family"]["num_nested"].is_u64()),
        "the inductive family must carry Lean's numNested"
    );
    assert!(!part["entries"]
        .as_array()
        .expect("entries array")
        .is_empty());

    let triple: Vec<PathBuf> = [
        "ModProbe.olean",
        "ModProbe.olean.server",
        "ModProbe.olean.private",
    ]
    .iter()
    .map(|name| dir.join(name))
    .collect();
    let triple_args: Vec<&str> = triple
        .iter()
        .map(|path| path.to_str().expect("utf-8 fixture path"))
        .collect();
    let parts = run_oracle(&triple_args);
    assert_eq!(parts["parts"].as_array().expect("parts array").len(), 3);
    assert_eq!(parts["regions_kept"].as_u64(), Some(3));

    let env = run_oracle(&[
        "--env",
        "Probe",
        "--search-path",
        dir.to_str().expect("utf-8 fixture path"),
    ]);
    let rows = env["rows"].as_array().expect("rows array");
    assert_eq!(
        rows.len(),
        constants.len(),
        "default probe rows are the module's own constants"
    );
    assert!(rows
        .iter()
        .any(|row| row["is_instance"].as_bool() == Some(true)));
    assert!(rows
        .iter()
        .all(|row| row["constant_present"].as_bool() == Some(true)));
    assert!(env["classes"]
        .as_array()
        .expect("classes array")
        .iter()
        .any(|row| row["is_class"].as_bool() == Some(true)));
}
