// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Drift test for the generated `docs/cli/` Markdown tree.
//!
//! The `gen_cli_docs` binary (`src/bin/gen_cli_docs.rs`) writes one Markdown
//! file per `FeatureDescriptor` plus a top-level `index.md`. Over time it is
//! easy for a contributor to add or rename a descriptor and forget to rerun
//! the generator; this test closes that loop by:
//!
//! 1. Calling the same in-process renderer the binary uses
//!    (`clean_cli::__test_support::render_all_docs`).
//! 2. Reading every top-level `*.md` file out of the committed
//!    `docs/cli/` directory.
//! 3. Comparing the two file trees. If any file is missing, extra, or has
//!    different contents, the test fails with a concise per-file diff and
//!    instructs the reader to rerun `cargo gen-cli-docs` (the cargo alias that
//!    replaced the former `scripts/gen_cli_docs.sh` wrapper).
//!
//! Important: this test DOES NOT shell out to the generator — it runs the
//! rendering logic directly so it works in CI environments without a bash
//! toolchain and so test failures are clearly attributable to the Rust
//! renderer, not shell quoting.
//!
//! Part of Epic #3436 Phase 5 (#3482).

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

use clean_cli::__test_support::{all_features, doc_index_filename, render_all_docs};

/// Resolve the workspace root from `CARGO_MANIFEST_DIR`.
///
/// `CARGO_MANIFEST_DIR` points at `crates/clean-cli`; the workspace root is
/// two directories up. Using `env!` rather than reading the environment at
/// runtime keeps the resolution fixed at compile time and panic-free at the
/// call site.
fn workspace_root() -> PathBuf {
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    manifest_dir
        .parent()
        .and_then(Path::parent)
        .map(Path::to_path_buf)
        .expect("workspace root: two parents above CARGO_MANIFEST_DIR must exist")
}

/// Read every top-level `*.md` file out of `dir` into a
/// `filename -> contents` map. Non-Markdown files and sub-directories are
/// ignored so hand-authored narrative docs can coexist with the generated
/// tree in the future if desired.
fn read_committed_tree(dir: &Path) -> BTreeMap<String, String> {
    let entries = fs::read_dir(dir).unwrap_or_else(|err| {
        panic!(
            "docs/cli/ is missing or unreadable at {}: {err}\n\
             Run `cargo gen-cli-docs` to regenerate.",
            dir.display()
        )
    });

    let mut out = BTreeMap::new();
    for entry in entries {
        let entry = entry.expect("reading docs/cli/ entry failed");
        let path = entry.path();
        if !path.is_file() {
            continue;
        }
        let Some(name) = path.file_name().and_then(|n| n.to_str()) else {
            continue;
        };
        if !name.ends_with(".md") {
            continue;
        }
        let contents = fs::read_to_string(&path)
            .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
        out.insert(name.to_owned(), contents);
    }
    out
}

/// Summarise a diff between two files as a bounded-line preview so panic
/// messages stay readable even for a large descriptor tree.
fn first_differing_lines(expected: &str, actual: &str, max_lines: usize) -> String {
    let mut lines = Vec::new();
    for (idx, (exp, act)) in expected.lines().zip(actual.lines()).enumerate() {
        if exp != act {
            lines.push(format!("  line {} expected: {exp}", idx + 1));
            lines.push(format!("  line {} actual  : {act}", idx + 1));
            if lines.len() >= max_lines * 2 {
                lines.push("  ... (truncated)".to_owned());
                break;
            }
        }
    }
    if lines.is_empty() {
        // Same prefix; one tree has extra trailing lines.
        let exp_lines = expected.lines().count();
        let act_lines = actual.lines().count();
        format!("  trailing-line count differs (expected {exp_lines}, actual {act_lines})")
    } else {
        lines.join("\n")
    }
}

/// The one drift test that gates the whole tree. A single test (rather than
/// N-per-file) keeps failure output consolidated so the contributor sees
/// every stale file in one pass.
#[test]
fn docs_cli_is_generated_freshly() {
    let root = workspace_root();
    let docs_dir = root.join("docs").join("cli");

    let descriptors = all_features();
    let expected: BTreeMap<String, String> = render_all_docs(&descriptors);
    let actual: BTreeMap<String, String> = read_committed_tree(&docs_dir);

    let expected_names: BTreeSet<&str> = expected.keys().map(String::as_str).collect();
    let actual_names: BTreeSet<&str> = actual.keys().map(String::as_str).collect();

    let missing: Vec<&&str> = expected_names.difference(&actual_names).collect();
    let extra: Vec<&&str> = actual_names.difference(&expected_names).collect();

    let mut differing: Vec<(&str, String)> = Vec::new();
    for name in expected_names.intersection(&actual_names) {
        let exp = expected.get(*name).expect("present in expected");
        let act = actual.get(*name).expect("present in actual");
        if exp != act {
            differing.push((*name, first_differing_lines(exp, act, 6)));
        }
    }

    if missing.is_empty() && extra.is_empty() && differing.is_empty() {
        // Sanity: the generator always emits an index; this would only
        // fail if the generator was accidentally silenced.
        assert!(
            actual.contains_key(doc_index_filename()),
            "committed docs/cli/ must contain {}",
            doc_index_filename()
        );
        return;
    }

    let mut report = String::new();
    report.push_str(
        "docs/cli/ has drifted from the FeatureDescriptor registry.\n\
         Run `cargo gen-cli-docs` to regenerate, then commit the result.\n",
    );
    if !missing.is_empty() {
        report.push_str("\nMissing files (present in registry, absent on disk):\n");
        for name in &missing {
            report.push_str(&format!("  - {name}\n"));
        }
    }
    if !extra.is_empty() {
        report.push_str(
            "\nStale files (present on disk, absent in registry — descriptor \
             renamed or removed?):\n",
        );
        for name in &extra {
            report.push_str(&format!("  - {name}\n"));
        }
    }
    if !differing.is_empty() {
        report.push_str("\nDiffering contents (first differing lines):\n");
        for (name, diff) in &differing {
            report.push_str(&format!("  * {name}\n{diff}\n"));
        }
    }

    panic!("{report}");
}

/// The shell wrapper `scripts/gen_cli_docs.sh` was migrated to the
/// `gen-cli-docs` cargo alias in `.cargo/config.toml` (Wave 70 scripts→Rust
/// consolidation). The original contract — the doc-generation entrypoint must
/// drive the in-repo `gen_cli_docs` binary through a `--locked` cargo run — is
/// unchanged; only its home moved. This test now validates that alias so the
/// `--locked` guarantee cannot silently regress.
#[test]
fn gen_cli_docs_entrypoint_uses_locked_cargo_run() {
    let root = workspace_root();
    let config = root.join(".cargo").join("config.toml");
    let contents = fs::read_to_string(&config)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", config.display()));

    let alias_line = contents
        .lines()
        .map(str::trim)
        .find(|line| line.starts_with("gen-cli-docs"))
        .unwrap_or_else(|| {
            panic!(
                "{} must define the gen-cli-docs alias that replaced scripts/gen_cli_docs.sh",
                config.display()
            )
        });

    assert!(
        alias_line.contains("\"run\""),
        "{} gen-cli-docs alias must invoke the in-repo gen_cli_docs binary with cargo run; \
         offending line: {alias_line}",
        config.display()
    );
    assert!(
        alias_line.contains("gen_cli_docs"),
        "{} gen-cli-docs alias must target the gen_cli_docs binary; offending line: {alias_line}",
        config.display()
    );
    assert!(
        alias_line.contains("\"--locked\""),
        "{} gen-cli-docs alias must pass --locked to cargo run; offending line: {alias_line}",
        config.display()
    );
}
