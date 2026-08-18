// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// NO NAME THIS STAGE DECLARES MAY ALREADY EXIST IN ANOTHER STAGE.
///
/// Measured, not hypothetical: the first full-spec run of this stage died
/// after 86 minutes on `Duplicate declaration: ir_scalar_tag` — a name
/// `eval_ir_ops.rs` already uses for a DIFFERENT thing (the constructor tag
/// of an `IRScalar`, for the equality decision). The projections here are
/// now `ir_agg_disc` / `ir_vals_head_disc` / `ir_outcome_disc`, and this
/// test turns that 86-minute failure into a millisecond one by scanning the
/// sibling `core_spec` sources for the same declaration.
#[test]
fn test_declared_names_are_unique_across_core_spec() {
    use std::path::PathBuf;
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src/spec/core_spec");
    let mut names: Vec<String> = Vec::new();
    for src in ALL.iter().chain(BLOCKS.iter()) {
        let mut it = src.split_whitespace();
        let kind = it.next().unwrap_or("");
        let name = it.next().unwrap_or("");
        assert!(
            matches!(kind, "def" | "inductive") && !name.is_empty(),
            "every source must begin `def <name>` or `inductive <name>`: {src}"
        );
        names.push(name.to_string());
    }
    assert!(
        names.len() >= 30,
        "coverage denominator: this stage declares {} names, which is too few to be the \
         whole stage — the scan would then be checking almost nothing",
        names.len()
    );

    let entries = std::fs::read_dir(&dir).expect("core_spec must be readable");
    let mut clashes: Vec<String> = Vec::new();
    for entry in entries.flatten() {
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) != Some("rs") {
            continue;
        }
        if path.file_name().and_then(|f| f.to_str()) == Some("eval_ir_from_source.rs") {
            continue;
        }
        let Ok(text) = std::fs::read_to_string(&path) else {
            continue;
        };
        for name in &names {
            for kw in ["def ", "inductive "] {
                let needle = format!("{kw}{name} ");
                let alt = format!("{kw}{name} :");
                if text.contains(&needle) || text.contains(&alt) {
                    clashes.push(format!("{} already declares `{kw}{name}`", path.display()));
                }
            }
        }
    }
    clashes.sort();
    clashes.dedup();
    assert!(
        clashes.is_empty(),
        "DUPLICATE DECLARATION(S) — the full spec registers stages sequentially and the \
         kernel refuses a second declaration of a name, which costs a whole spec build to \
         discover:\n  {}",
        clashes.join("\n  ")
    );
}
