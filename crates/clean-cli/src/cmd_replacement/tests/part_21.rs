// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests (slice 21): the Rust producer's source scope against the known-answer
//! tables that live once in `scripts/check_add_decl_ratchet.py` (2026-11-16).
//! `add_decl_scan_scope_matches_the_python_producer` (slice 19) holds the two
//! producers to the same SET of files; these hold each to the right ANSWER,
//! which a parity arm cannot do when both are blind in the same place.

use crate::cmd_replacement::*;

/// 2026-11-16: the MODULE TREE's known answers, on both producers. The table
/// lives once, in the Python producer (`--module-tree-cases`); its selftest
/// answers it there and this arm answers it here, so a shared blindness in the
/// set-equality arm in slice 19 cannot hide a wrong resolution in either. Among the
/// cases: a module reached only through `#[cfg(test)] mod a;` one file up, via
/// an ordinary `a.rs` that owns `a/` (the 79a1983740 shape), is test code; the
/// same files without the gate are production.
///
/// This arm fails closed: no python3, no table, no pass.
#[test]
fn the_module_tree_answers_every_layout_correctly() {
    use crate::cmd_replacement::rust_source_scope::classify;
    let out = Command::new("python3")
        .arg(repo_root().join("scripts/check_add_decl_ratchet.py"))
        .arg("--module-tree-cases")
        .output()
        .expect("python3 must be available; the table lives in the Python producer");
    assert!(out.status.success(), "--module-tree-cases failed");
    let cases: Vec<serde_json::Value> =
        serde_json::from_slice(&out.stdout).expect("the case table is JSON");
    assert!(
        cases.len() >= 16,
        "the case table collapsed to {}",
        cases.len()
    );
    let mut wrong = Vec::new();
    for case in &cases {
        let dir = tempfile::tempdir().expect("tempdir");
        let crate_dir = dir.path().join("crates/c");
        let files = case["files"].as_object().expect("files is an object");
        for (relative, source) in files {
            let path = crate_dir.join(relative);
            fs::create_dir_all(path.parent().expect("parent")).expect("mkdir");
            fs::write(&path, source.as_str().expect("source is text")).expect("write");
        }
        let scope = classify(dir.path());
        let target = crate_dir
            .join(case["target"].as_str().expect("target"))
            .canonicalize()
            .expect("the case's target exists");
        let got = if scope.production.contains(&target) {
            "prod"
        } else if scope.test_only.contains(&target) {
            "test"
        } else {
            "scan"
        };
        let want = case["want"].as_str().expect("want");
        if got != want && !(want == "scan" && got == "prod") {
            wrong.push(format!("{}: got {got}, want {want}", case["name"]));
        }
    }
    assert!(
        wrong.is_empty(),
        "module-tree layouts resolved wrongly: {wrong:#?}"
    );
}

/// 2026-11-16: the shared Rust lexer's known answers (nested block comments,
/// raw-string prefixes that need a token boundary, the `\x..` and `\u{..}`
/// char escapes), the file-head `#![cfg(test)]` rule and the anchored `cfg`
/// head, on this producer. The tables live once, in the Python producer
/// (`--lexer-cases`), so the mirror cannot drift from them alone.
///
/// This arm fails closed: no python3, no table, no pass.
#[test]
fn the_lexer_and_cfg_heads_answer_every_reading_correctly() {
    use crate::cmd_replacement::rust_source_scope::{
        blank_both, cfg_attr_is_test_only, headed_cfg_test,
    };
    let out = Command::new("python3")
        .arg(repo_root().join("scripts/check_add_decl_ratchet.py"))
        .arg("--lexer-cases")
        .output()
        .expect("python3 must be available; the tables live in the Python producer");
    assert!(out.status.success(), "--lexer-cases failed");
    let tables: serde_json::Value =
        serde_json::from_slice(&out.stdout).expect("the case tables are JSON");
    let text = |v: &serde_json::Value| v.as_str().expect("text").to_string();
    let mut wrong = Vec::new();
    let lexer = tables["lexer"].as_array().expect("lexer cases");
    assert!(
        lexer.len() >= 14,
        "the lexer table collapsed to {}",
        lexer.len()
    );
    for case in lexer {
        let (keep, full) = blank_both(&text(&case["source"]));
        let seen = if case["mode"] == "all" { full } else { keep };
        let lost = case["survive"]
            .as_array()
            .expect("survive")
            .iter()
            .map(text)
            .filter(|s| !seen.contains(s.as_str()));
        let kept = case["vanish"]
            .as_array()
            .expect("vanish")
            .iter()
            .map(text)
            .filter(|s| seen.contains(s.as_str()));
        for s in lost.chain(kept) {
            wrong.push(format!("lexer {}: {s:?} in {seen:?}", case["name"]));
        }
    }
    let heads = tables["file_head"].as_array().expect("file-head cases");
    assert!(
        heads.len() >= 10,
        "the file-head table collapsed to {}",
        heads.len()
    );
    for case in heads {
        let source = text(&case["source"]);
        if Some(headed_cfg_test(&source)) != case["want"].as_bool() {
            wrong.push(format!("file head {source:?}"));
        }
    }
    let attrs = tables["cfg_head"].as_array().expect("cfg-head cases");
    assert!(
        attrs.len() >= 6,
        "the cfg-head table collapsed to {}",
        attrs.len()
    );
    for case in attrs {
        let attr = text(&case["attr"]);
        if Some(cfg_attr_is_test_only(&attr)) != case["want"].as_bool() {
            wrong.push(format!("cfg head {attr:?}"));
        }
    }
    assert!(wrong.is_empty(), "read differently from rustc: {wrong:#?}");
}
