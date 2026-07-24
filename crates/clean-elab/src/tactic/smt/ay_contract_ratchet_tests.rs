// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::fs;
use std::path::Path;
use syn::visit::{self, Visit};

use crate::test_support::source_scan::{collect_rust_source_files, SourceScanRules};

const LEGACY_AY_BACKEND_PATH: &str = "clean_auto::bridge::ay_backend::";
const LEGACY_AY_BACKEND_SEGMENTS: [&str; 3] = ["clean_auto", "bridge", "ay_backend"];

/// Crate-wide rules for the ay contract ratchet: scan all `src/` and `tests/`
/// Rust files while excluding the ratchet test file itself, which contains
/// intentional legacy-path fixtures.
const AY_CONTRACT_RULES: SourceScanRules<'static> = SourceScanRules {
    excluded_dir_names: &[],
    excluded_dir_suffixes: &[],
    excluded_file_names: &["ay_contract_ratchet_tests.rs"],
    excluded_file_prefixes: &[],
    excluded_file_suffixes: &[],
};

fn path_has_legacy_ay_backend_prefix(path: &syn::Path) -> bool {
    let mut segments = path.segments.iter();
    matches!(
        (segments.next(), segments.next(), segments.next()),
        (Some(a), Some(b), Some(c))
            if a.ident == LEGACY_AY_BACKEND_SEGMENTS[0]
                && b.ident == LEGACY_AY_BACKEND_SEGMENTS[1]
                && c.ident == LEGACY_AY_BACKEND_SEGMENTS[2]
    )
}

fn prefix_has_legacy_ay_backend(prefix: &[String]) -> bool {
    prefix.len() >= LEGACY_AY_BACKEND_SEGMENTS.len()
        && prefix
            .iter()
            .zip(LEGACY_AY_BACKEND_SEGMENTS)
            .all(|(segment, expected)| segment == expected)
}

fn push_use_prefix(prefix: &[String], ident: &syn::Ident) -> Vec<String> {
    let mut next = prefix.to_vec();
    next.push(ident.to_string());
    next
}

fn use_tree_contains_legacy_ay_backend(tree: &syn::UseTree, prefix: &[String]) -> bool {
    if prefix_has_legacy_ay_backend(prefix) {
        return true;
    }

    match tree {
        syn::UseTree::Path(use_path) => {
            let next = push_use_prefix(prefix, &use_path.ident);
            use_tree_contains_legacy_ay_backend(&use_path.tree, &next)
        }
        syn::UseTree::Name(use_name) => {
            let next = push_use_prefix(prefix, &use_name.ident);
            prefix_has_legacy_ay_backend(&next)
        }
        syn::UseTree::Rename(use_rename) => {
            let next = push_use_prefix(prefix, &use_rename.ident);
            prefix_has_legacy_ay_backend(&next)
        }
        syn::UseTree::Glob(_) => prefix_has_legacy_ay_backend(prefix),
        syn::UseTree::Group(use_group) => use_group
            .items
            .iter()
            .any(|item| use_tree_contains_legacy_ay_backend(item, prefix)),
    }
}

struct LegacyAyBackendVisitor {
    found: bool,
}

impl<'ast> Visit<'ast> for LegacyAyBackendVisitor {
    fn visit_item_use(&mut self, item_use: &'ast syn::ItemUse) {
        if use_tree_contains_legacy_ay_backend(&item_use.tree, &[]) {
            self.found = true;
            return;
        }
        visit::visit_item_use(self, item_use);
    }

    fn visit_path(&mut self, path: &'ast syn::Path) {
        if path_has_legacy_ay_backend_prefix(path) {
            self.found = true;
            return;
        }
        visit::visit_path(self, path);
    }
}

fn source_contains_legacy_ay_backend(source: &str) -> bool {
    let file = syn::parse_file(source).expect("clean-elab source should parse for ratchet scan");
    let mut visitor = LegacyAyBackendVisitor { found: false };
    visitor.visit_file(&file);
    visitor.found
}

fn legacy_ay_backend_lines(source: &str) -> Vec<(usize, String)> {
    source
        .lines()
        .enumerate()
        .filter_map(|(line_no, line)| {
            let code = line.split("//").next().unwrap_or("");
            code.contains("ay_backend::")
                .then(|| (line_no + 1, line.trim().to_string()))
        })
        .collect()
}

#[test]
fn test_clean_elab_crate_uses_curated_ay_contract_path() {
    let src_root = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let tests_root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests");
    let mut source_files = collect_rust_source_files(&src_root, &AY_CONTRACT_RULES);
    source_files.extend(collect_rust_source_files(&tests_root, &AY_CONTRACT_RULES));
    assert!(
        !source_files.is_empty(),
        "clean-elab source scan should discover src/ and tests/ files"
    );

    let repo_root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut offenders = Vec::new();

    for path in source_files {
        let source = fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("failed to read {}: {}", path.display(), e));
        let relative = path.strip_prefix(repo_root).unwrap_or(path.as_path());
        if source_contains_legacy_ay_backend(&source) {
            let lines = legacy_ay_backend_lines(&source);
            if lines.is_empty() {
                offenders.push(format!(
                    "{}: legacy `ay_backend` dependency detected",
                    relative.display()
                ));
                continue;
            }
            for (line_no, line) in lines {
                offenders.push(format!("{}:{}: {}", relative.display(), line_no, line));
            }
        }
    }

    assert!(
        offenders.is_empty(),
        "clean-elab source and tests must depend on \
         `clean_auto::bridge::ay_contract::...`, not the legacy backend path:\n{}",
        offenders.join("\n")
    );
}

#[test]
fn test_legacy_ay_backend_detection_catches_direct_path_usage() {
    let source = r#"
fn logic_name() -> &'static str {
    match clean_auto::bridge::ay_backend::AyLogic::QfUf {
        clean_auto::bridge::ay_backend::AyLogic::QfUf => "qfuf",
        _ => "other",
    }
}
"#;

    assert!(
        source_contains_legacy_ay_backend(source),
        "direct legacy backend paths must be detected"
    );
}

#[test]
fn test_legacy_ay_backend_detection_catches_grouped_use_tree() {
    let source = r#"
use clean_auto::{
    bridge::{ay_backend::AyLogic, ay_contract::AyResult},
};
"#;

    assert!(
        source_contains_legacy_ay_backend(source),
        "grouped use trees must not evade the ratchet"
    );
}

#[test]
fn test_legacy_ay_backend_detection_ignores_curated_contract_path() {
    let source = r#"
use clean_auto::{
    bridge::{ay_contract::AyLogic, ay_contract::AyResult},
};

fn logic_name() -> &'static str {
    match clean_auto::bridge::ay_contract::AyLogic::QfUf {
        clean_auto::bridge::ay_contract::AyLogic::QfUf => "qfuf",
        _ => "other",
    }
}
"#;

    assert!(
        !source_contains_legacy_ay_backend(source),
        "curated contract usage must remain allowed"
    );
    assert_eq!(
        legacy_ay_backend_lines(source),
        Vec::<(usize, String)>::new()
    );
    assert!(
        !source.contains(LEGACY_AY_BACKEND_PATH),
        "curated-path fixture should not accidentally include the legacy path"
    );
}
