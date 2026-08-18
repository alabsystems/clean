// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Strict-mode `lakefile.lean` parsing with skipped-construct accounting
//! (Lean 4 drop-in roadmap, Lake pillar): a Mathlib-style lakefile lists its
//! exact skipped top-level constructs, strict mode rejects a custom `target`
//! declaration, and fully-modeled lakefiles carry zero diagnostics.

use clean_lake::{LakeConfig, LakeError, LakefileParseMode};

const MATHLIB_STYLE: &str = include_str!("fixtures/mathlib-style-lakefile.lean");
const CUSTOM_TARGET: &str = include_str!("fixtures/custom-target-lakefile.lean");

#[test]
fn test_mathlib_style_lakefile_lists_exact_skipped_constructs() {
    let config = LakeConfig::parse(MATHLIB_STYLE).expect("lenient parse should succeed");

    // The declarative subset is parsed as before...
    assert_eq!(config.package.name, "mathlib");
    assert_eq!(config.package.dependencies.len(), 4);
    assert!(config.default_targets.contains(&"Mathlib".to_string()));
    let lib_names: Vec<_> = config.libs.iter().map(|lib| lib.name.as_str()).collect();
    assert!(lib_names.contains(&"Mathlib") && lib_names.contains(&"Cache"));

    // ...and the skipped top-level constructs are accounted for EXACTLY: the
    // two `abbrev` declarations, at their exact source lines. Doc/block
    // comments, indented continuation lines, and the dangling `]` closing the
    // first abbrev's array literal must not appear.
    let expected: Vec<(usize, &str)> = MATHLIB_STYLE
        .lines()
        .enumerate()
        .filter(|(_, line)| line.starts_with("abbrev "))
        .map(|(idx, _)| (idx + 1, "abbrev"))
        .collect();
    assert_eq!(expected.len(), 2, "fixture declares exactly two abbrevs");
    let actual: Vec<(usize, &str)> = config
        .diagnostics
        .iter()
        .map(|skipped| (skipped.line, skipped.token.as_str()))
        .collect();
    assert_eq!(
        actual, expected,
        "diagnostics must list exactly the skipped abbrev declarations"
    );
}

#[test]
fn test_strict_mode_rejects_custom_target_declaration() {
    let result = LakeConfig::parse_with_mode(CUSTOM_TARGET, LakefileParseMode::Strict);
    match result {
        Err(LakeError::UnrecognizedConstructs { count, summary }) => {
            assert_eq!(count, 1, "exactly the target declaration is unrecognized");
            assert!(
                summary.contains("`target`"),
                "summary should name the construct: {summary}"
            );
        }
        other => panic!("expected UnrecognizedConstructs, got: {other:?}"),
    }
}

#[test]
fn test_lenient_mode_records_custom_target_diagnostic() {
    let config = LakeConfig::parse(CUSTOM_TARGET).expect("lenient parse should succeed");
    assert_eq!(config.package.name, "demo");
    assert_eq!(config.libs.len(), 1);
    assert_eq!(
        config.diagnostics.len(),
        1,
        "exactly one skipped construct expected: {:?}",
        config.diagnostics
    );
    assert_eq!(config.diagnostics[0].token, "target");
    assert!(
        config.diagnostics[0]
            .text
            .starts_with("target generateAssets"),
        "diagnostic should carry the construct text: {}",
        config.diagnostics[0].text
    );
}

#[test]
fn test_strict_mode_accepts_mathlib_declarative_subset_minus_abbrevs() {
    // Removing the two abbrev declarations (the only unmodeled constructs)
    // makes the Mathlib-style fixture strict-clean.
    let stripped: String = {
        let mut out = String::new();
        let mut skipping_abbrev = false;
        for line in MATHLIB_STYLE.lines() {
            if line.starts_with("abbrev ") {
                // Skip the abbrev head and any continuation up to a bare `]`.
                skipping_abbrev = line.ends_with("#[");
                continue;
            }
            if skipping_abbrev {
                if line.trim() == "]" {
                    skipping_abbrev = false;
                }
                continue;
            }
            out.push_str(line);
            out.push('\n');
        }
        out
    };
    let config = LakeConfig::parse_with_mode(&stripped, LakefileParseMode::Strict)
        .expect("declarative subset should be strict-clean");
    assert!(config.diagnostics.is_empty());
    assert_eq!(config.package.name, "mathlib");
}
