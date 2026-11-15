// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Real-olean `Lean.aliasExtension` decode (imported `export` aliases).
//!
//! Lean persists `export Ns (a b c)` as `Name × Name` pairs in
//! `Lean.aliasExtension`. Before the typed decoder those pairs reached the
//! generic `(Name × DataValue)` reader, which resolved the ALIAS but captured
//! the TARGET as opaque bytes — so every `export`ed short name was
//! unresolvable after `import Init` even though its constant imported and
//! kernel-checked fine. `isTrue` (from `export Decidable (isTrue isFalse
//! decide)`, `Init/Prelude.lean`) is the canonical casualty: Mathlib source
//! uses it unqualified.
//!
//! These tests use the same repository-pinned fixture resolver as the other
//! importer tests, including an explicitly captured toolchain outside elan's
//! default installation directory. Only an unavailable fixture may skip;
//! missing, malformed or incomplete metadata in a selected fixture fails.

use super::parse_module;
use crate::module::{ParsedExtensionEntry, ParsedModule, LEAN_ALIAS_EXTENSION};
use std::path::Path;

/// Decode every `Lean.aliasExtension` pair of a module, asserting that the
/// typed decoder claims all of them (a `Named` leftover would mean the
/// generic reader ran and the target was lost).
fn decode_alias_entries(module: &str) -> Option<Vec<(String, String)>> {
    let lib = crate::pinned_lean_lib_path()?;
    Some(
        decode_alias_file(&lib.join(module))
            .unwrap_or_else(|error| panic!("selected pinned fixture {module}: {error}")),
    )
}

fn decode_alias_file(path: &Path) -> Result<Vec<(String, String)>, String> {
    let bytes = std::fs::read(path).map_err(|error| format!("fixture read failed: {error}"))?;
    let parsed = parse_module(&bytes).map_err(|error| format!("fixture parse failed: {error}"))?;
    alias_entries(&parsed)
}

fn alias_entries(parsed: &ParsedModule) -> Result<Vec<(String, String)>, String> {
    let mut extensions = parsed
        .entries
        .iter()
        .filter(|ext| ext.extension_name == LEAN_ALIAS_EXTENSION);
    let ext = extensions
        .next()
        .ok_or("selected fixture has no aliasExtension")?;
    if extensions.next().is_some() {
        return Err("selected fixture has duplicate aliasExtension snapshots".into());
    }
    if ext.undecoded_entries != 0 {
        return Err("selected aliasExtension has undecoded rows".into());
    }
    ext.entries
        .iter()
        .map(|entry| match entry {
            ParsedExtensionEntry::Alias { alias, target } => Ok((alias.clone(), target.clone())),
            other => Err(format!("aliasExtension entry is not Alias: {other:?}")),
        })
        .collect()
}

#[test]
fn test_prelude_export_aliases_decode_with_their_targets() {
    let Some(entries) = decode_alias_entries("Init/Prelude.olean") else {
        eprintln!("Skipping: repository-pinned Lean fixture unavailable");
        return;
    };
    assert!(
        !entries.is_empty(),
        "Init/Prelude carries `export Decidable (isTrue isFalse decide)`, so its \
         aliasExtension entry array must be non-empty"
    );
    // TEETH: the target must be the real qualified constant, not a truncated
    // or empty name — that is exactly what the generic reader lost.
    for (alias, target) in &entries {
        assert!(!alias.is_empty(), "an alias name must never decode empty");
        assert!(
            !target.is_empty(),
            "alias `{alias}` decoded with an EMPTY target — the Name × Name \
             pair was not read as two names"
        );
    }
    let is_true = entries.iter().find(|(alias, _)| alias == "isTrue");
    assert_eq!(
        is_true.map(|(_, target)| target.as_str()),
        Some("Decidable.isTrue"),
        "`export Decidable (isTrue …)` must decode as isTrue -> Decidable.isTrue; \
         got {is_true:?}"
    );
}

#[test]
fn test_alias_targets_are_qualified_names() {
    let Some(entries) = decode_alias_entries("Init/Prelude.olean") else {
        eprintln!("Skipping: repository-pinned Lean fixture unavailable");
        return;
    };
    // An `export`ed alias is by construction SHORTER than its target (the
    // target carries the namespace the export strips), so a decode that
    // returned the same name on both sides would indicate the reader picked
    // the wrong slot.
    for (alias, target) in &entries {
        assert_ne!(
            alias, target,
            "alias and target decoded identical ({alias}) — the pair's second \
             slot was not read"
        );
    }
}

fn alias_fixture() -> ParsedModule {
    ParsedModule {
        const_names: vec![],
        constants: vec![],
        extra_const_names: vec![],
        imports: vec![],
        entries: vec![crate::module::ParsedExtension {
            extension_name: LEAN_ALIAS_EXTENSION.into(),
            entries: vec![ParsedExtensionEntry::Alias {
                alias: "isTrue".into(),
                target: "Decidable.isTrue".into(),
            }],
            undecoded_entries: 0,
        }],
        clean_payload: None,
    }
}

#[test]
fn test_alias_fixture_projection_keeps_both_names() {
    assert_eq!(
        alias_entries(&alias_fixture()).unwrap(),
        vec![("isTrue".into(), "Decidable.isTrue".into())]
    );
}

#[test]
fn test_selected_alias_fixture_requires_one_extension() {
    let mut fixture = alias_fixture();
    fixture.entries.clear();
    assert!(alias_entries(&fixture)
        .unwrap_err()
        .contains("no aliasExtension"));
    let mut fixture = alias_fixture();
    fixture.entries.push(fixture.entries[0].clone());
    assert!(alias_entries(&fixture).unwrap_err().contains("duplicate"));
}

#[test]
fn test_selected_alias_fixture_refuses_lost_or_wrong_kind_rows() {
    let mut fixture = alias_fixture();
    fixture.entries[0].undecoded_entries = 1;
    assert!(alias_entries(&fixture).unwrap_err().contains("undecoded"));
    fixture.entries[0].undecoded_entries = 0;
    fixture.entries[0]
        .entries
        .push(ParsedExtensionEntry::RawScalar(1));
    assert!(alias_entries(&fixture).unwrap_err().contains("not Alias"));
}

#[test]
fn test_selected_alias_fixture_read_and_parse_errors_are_not_skips() {
    let dir = tempfile::tempdir().unwrap();
    let file = dir.path().join("Missing.olean");
    assert!(decode_alias_file(&file)
        .unwrap_err()
        .contains("read failed"));
    std::fs::write(&file, b"malformed fixture").unwrap();
    assert!(decode_alias_file(&file)
        .unwrap_err()
        .contains("parse failed"));
}
