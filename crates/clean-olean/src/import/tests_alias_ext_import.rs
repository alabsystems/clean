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
//! These tests pin the decode against the pinned v4.30.0-rc2 toolchain and
//! skip (with a message) when it is absent.

use super::parse_module;
use crate::module::{ParsedExtensionEntry, LEAN_ALIAS_EXTENSION};
use std::path::PathBuf;

const PINNED_TOOLCHAIN: &str = "leanprover--lean4---v4.30.0-rc2";

fn v4_30_lib_path() -> Option<PathBuf> {
    let home = std::env::var("HOME").ok()?;
    let lib = PathBuf::from(home)
        .join(".elan/toolchains")
        .join(PINNED_TOOLCHAIN)
        .join("lib/lean");
    lib.join("Init.olean").is_file().then_some(lib)
}

/// Decode every `Lean.aliasExtension` pair of a module, asserting that the
/// typed decoder claims all of them (a `Named` leftover would mean the
/// generic reader ran and the target was lost).
fn decode_alias_entries(module: &str) -> Option<Vec<(String, String)>> {
    let lib = v4_30_lib_path()?;
    let bytes = std::fs::read(lib.join(module)).ok()?;
    let parsed = parse_module(&bytes).unwrap_or_else(|e| panic!("{module} should parse: {e}"));
    let ext = parsed
        .entries
        .iter()
        .find(|ext| ext.extension_name == LEAN_ALIAS_EXTENSION)?;
    Some(
        ext.entries
            .iter()
            .map(|entry| match entry {
                ParsedExtensionEntry::Alias { alias, target } => (alias.clone(), target.clone()),
                other => panic!("aliasExtension should decode every entry as Alias, got {other:?}"),
            })
            .collect(),
    )
}

#[test]
fn test_prelude_export_aliases_decode_with_their_targets() {
    let Some(entries) = decode_alias_entries("Init/Prelude.olean") else {
        eprintln!("Skipping: {PINNED_TOOLCHAIN} not installed (or no aliasExtension in Prelude)");
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
        eprintln!("Skipping: {PINNED_TOOLCHAIN} not installed");
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
