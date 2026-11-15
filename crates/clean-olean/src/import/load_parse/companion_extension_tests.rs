// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Actual upstream part snapshots and adversarial byte mutations. These tests
//! measure metadata transport through the existing assumed-environment loader,
//! not dependency-closed admission, scoped activation, or simp proof fidelity.
use super::*;
use crate::import::load_register::load_part_direct_with_cache;
use crate::import::ExprInternCache;
use crate::module::typed_extensions::TypedExtensionEntry;
use crate::test_support::{compiled_fixture_dir, run_oracle};
use clean_kernel::env::Environment;
use serde_json::Value;
use std::sync::OnceLock;

/// The `companion_probe` family (`tests/fixtures/lean/v4.30.0-rc2/companion_probe/
/// README.md`) compiled by the pinned Lean on first use — the module-system
/// triple `CompanionProbe.olean{,.server,.private}` — and the independent
/// upstream oracle's reading of the same three files (`oracle/DumpOlean.lean`,
/// raw mode, base → server → private). Read once per process. Every
/// whole-module census a test below compares against (extensions per part,
/// rows per part, constants per part, decoded rows per part) is derived from
/// that oracle or from an unmutated parse of the same bytes; the lost
/// original's literals — `(22, 76, 17) / (24, 90, 17) / (26, 106, 28)`, `26`,
/// `22` — are not reproducible by authoring and are gone. Measured 2026-09-15
/// with `lean --run DumpOlean.lean` over the family compiled by the README
/// recipe: `(entries, Σ count, constants)` = `(20, 47, 13) / (22, 59, 13) /
/// (24, 66, 19)`, decoded rows `5 / 5 / 7` — quoted so a drift can be
/// recognised, never asserted. Fails closed when the toolchain is absent.
fn fixture() -> ([Vec<u8>; 3], Value) {
    static FIXTURE: OnceLock<([Vec<u8>; 3], Value)> = OnceLock::new();
    FIXTURE
        .get_or_init(|| {
            let root = compiled_fixture_dir("companion_probe");
            let paths = ["", ".server", ".private"]
                .map(|suffix| root.join(format!("CompanionProbe.olean{suffix}")));
            let parts = paths
                .each_ref()
                .map(|path| std::fs::read(path).expect("pinned-Lean compiled CompanionProbe part"));
            let args = paths
                .each_ref()
                .map(|path| path.to_str().expect("utf-8 fixture path"));
            (parts, run_oracle(&args))
        })
        .clone()
}

fn parse(parts: &[Vec<u8>; 3], index: usize) -> OleanResult<LoadModule> {
    match index {
        0 => parse_load_module(parts[0].clone()),
        1 => parse_load_module_incremental(&parts[0], None, parts[1].clone()),
        2 => parse_load_module_incremental(&parts[0], Some(&parts[1]), parts[2].clone()),
        _ => panic!("invalid test part"),
    }
}

fn name(value: &Value) -> Name {
    value
        .as_array()
        .unwrap()
        .iter()
        .fold(Name::anon(), |name, part| {
            match part["kind"].as_str().unwrap() {
                "str" => name.str(part["value"].as_str().unwrap()),
                "num" => name.num(part["value"].as_u64().unwrap()),
                other => panic!("unexpected oracle Name segment {other}"),
            }
        })
}

fn known(row: &TypedExtensionEntry) -> Option<(&'static str, Name)> {
    match row {
        TypedExtensionEntry::Alias { alias, .. } => Some(("alias", alias.clone())),
        TypedExtensionEntry::Class(row) => Some(("class", row.name.clone())),
        TypedExtensionEntry::Instance(row) => Some(("instance", row.instance_name.clone())),
        TypedExtensionEntry::Simp(row) => Some(("theorem", row.lemma_name.clone())),
        TypedExtensionEntry::Unmeasured { .. } => None,
        // `Lean.structureExt` rows decode too, but the oracle compares the
        // four extensions above only; they are outside this snapshot.
        TypedExtensionEntry::Structure(_)
        | TypedExtensionEntry::Matcher { .. }
        | TypedExtensionEntry::Noncomputable { .. } => None,
        other => panic!("unexpected modern fallback: {other:?}"),
    }
}

fn oracle_known(row: &Value) -> Option<(&str, Name)> {
    let row = row.get("value").unwrap_or(row);
    let kind = row.get("kind")?.as_str().unwrap();
    Some((
        kind,
        name(&row[if kind == "alias" { "alias" } else { "name" }]),
    ))
}

fn word(bytes: &[u8], offset: usize) -> u64 {
    u64::from_le_bytes(bytes[offset..offset + 8].try_into().unwrap())
}

fn root_offset(bytes: &[u8]) -> usize {
    usize::try_from(word(bytes, 88) - word(bytes, 80)).unwrap()
}

#[test]
fn actual_all_three_extension_snapshots_match_independent_upstream_rows() {
    let (parts, oracle) = fixture();
    for index in 0..3 {
        let module = parse(&parts, index).unwrap();
        let part = &oracle["parts"][index];
        let expected = part["entries"].as_array().unwrap();
        assert!(!expected.is_empty(), "part {index} has upstream extensions");
        assert_eq!(
            module.constants.len(),
            part["constants"].as_array().unwrap().len(),
            "part {index}"
        );
        assert_eq!(module.entries.len(), expected.len(), "part {index}");
        assert_eq!(
            module
                .entries
                .iter()
                .map(|row| row.source_rows.unwrap())
                .sum::<usize>(),
            expected
                .iter()
                .map(|entry| entry["count"].as_u64().unwrap() as usize)
                .sum::<usize>(),
            "part {index}"
        );
        for (actual, expected) in module.entries.iter().zip(expected) {
            assert_eq!(actual.extension_name, name(&expected["name"]));
            assert_eq!(
                actual.source_rows,
                Some(expected["count"].as_u64().unwrap() as usize)
            );
            let actual: Vec<_> = actual.entries.iter().filter_map(known).collect();
            let expected: Vec<_> = expected["rows"]
                .as_array()
                .unwrap()
                .iter()
                .filter_map(oracle_known)
                .collect();
            assert_eq!(actual, expected, "part {index}");
        }
    }
}

/// The number of rows Clean must recognise per part is the number of rows the
/// oracle decoded (the same four extensions, `oracle_known`), not a literal.
#[test]
fn actual_unknown_companion_rows_keep_positions_and_full_population() {
    let (parts, oracle) = fixture();
    for index in 0..3 {
        let decoded = oracle["parts"][index]["entries"]
            .as_array()
            .unwrap()
            .iter()
            .flat_map(|entry| entry["rows"].as_array().unwrap())
            .filter(|row| oracle_known(row).is_some())
            .count();
        assert!(
            decoded > 0,
            "part {index}: the oracle decodes at least one row"
        );
        let module = parse(&parts, index).unwrap();
        assert!(
            !module.entries.is_empty(),
            "part {index} must not be discarded"
        );
        let mut recognized = 0;
        for extension in module.entries {
            assert_eq!(extension.source_rows, Some(extension.entries.len()));
            let mut unknown = 0;
            for (position, row) in extension.entries.iter().enumerate() {
                if let TypedExtensionEntry::Unmeasured { index, reason } = row {
                    assert_eq!(*index, position);
                    assert!(!reason.is_empty());
                    unknown += 1;
                } else if known(row).is_some() {
                    // Counted against the oracle's four extensions only; a
                    // decoded `structureExt` row is neither unknown nor one
                    // of the oracle's.
                    recognized += 1;
                }
            }
            assert_eq!(unknown, extension.undecoded_entries);
        }
        assert_eq!(recognized, decoded, "part {index}");
    }
}

/// Every load below is a part of the one module `CompanionProbe` (the
/// loader binds `M._server` / `M._private` to `M` the same way): parts of one
/// artifact may repeat its declarations; different artifacts may not.
fn artifact() -> Option<String> {
    Some("CompanionProbe".to_string())
}

fn registry(env: &Environment) -> Vec<(Name, Vec<(Name, u32)>)> {
    [
        Name::anon().str("CompanionProbe").str("public.class"),
        Name::anon()
            .str("_private")
            .str("CompanionProbe")
            .num(0)
            .str("CompanionProbe")
            .str("private.class"),
    ]
    .into_iter()
    .map(|class| {
        let entries = env
            .get_class_instances(&class)
            .iter()
            .map(|row| (row.name.clone(), row.priority))
            .collect();
        (class, entries)
    })
    .collect()
}

/// Compiled with `--root .`, so the main module is `CompanionProbe` and the
/// private names mangle to `_private.CompanionProbe.0.CompanionProbe.*`.
#[test]
fn actual_private_metadata_registers_without_duplicate_public_targets() {
    let (parts, _) = fixture();
    let mut env = Environment::new();
    let mut cache = ExprInternCache::with_capacity(128);
    for index in 0..3 {
        let module = parse(&parts, index).unwrap();
        let summary = load_part_direct_with_cache(
            &mut env,
            &module,
            Some(format!("CompanionProbe.part{index}")),
            artifact(),
            &mut cache,
        )
        .unwrap();
        assert_eq!(summary.extension_accounting.len(), module.entries.len());
        for row in &summary.extension_accounting {
            assert_eq!(row.source_rows, Some(row.decoded_rows + row.undecoded_rows));
        }
        assert_eq!(
            summary.extension_undecoded_entries,
            summary
                .extension_accounting
                .iter()
                .map(|row| row.undecoded_rows + row.unresolved_targets)
                .sum::<usize>()
        );
    }
    let public = Name::anon().str("CompanionProbe");
    let private = Name::anon()
        .str("_private")
        .str("CompanionProbe")
        .num(0)
        .str("CompanionProbe");
    for (prefix, visibility) in [(public.clone(), "public"), (private, "private")] {
        let class = prefix.clone().str(format!("{visibility}.class"));
        let instance = prefix.clone().str(format!("{visibility}.instance"));
        let lemma = prefix.str(format!("{visibility}.lemma"));
        assert!(env.is_class(&class));
        assert_eq!(
            env.get_class_instances(&class)
                .iter()
                .filter(|row| row.name == instance && row.priority == 1000)
                .count(),
            1
        );
        assert!(env.is_simp_lemma(&lemma), "exact typed lemma {lemma:?}");
    }
    assert_eq!(
        env.get_export_alias(&public.clone().str("target.dot")),
        Some(&public.str("PublicExports").str("target.dot"))
    );
    let before = (
        registry(&env),
        env.simp_lemma_count(),
        env.export_alias_count(),
    );
    for index in 0..3 {
        let module = parse(&parts, index).unwrap();
        load_part_direct_with_cache(
            &mut env,
            &module,
            Some(format!("repeated.part{index}")),
            artifact(),
            &mut cache,
        )
        .unwrap();
    }
    assert_eq!(
        before,
        (
            registry(&env),
            env.simp_lemma_count(),
            env.export_alias_count()
        )
    );
}

#[test]
fn actual_companion_bad_extension_array_is_not_silently_omitted() {
    let (original, _) = fixture();
    for index in [1, 2] {
        let offset = root_offset(&original[index]) + 40;
        for pointer in [1, u64::MAX - 7, word(&original[index], 80) + 8] {
            let mut changed = original.clone();
            changed[index][offset..offset + 8].copy_from_slice(&pointer.to_le_bytes());
            assert!(
                parse(&changed, index).is_err(),
                "part {index}, pointer {pointer}"
            );
        }
    }
}

/// The private part's `Lean.Meta.instanceExtension` carries two rows; the
/// second (the `private instance`) lives in the private region because the
/// extension exports a private name only at `OLeanLevel.private`, while the
/// first is a borrowed base object (family README, "The private instance row").
/// The extension count after the mutation is the unmutated parse's, not a literal.
#[test]
fn actual_companion_malformed_row_keeps_its_slot_and_other_rows() {
    let (original, _) = fixture();
    let private = parse(&original, 2).unwrap();
    let region = private.region();
    let root = word(&original[2], 88);
    let array = region
        .read_u64_at(region.ptr_to_offset(root).unwrap() + 40)
        .unwrap();
    let array = region.ptr_to_offset(array).unwrap();
    let mut chosen = None;
    for (index, entry) in private.entries.iter().enumerate() {
        if entry.extension_name == Name::from_string("Lean.Meta.instanceExtension") {
            let extension = region.read_u64_at(array + 24 + index * 8).unwrap();
            let rows = region
                .read_u64_at(region.ptr_to_offset(extension).unwrap() + 16)
                .unwrap();
            let second_row = region
                .read_u64_at(region.ptr_to_offset(rows).unwrap() + 32)
                .unwrap();
            chosen = Some((index, second_row));
        }
    }
    let (index, row) = chosen.expect("actual private instance row");
    let offset =
        usize::try_from(row - word(&original[2], 80)).expect("private row is in private part");
    let mut changed = original;
    changed[2][offset + 7] = 255;
    let changed = parse(&changed, 2).unwrap();
    assert_eq!(changed.entries.len(), private.entries.len());
    let entries = &changed.entries[index];
    assert_eq!(entries.source_rows, Some(2));
    assert_eq!(entries.undecoded_entries, 1);
    assert!(matches!(
        &entries.entries[0],
        TypedExtensionEntry::Instance(_)
    ));
    assert!(matches!(
        &entries.entries[1],
        TypedExtensionEntry::Unmeasured { index: 1, .. }
    ));
}

/// A server/private part whose root word is redirected at the base root sees
/// exactly the base part's extensions, so the accounting length is the base
/// parse's `entries.len()`, not a literal.
#[test]
fn borrowed_base_root_preserves_snapshot_without_doubling_registries() {
    let (original, _) = fixture();
    let mut parts = original.clone();
    for part in &mut parts[1..] {
        part.truncate(96);
        part[88..96].copy_from_slice(&original[0][88..96]);
    }
    let base = parse(&parts, 0).unwrap();
    let mut env = Environment::new();
    let mut cache = ExprInternCache::with_capacity(128);
    load_part_direct_with_cache(&mut env, &base, Some("base".into()), artifact(), &mut cache)
        .unwrap();
    let before = (
        registry(&env),
        env.simp_lemma_count(),
        env.export_alias_count(),
    );
    for index in [1, 2] {
        let module = parse(&parts, index).unwrap();
        assert_eq!(
            format!("{:?}", base.entries),
            format!("{:?}", module.entries)
        );
        let summary = load_part_direct_with_cache(
            &mut env,
            &module,
            Some(format!("borrowed{index}")),
            artifact(),
            &mut cache,
        )
        .unwrap();
        assert!(!base.entries.is_empty());
        assert_eq!(summary.extension_accounting.len(), base.entries.len());
        assert_eq!(
            before,
            (
                registry(&env),
                env.simp_lemma_count(),
                env.export_alias_count()
            )
        );
    }
}

#[test]
fn borrowed_roots_require_captured_objects_not_zero_filled_gaps() {
    let (original, _) = fixture();
    let end = word(&original[0], 80) + original[0].len() as u64;
    for index in [1, 2] {
        let mut parts = original.clone();
        parts[index][88..96].copy_from_slice(&(end + 8).to_le_bytes());
        assert!(parse(&parts, index).is_err());
    }
    // Make the dependency explicit rather than assuming every actual private
    // snapshot happens to reference server-owned objects.
    let mut borrowed = original.clone();
    borrowed[2][88..96].copy_from_slice(&original[1][88..96]);
    assert!(
        parse(&borrowed, 2).is_ok(),
        "captured authentic server root"
    );
    assert!(
        parse_load_module_incremental(&borrowed[0], None, borrowed[2].clone()).is_err(),
        "borrowed server root requires the actual server region"
    );
}
