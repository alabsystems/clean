// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Runtime-declaration refusals: changed borrowed content, the logical
//! import policy, null family counts and rule headers, flag-only nested
//! metadata, and changed value-header shapes.

use super::*;

/// Requires the interned string `"Unary\0"` to occur exactly once in the base
/// part — a property of the whole compiled module the family README measures
/// (1 occurrence, byte offset 328; no other identifier contains `Unary`).
#[test]
fn same_private_bytes_resolve_changed_typed_content_when_borrowed_base_changes() {
    let (mut parts, _) = fixture();
    let before = extract(&parts);
    let offsets: Vec<_> = parts[0]
        .windows(6)
        .enumerate()
        .filter(|(_, v)| *v == b"Unary\0")
        .map(|(i, _)| i)
        .collect();
    assert_eq!(offsets.len(), 1, "actual unique interned base Name string");
    parts[0][offsets[0]] = b'V';
    let after = extract(&parts);
    assert!(after.iter().all(|p| p.error.is_none()));
    assert_eq!(before[2].identity, after[2].identity);
    assert_ne!(before[2].borrowed_prefix, after[2].borrowed_prefix);
    let (_, old) = row(&before[2], &generated());
    let (_, changed) = row(&after[2], &generated());
    assert_ne!(old.type_.as_ref().unwrap(), changed.type_.as_ref().unwrap());
    assert!(changed.dependencies.contains(&Name::anon().str("Vnary")));
    assert!(!changed.dependencies.contains(&Name::anon().str("Unary")));
    assert!(matches!(changed.body, RuntimeBody::Stored(Ok(_))));
}

#[test]
fn existing_logical_import_policy_still_refuses_runtime_artifacts_and_unpinned_admission() {
    let (parts, oracle) = fixture();
    let parsed =
        clean_olean::parse_module_incremental(&parts[0], Some(&parts[1]), &parts[2]).unwrap();
    let private_rows = oracle["parts"][2]["constants"].as_array().unwrap().len();
    assert!(private_rows > 0);
    assert_eq!(parsed.constants.len(), private_rows);
    assert!(parsed
        .constants
        .iter()
        .any(|row| row.name == generated().to_string() && row.value.is_some()));
    // This compatibility projection has lost the distinction between the
    // generated three-component name and the safe quoted two-component twin.
    // Names alone used to hide both rows as compiler artifacts. Refuse the
    // collision; do not manufacture typed identity from a display string.
    let mut projected = Environment::default();
    let error = clean_olean::load_parsed_module_with_import_policy(
        &mut projected,
        &parsed,
        Some("RuntimeProbe".into()),
        clean_olean::OleanImportPolicy::allow_unpinned_legacy(),
    )
    .expect_err("the legacy projection cannot represent both exact Names");
    assert!(
        matches!(error, clean_olean::ImportError::DuplicateDeclaration { .. }),
        "{error}"
    );
    assert_eq!(projected.constants().count(), 0);

    // The authenticated direct reader retains exact Names and uses the final
    // partial record consistently across its Safe exported axiom stubs.
    let mut env = Environment::default();
    let summaries = clean_olean::load_module_with_deps(
        &mut env,
        "RuntimeProbe",
        &[
            fixture_dir(),
            clean_olean::require_pinned_lean_lib_path().unwrap(),
        ],
    )
    .expect("the typed artifact preserves the distinct compiler/user records");
    assert!(summaries.iter().any(|summary| summary
        .skipped_constants
        .iter()
        .any(|row| row.name == generated().to_string()
            && row.reason == "compiler/code-generator artifact (not kernel-checkable)")));
    assert!(
        env.get_const(&generated()).is_none(),
        "partial helper gains no logical authority"
    );
    for name in [
        Name::anon().str("RuntimeProbe").str("count._unsafe_rec"),
        Name::anon()
            .str("RuntimeProbe")
            .str("safe")
            .str("_unsafe_rec"),
    ] {
        assert!(
            env.get_const(&name)
                .is_some_and(|constant| constant.value.is_some()),
            "{name}"
        );
        assert!(!env.is_unsafe(&name) && !env.is_partial(&name));
    }
    let dir = fixture_dir();
    let mut fresh = Environment::default();
    assert!(clean_olean::load_olean_file_with_import_policy(
        &mut fresh,
        dir.join("RuntimeProbe.olean"),
        clean_olean::OleanImportPolicy::reject_unpinned_external()
    )
    .is_err());
    assert_eq!(fresh.constants().count(), 0);
}

#[test]
fn null_family_nats_and_recursor_rule_headers_refuse_per_row_not_as_zero() {
    let (original, _) = fixture();
    let before = extract(&original);
    assert!(before[2].source_row_count.is_some());
    for (name, offset) in [
        (Name::anon().str("Unary"), 16),
        (Name::anon().str("Unary").str("succ"), 40),
        (Name::anon().str("Unary").str("rec"), 40),
    ] {
        let (index, _) = row(&before[2], &name);
        let mut parts = original.clone();
        let at = val(&parts, 2, index) + offset;
        write(&mut parts, at, 0);
        let after = extract(&parts);
        assert_eq!(after[2].source_row_count, before[2].source_row_count);
        assert!(after[2].rows[index].declaration.is_err(), "{name}");
        assert!(row(&after[2], &generated()).1.type_.is_ok());
    }
    let (index, _) = row(&before[2], &Name::anon().str("Unary").str("rec"));
    for mutation in 0..3 {
        let mut parts = original.clone();
        let list = read(&parts, val(&parts, 2, index) + 56);
        let rule = read(&parts, list + 8);
        match mutation {
            0 => write(&mut parts, rule + 16, 0),
            1 => {
                let header = read(&parts, list);
                write(&mut parts, list, header | 1);
            }
            _ => {
                let header = read(&parts, rule);
                write(&mut parts, rule, header ^ (1 << 32));
            }
        }
        let after = extract(&parts);
        assert_eq!(after[2].rows.len(), before[2].rows.len());
        assert!(
            after[2].rows[index].declaration.is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn legacy_flag_only_nested_metadata_is_explicitly_incomplete() {
    let (mut parts, _) = fixture();
    let before = extract(&parts);
    let (index, _) = row(&before[0], &Name::anon().str("Unary"));
    let at = val(&parts, 0, index);
    let header = read(&parts, at);
    // Simulate only the documented old flag-only InductiveVal payload ABI;
    // this is a raw-field control, not an authentic old-toolchain fixture.
    write(
        &mut parts,
        at,
        (header & 0xff00_0000_ffff_ffff) | (5 << 48) | (56 << 32),
    );
    let booleans = read(&parts, at + 56) & 0x00ff_ffff;
    write(&mut parts, at + 48, booleans | (1 << 24));
    let after = extract(&parts);
    let (_, d) = row(&after[0], &Name::anon().str("Unary"));
    assert!(matches!(
        d.family,
        RuntimeFamily::Inductive {
            num_nested: None,
            is_nested: true,
            ..
        }
    ));
    assert!(!d.represented_fields_complete);
    assert!(d
        .issues
        .iter()
        .any(|issue| issue.contains("exact nested count")));
}

/// The kind population is derived from the oracle's `kind` fields over all
/// three parts, not typed. The lost original asserted 6; every v4.30.0-rc2
/// output of this shape has 7, because the module system forces an `axiom`
/// stub per non-exposed body, `partial def` forces an `opaque`, and
/// `Unary.brecOn.eq` is a `theorem` minted beside `brecOn` whenever `PUnit` and
/// `Prod` are in scope (family README, "Literals that do NOT hold").
#[test]
fn each_actual_declaration_kind_refuses_changed_value_header_shape() {
    let (original, oracle) = fixture();
    let before = extract(&original);
    let expected: BTreeSet<&str> = oracle["parts"]
        .as_array()
        .unwrap()
        .iter()
        .flat_map(|part| part["constants"].as_array().unwrap())
        .map(|constant| constant["kind"].as_str().unwrap())
        .collect();
    let mut kinds = BTreeSet::new();
    for part in 0..3 {
        for row in &before[part].rows {
            let d = row.declaration.as_ref().unwrap();
            if !kinds.insert(kind_label(&d.kind)) {
                continue;
            }
            let mut parts = original.clone();
            let at = val(&parts, part, row.index);
            let header = read(&parts, at);
            write(&mut parts, at, header ^ (1 << 32));
            let after = extract(&parts);
            assert_eq!(after[part].source_row_count, before[part].source_row_count);
            assert!(
                after[part].rows[row.index].declaration.is_err(),
                "{:?}",
                d.kind
            );
        }
    }
    assert!(kinds.len() > 1, "more than one kind was exercised");
    assert_eq!(kinds, expected, "full actual fixture kind population");
}
