// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::tests::{extension_pointer, reader, region};
use super::*;

fn fixture() -> Vec<u8> {
    let path = crate::test_support::compiled_fixture_dir("csimp_import").join("CSimpImport.olean");
    std::fs::read(path).expect("genuine pinned Lean artifact")
}

#[test]
fn csimp_import_retains_global_and_scoped_rows_without_exporting_local_rules() {
    let bytes = fixture();
    let original = region(&bytes);
    let ext = reader(&original)
        .extension(extension_pointer(&original, "Lean.Compiler.CSimp.ext"))
        .expect("measured scoped CSimp metadata");
    assert_eq!(ext.source_rows, Some(2));
    assert_eq!(ext.undecoded_entries, 0);
    for (prefix, namespace) in [("", None), ("Scoped.", Some("Scoped"))] {
        assert!(
            ext.entries.iter().any(|entry| matches!(entry,
                TypedExtensionEntry::CSimp { from, to, theorem, namespace: scope }
                if *from == Name::from_string(&format!("{prefix}slow"))
                    && *to == Name::from_string(&format!("{prefix}fast"))
                    && *theorem == Name::from_string(&format!("{prefix}slow_eq_fast"))
                    && *scope == namespace.map(Name::from_string)
            )),
            "{ext:#?}"
        );
    }
}

#[test]
fn csimp_import_refuses_anonymous_identities_and_malformed_entry_layouts() {
    let bytes = fixture();
    let original = region(&bytes);
    let read = reader(&original);
    let ext = extension_pointer(&original, "Lean.Compiler.CSimp.ext");
    let ext_at = original.ptr_to_offset(ext).unwrap();
    let rows = read.array(read.field(ext_at, 1).unwrap()).unwrap();
    assert_eq!(rows.len(), 2);
    for wrapper in rows {
        let (row, _) = read.scoped(wrapper).unwrap();
        let at = original.ptr_to_offset(row).unwrap();
        for field in 0..3 {
            let mut changed = bytes.clone();
            let offset = at + 8 + field * 8;
            changed[offset..offset + 8].copy_from_slice(&1u64.to_le_bytes());
            assert!(
                reader(&region(&changed)).extension(ext).is_err(),
                "anonymous field {field}"
            );
        }
        let mut changed = bytes.clone();
        changed[at + 6] = 2;
        assert!(
            reader(&region(&changed)).extension(ext).is_err(),
            "short CSimp entry"
        );
    }
}
