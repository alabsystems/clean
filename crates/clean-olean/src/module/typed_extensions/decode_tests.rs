// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

const MATCHER_FIXTURE: &[u8] = include_bytes!(
    "../../../../../tests/fixtures/olean/v4.8.0/matcher-metadata/MatcherParity.olean"
);

#[test]
fn lean_v1_matcher_metadata_preserves_all_measured_fields() {
    let region = region(MATCHER_FIXTURE);
    let read = reader(&region);
    let ext = read
        .extension(extension_pointer(
            &region,
            "Lean.Meta.Match.Extension.extension",
        ))
        .unwrap();
    assert_eq!(ext.source_rows, Some(3));
    assert_eq!(ext.undecoded_entries, 0);
    for (suffix, discrs, alts, names) in [
        ("choose.match_1", 1, vec![1, 1, 1], vec![None]),
        (
            "chooseEq.match_1",
            1,
            vec![1, 1, 1],
            vec![Some(Name::from_string("h"))],
        ),
        ("chooseTwo.match_1", 2, vec![1, 1, 1, 1], vec![None, None]),
    ] {
        let wanted = Name::from_string(&format!("MatcherParity.{suffix}"));
        let info = ext
            .entries
            .iter()
            .find_map(|entry| match entry {
                TypedExtensionEntry::Matcher { name, info } if *name == wanted => Some(info),
                _ => None,
            })
            .expect("the oracle lists this exact matcher");
        assert_eq!(info.num_params, 0);
        assert_eq!(info.num_discrs, discrs);
        assert_eq!(info.alt_num_params, alts);
        assert_eq!(info.u_elim_pos, Some(0));
        assert_eq!(info.discr_names, names);
    }
}

#[test]
fn lean_v1_matcher_rows_reject_malformed_shapes_and_unmeasured_layouts() {
    let original = region(MATCHER_FIXTURE);
    let read = reader(&original);
    let ext = extension_pointer(&original, "Lean.Meta.Match.Extension.extension");
    let ext_at = original.ptr_to_offset(ext).unwrap();
    let row = read.array(read.field(ext_at, 1).unwrap()).unwrap()[0];
    let row_at = original.ptr_to_offset(row).unwrap();
    let info = read.field(row_at, 1).unwrap();
    let info_at = original.ptr_to_offset(info).unwrap();
    assert!(read.matcher(row).is_ok());
    for (at, byte, value) in [
        (row_at, 6, 1),
        (row_at, 7, 1),
        (info_at, 6, 4),
        (info_at, 6, 6),
        (info_at, 7, 1),
        (info_at, 4, 40),
    ] {
        let mut changed = MATCHER_FIXTURE.to_vec();
        changed[at + byte] = value;
        assert!(
            reader(&region(&changed)).matcher(row).is_err(),
            "mutation {at}/{byte}/{value}"
        );
    }
    let mut changed = MATCHER_FIXTURE.to_vec();
    changed[info_at + 16..info_at + 24].copy_from_slice(&199_999_u64.to_le_bytes());
    assert!(
        reader(&region(&changed)).matcher(row).is_err(),
        "discriminant extent mismatch"
    );
    let later = Reader {
        layout: TypedModuleLayout::LeanV2,
        ..reader(&original)
    };
    let ext = later.extension(ext).unwrap();
    assert_eq!(ext.undecoded_entries, 3);
    assert!(ext
        .entries
        .iter()
        .all(|row| matches!(row, TypedExtensionEntry::Unmeasured { .. })));
}

#[test]
fn imported_matcher_metadata_never_infers_registration_from_a_name() {
    let fixture = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/olean/v4.8.0/matcher-metadata");
    let core = crate::installed_lean_lib_path("leanprover/lean4:v4.8.0")
        .expect("this measured fixture requires the exact Lean 4.8 standard library");
    let mut env = clean_kernel::Environment::default();
    crate::load_module_with_deps(&mut env, "MatcherParity", &[fixture, core]).unwrap();
    let name = Name::from_string("MatcherParity.choose.match_1");
    let info = env.get_matcher_info(&name).unwrap().clone();
    assert!(env
        .get_matcher_info(&Name::from_string("MatcherParity.ordinary.match_1"))
        .is_none());
    let mut wrong = info.clone();
    wrong.num_params += 100;
    assert!(env.register_matcher_info(name.clone(), wrong).is_err());
    assert_eq!(env.get_matcher_info(&name), Some(&info));
    let mut wrong = info.clone();
    wrong.u_elim_pos = Some(100);
    assert!(env.register_matcher_info(name.clone(), wrong).is_err());
    assert!(env.forget_decl(&name));
    assert!(env.get_matcher_info(&name).is_none());
}

const FIXTURE: &[u8] = include_bytes!(
    "../../../../../tests/fixtures/olean/v4.8.0/instance-metadata/InstanceParity.olean"
);

pub(super) fn region(bytes: &[u8]) -> CompactedRegion<'_> {
    let header = crate::header::OleanHeader::parse(bytes).unwrap();
    CompactedRegion::new(bytes, header.base_addr)
}

pub(super) fn reader<'r, 'a>(region: &'r CompactedRegion<'a>) -> Reader<'r, 'a> {
    Reader {
        region,
        layout: region.typed_module_layout().unwrap(),
        legacy: false,
        remaining_items: Cell::new(MAX_TOTAL_ARRAY_ITEMS),
    }
}

#[test]
fn lean_v1_metadata_registers_only_the_original_classes_and_instances() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/olean/v4.8.0/instance-metadata");
    let mut env = clean_kernel::Environment::default();
    crate::load_module_with_deps(&mut env, "InstanceParity", &[path])
        .expect("the original import-free oracle fixture loads");
    let prefix = Name::anon().str("InstanceParity");
    for class in ["Actual", "Removed"] {
        assert!(env.is_class(&prefix.clone().str(class)));
    }
    assert!(!env.is_class(&prefix.clone().str("Plain")));
    for instance in ["registered.dot", "removed"] {
        assert!(env.is_instance(&prefix.clone().str(instance)));
    }
    for (class, instance, priority) in [
        ("Actual", "registered.dot", 731),
        ("Removed", "removed", 1000),
    ] {
        let found = env
            .get_class_instances(&prefix.clone().str(class))
            .iter()
            .find(|entry| entry.name == prefix.clone().str(instance))
            .expect("the original instance remains associated with its class");
        assert_eq!(found.priority, priority);
    }
    for ordinary in ["plainActual", "plainRemoved", "plainValue"] {
        assert!(!env.is_instance(&prefix.clone().str(ordinary)));
    }
}

pub(super) fn extension_pointer(region: &CompactedRegion<'_>, wanted: &str) -> u64 {
    let read = reader(region);
    let root = region.ptr_to_offset(region.root_ptr().unwrap()).unwrap();
    let extensions = read.array(region.read_u64_at(root + 40).unwrap()).unwrap();
    extensions
        .into_iter()
        .find(|&ptr| {
            let at = region.ptr_to_offset(ptr).unwrap();
            read.name(read.field(at, 0).unwrap()).unwrap() == Name::from_string(wanted)
        })
        .unwrap()
}

#[test]
fn lean_v1_class_and_instance_rows_decode_from_actual_oracle_bytes() {
    let region = region(FIXTURE);
    let read = reader(&region);
    assert_eq!(read.layout, TypedModuleLayout::LeanV1);
    for (name, is_class) in [
        ("Lean.classExtension", true),
        ("Lean.Meta.instanceExtension", false),
    ] {
        let ext = read.extension(extension_pointer(&region, name)).unwrap();
        assert_eq!(ext.source_rows, Some(2));
        assert_eq!(ext.undecoded_entries, 0);
        assert_eq!(ext.entries.len(), 2);
        assert!(ext.entries.iter().all(|row| if is_class {
            matches!(row, TypedExtensionEntry::Class(_))
        } else {
            matches!(row, TypedExtensionEntry::Instance(_))
        }));
    }
}

#[test]
fn lean_v1_class_rows_reject_wrong_tag_extent_and_field_counts() {
    let original = region(FIXTURE);
    let read = reader(&original);
    let ext = extension_pointer(&original, "Lean.classExtension");
    let at = original.ptr_to_offset(ext).unwrap();
    let row = read.array(read.field(at, 1).unwrap()).unwrap()[0];
    let offset = original.ptr_to_offset(row).unwrap();
    assert!(read.class(row).is_ok());
    for (byte, value) in [(7, 1), (6, 1), (6, 3), (6, 4), (4, 16), (4, 32)] {
        let mut bytes = FIXTURE.to_vec();
        bytes[offset + byte] = value;
        let mutant = region(&bytes);
        assert!(
            reader(&mutant).class(row).is_err(),
            "mutation {byte}/{value}"
        );
    }
    let mut mixed = FIXTURE.to_vec();
    let out_params = read.field(offset, 1).unwrap();
    mixed[offset + 4..offset + 6].copy_from_slice(&32u16.to_le_bytes());
    mixed[offset + 6] = 3;
    mixed[offset + 24..offset + 32].copy_from_slice(&out_params.to_le_bytes());
    assert!(
        reader(&region(&mixed)).class(row).is_err(),
        "even a well-shaped three-field row is outside the measured v1 layout"
    );
    let truncated = region(&FIXTURE[..offset + 23]);
    let truncated_read = Reader {
        region: &truncated,
        layout: TypedModuleLayout::LeanV1,
        legacy: false,
        remaining_items: Cell::new(MAX_TOTAL_ARRAY_ITEMS),
    };
    assert!(truncated_read.class(row).is_err());
    let later = Reader {
        layout: TypedModuleLayout::LeanV2,
        ..reader(&original)
    };
    assert!(
        later.class(row).is_err(),
        "the two-field exception is v1-only"
    );
}

#[test]
fn lean_v1_instance_rows_reject_malformed_shape_and_identity() {
    let original = region(FIXTURE);
    let read = reader(&original);
    let ext = extension_pointer(&original, "Lean.Meta.instanceExtension");
    let at = original.ptr_to_offset(ext).unwrap();
    let row = read.array(read.field(at, 1).unwrap()).unwrap()[0];
    let (inner, _) = read.scoped(row).unwrap();
    let offset = original.ptr_to_offset(inner).unwrap();
    assert!(read.instance(row).is_ok());
    for (byte, value) in [(7, 1), (6, 4), (6, 6), (4, 48), (48, 255)] {
        let mut bytes = FIXTURE.to_vec();
        bytes[offset + byte] = value;
        let mutant = region(&bytes);
        assert!(
            reader(&mutant).instance(row).is_err(),
            "mutation {byte}/{value}"
        );
    }
    let mut bytes = FIXTURE.to_vec();
    // A global instance row requires its actual `some Name`, never `none`.
    bytes[offset + 32..offset + 40].copy_from_slice(&1u64.to_le_bytes());
    let missing_name = region(&bytes);
    assert!(reader(&missing_name).instance(row).is_err());
}

#[test]
fn noncomputable_tag_names_are_restored_and_malformed_rows_fail_closed() {
    let fixture = crate::test_support::compiled_fixture_dir("noncomputable_import")
        .join("NoncomputableImport.olean");
    let bytes = std::fs::read(&fixture).unwrap();
    let original = region(&bytes);
    let read = reader(&original);
    let ext_ptr = extension_pointer(&original, "Lean.noncomputableExt");
    let ext = read.extension(ext_ptr).unwrap();
    assert_eq!(ext.source_rows, Some(1));
    assert_eq!(ext.undecoded_entries, 0);
    assert!(
        matches!(ext.entries.as_slice(), [TypedExtensionEntry::Noncomputable { decl }] if decl == &Name::from_string("blocked"))
    );
    let mut env = clean_kernel::Environment::for_lean_replay();
    crate::load_module_with_deps(
        &mut env,
        "NoncomputableImport",
        &[fixture.parent().unwrap().to_path_buf()],
    )
    .unwrap();
    assert!(env.is_noncomputable(&Name::from_string("blocked")));
    assert!(!env.is_noncomputable(&Name::from_string("ordinary")));
    let ext_at = original.ptr_to_offset(ext_ptr).unwrap();
    let array = read.field(ext_at, 1).unwrap();
    let at = original
        .array_elem_offset(
            original.ptr_to_offset(array).unwrap(),
            0,
            "noncomputable row",
        )
        .unwrap();
    let mut mutated = bytes.clone();
    // A tag entry is a declaration identity, never anonymous Lean.box(0).
    mutated[at..at + 8].copy_from_slice(&1u64.to_le_bytes());
    let error = reader(&region(&mutated)).extension(ext_ptr).unwrap_err();
    assert!(error.to_string().contains("noncomputable"), "{error}");
}
