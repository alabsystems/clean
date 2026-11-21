// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::region::CompactedRegion;

const PLAIN: &[u8] =
    include_bytes!("../../../../tests/fixtures/olean/v4.36.0/plain/StablePlain.olean");
const SPLIT: &[u8] =
    include_bytes!("../../../../tests/fixtures/olean/v4.36.0/module-ir/StableFixture/Defs.olean");
const BASE: u64 = 0x10000;

fn writer() -> LeanV2RegionWriter {
    LeanV2RegionWriter::new(&OleanHeader::parse(PLAIN).unwrap(), BASE).unwrap()
}

fn region(bytes: &[u8]) -> CompactedRegion<'_> {
    CompactedRegion::new(bytes, OleanHeader::parse(bytes).unwrap().base_addr)
}

fn word_at(region: &CompactedRegion<'_>, at: usize) -> u64 {
    region.read_u64_at(at).unwrap()
}

fn offset(region: &CompactedRegion<'_>, pointer: u64) -> usize {
    region.ptr_to_offset(pointer).unwrap()
}

fn object_field(region: &CompactedRegion<'_>, object: usize, index: usize) -> usize {
    offset(region, word_at(region, object + WORD + index * WORD))
}

fn root(region: &CompactedRegion<'_>) -> usize {
    offset(region, region.root_ptr().unwrap())
}

fn import_objects(region: &CompactedRegion<'_>) -> (usize, Vec<usize>) {
    let array = object_field(region, root(region), 0);
    let size = word_at(region, array + 8) as usize;
    let objects = (0..size)
        .map(|index| offset(region, word_at(region, array + 24 + WORD * index)))
        .collect();
    (array, objects)
}

#[test]
fn stable_imports_match_official_rows_and_object_encodings() {
    let imports = crate::parse_typed_imports(SPLIT).expect("official split imports");
    assert_eq!(imports.len(), 3);
    let bytes = writer()
        .finish_ordinary_module(&imports, &[], &[], &[], &[])
        .expect("stable v2 ordinary ModuleData");
    assert_eq!(&bytes[..80], &PLAIN[..80]);
    assert_eq!(crate::parse_typed_imports(&bytes).unwrap(), imports);
    assert!(crate::decode_clean_payload(&bytes).unwrap().is_none());

    let written = region(&bytes);
    let plain = region(PLAIN);
    let split = region(SPLIT);
    assert_eq!(
        written.bytes_at(root(&written), 8).unwrap(),
        plain.bytes_at(root(&plain), 8).unwrap()
    );
    assert_eq!(word_at(&written, root(&written) + 48), 0);
    let (written_array, written_rows) = import_objects(&written);
    let (lean_array, lean_rows) = import_objects(&split);
    assert_eq!(
        written.bytes_at(written_array, 24).unwrap(),
        split.bytes_at(lean_array, 24).unwrap()
    );
    for (written_row, lean_row) in written_rows.into_iter().zip(lean_rows) {
        assert_eq!(
            written.bytes_at(written_row, 8).unwrap(),
            split.bytes_at(lean_row, 8).unwrap()
        );
        // Includes all three flags and the zeroed alignment bytes.
        assert_eq!(
            word_at(&written, written_row + 16),
            word_at(&split, lean_row + 16)
        );
        let written_name = object_field(&written, written_row, 0);
        let lean_name = object_field(&split, lean_row, 0);
        assert_eq!(
            written.bytes_at(written_name, 8).unwrap(),
            split.bytes_at(lean_name, 8).unwrap()
        );
        assert_eq!(word_at(&written, written_name + 8), 1);
        assert_eq!(
            word_at(&written, written_name + 24),
            word_at(&split, lean_name + 24)
        );
        let written_string = object_field(&written, written_name, 1);
        let lean_string = object_field(&split, lean_name, 1);
        let length = 32 + word_at(&split, lean_string + 8) as usize;
        assert_eq!(
            written.bytes_at(written_string, length).unwrap(),
            split.bytes_at(lean_string, length).unwrap()
        );
    }
}

#[test]
fn typed_names_and_boxed_naturals_round_trip_without_display_projection() {
    let mut out = writer();
    let name = Name::anon().str("é.part").num(u64::MAX).str("7");
    let name_value = out.write_name(&name).unwrap();
    let natural = BigNat::from_limbs(vec![8, 1]);
    let heap = out.write_nat(&natural).unwrap();
    let boundary = out.write_nat(&BigNat::Small(MAX_SCALAR)).unwrap();
    let next = out.write_nat(&BigNat::Small(MAX_SCALAR + 1)).unwrap();
    assert_eq!(boundary, LeanV2Value::scalar(MAX_SCALAR).unwrap());

    let imports = [TypedImport {
        module_name: Name::anon().str("A.B"),
        flags: TypedImportFlags::LeanV2 {
            import_all: true,
            is_exported: false,
            is_meta: true,
        },
    }];
    let bytes = out
        .finish_ordinary_module(&imports, &[], &[], &[name.clone()], &[])
        .unwrap();
    let region = region(&bytes);
    let extra = object_field(&region, root(&region), 3);
    assert_eq!(word_at(&region, extra + 24), name_value.word);
    assert_eq!(region.read_kernel_name_ptr(name_value.word).unwrap(), name);
    assert_eq!(
        region.read_bignat_value(heap.word).unwrap().limbs(),
        natural.limbs()
    );
    assert_eq!(
        region.read_bignat_value(next.word).unwrap().limbs(),
        &[MAX_SCALAR + 1]
    );
    assert_eq!(crate::parse_typed_imports(&bytes).unwrap(), imports);
}

#[test]
fn wrong_world_legacy_flags_and_foreign_objects_are_refused() {
    let mut header = OleanHeader::parse(PLAIN).unwrap();
    header.flags = 0;
    assert!(LeanV2RegionWriter::new(&header, BASE).is_err());

    let mut first = writer();
    let name = first.write_name(&Name::anon().str("foreign")).unwrap();
    let mut second = writer();
    assert!(second.write_array(&[name]).is_err());
    assert!(second
        .write_imports(&[TypedImport {
            module_name: Name::anon().str("Init"),
            flags: TypedImportFlags::CleanLegacy {
                runtime_only: false
            },
        }])
        .is_err());
}
