// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Raw ABI controls, not declaration admission or a whole-module validator.
use super::*;

const BASE: u64 = 0x10000;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Format {
    Modern,
    Legacy,
}

struct Raw {
    bytes: Vec<u8>,
    root: u64,
    format: Format,
}
impl Raw {
    fn new(format: Format) -> Self {
        let mut bytes = vec![0; if format == Format::Modern { 96 } else { 64 }];
        bytes[..5].copy_from_slice(b"olean");
        let root_slot = if format == Format::Modern {
            bytes[5] = 2;
            bytes[6] = 1;
            bytes[7..17].copy_from_slice(b"4.30.0-rc2");
            bytes[40..80].fill(b'a');
            bytes[80..88].copy_from_slice(&BASE.to_le_bytes());
            88
        } else {
            bytes[5] = 1;
            bytes[6..46].fill(b'a');
            bytes[48..56].copy_from_slice(&BASE.to_le_bytes());
            56
        };
        let mut raw = Self {
            bytes,
            root: 0,
            format,
        };
        raw.root = raw.object(
            0,
            &[1; 5],
            if format == Format::Modern { 56 } else { 0 },
            if format == Format::Modern {
                &[0; 8]
            } else {
                &[]
            },
        );
        raw.bytes[root_slot..root_slot + 8].copy_from_slice(&raw.root.to_le_bytes());
        raw
    }
    fn object(&mut self, tag: u8, fields: &[u64], size: u16, scalar: &[u8]) -> u64 {
        while !self.bytes.len().is_multiple_of(8) {
            self.bytes.push(0);
        }
        let pointer = BASE + self.bytes.len() as u64;
        self.bytes.extend_from_slice(&[0; 4]);
        self.bytes.extend_from_slice(&size.to_le_bytes());
        self.bytes.extend_from_slice(&[fields.len() as u8, tag]);
        for field in fields {
            self.bytes.extend_from_slice(&field.to_le_bytes());
        }
        self.bytes.extend_from_slice(scalar);
        pointer
    }
    fn word(&mut self, pointer: u64, relative: usize, value: u64) {
        let start = (pointer - BASE) as usize + relative;
        self.bytes[start..start + 8].copy_from_slice(&value.to_le_bytes());
    }
    fn byte(&mut self, pointer: u64, relative: usize, value: u8) {
        self.bytes[(pointer - BASE) as usize + relative] = value;
    }
    fn string(&mut self, text: &str) -> u64 {
        let pointer = self.object(tags::STRING, &[], 0, &[]);
        for word in [
            text.len() as u64 + 1,
            text.len() as u64 + 1,
            text.chars().count() as u64,
        ] {
            self.bytes.extend_from_slice(&word.to_le_bytes());
        }
        self.bytes.extend_from_slice(text.as_bytes());
        self.bytes.push(0);
        pointer
    }
    fn name(&mut self, tag: u8, parent: u64, value: u64) -> u64 {
        self.object(
            tag,
            &[parent, value],
            if self.format == Format::Modern { 32 } else { 0 },
            if self.format == Format::Modern {
                &[0; 8]
            } else {
                &[]
            },
        )
    }
    fn str(&mut self, parent: u64, text: &str) -> u64 {
        let string = self.string(text);
        self.name(1, parent, string)
    }
    fn num(&mut self, parent: u64, n: u64) -> u64 {
        let value = if self.format == Format::Legacy {
            n
        } else if n <= u64::MAX >> 1 {
            (n << 1) | 1
        } else {
            self.mpz(&[n], 1)
        };
        self.name(2, parent, value)
    }
    fn mpz(&mut self, limbs: &[u64], size: i32) -> u64 {
        let pointer = self.object(tags::MPZ, &[], (24 + 8 * limbs.len()) as u16, &[]);
        self.bytes
            .extend_from_slice(&(limbs.len() as i32).to_le_bytes());
        self.bytes.extend_from_slice(&size.to_le_bytes());
        self.bytes.extend_from_slice(&(pointer + 24).to_le_bytes());
        for limb in limbs {
            self.bytes.extend_from_slice(&limb.to_le_bytes());
        }
        pointer
    }
    fn level(&mut self, tag: u8, fields: &[u64]) -> u64 {
        self.object(
            tag,
            fields,
            if self.format == Format::Modern {
                (16 + fields.len() * 8) as u16
            } else {
                0
            },
            if self.format == Format::Modern {
                &[0; 8]
            } else {
                &[]
            },
        )
    }
    fn list(&mut self, items: &[u64]) -> u64 {
        items.iter().rev().fold(1, |tail, head| {
            self.object(
                1,
                &[*head, tail],
                if self.format == Format::Modern { 24 } else { 0 },
                &[],
            )
        })
    }
    fn region(&self) -> CompactedRegion<'_> {
        CompactedRegion::new(&self.bytes, BASE)
    }
}

// Lean v4.13 has no isModule scalar in ModuleData: five object fields,
// cs_sz=48. Its Name and Level objects still carry their cached data words.
fn lean_v1_raw() -> Raw {
    let mut raw = Raw::new(Format::Modern);
    raw.bytes[5] = 1;
    raw.bytes[6..46].fill(b'a');
    raw.bytes[46..48].fill(0);
    raw.bytes[48..56].copy_from_slice(&BASE.to_le_bytes());
    raw.bytes[56..64].copy_from_slice(&raw.root.to_le_bytes());
    let root = (raw.root - BASE) as usize;
    raw.bytes[root + 4..root + 6].copy_from_slice(&48u16.to_le_bytes());
    raw
}

#[test]
fn lean_v1_names_levels_and_small_nats_preserve_structural_identity() {
    let mut raw = lean_v1_raw();
    let quoted = raw.str(1, "Alias.value");
    let prefix = raw.str(1, "Alias");
    let hierarchical = raw.str(prefix, "value");
    let numeric = raw.num(1, 7);
    let string = raw.str(1, "7");
    let universe = raw.str(1, "u.dot");
    let param = raw.level(4, &[universe]);
    let succ = raw.level(1, &[param]);
    let region = raw.region();
    assert_eq!(
        region.read_kernel_name_ptr(quoted).unwrap(),
        Name::anon().str("Alias.value")
    );
    assert_eq!(
        region.read_kernel_name_ptr(hierarchical).unwrap(),
        Name::anon().str("Alias").str("value")
    );
    assert_eq!(
        region.read_kernel_name_ptr(numeric).unwrap(),
        Name::anon().num(7)
    );
    assert_eq!(
        region.read_kernel_name_ptr(string).unwrap(),
        Name::anon().str("7")
    );
    assert_eq!(
        region.read_kernel_level_ptr(succ).unwrap(),
        Level::succ(Level::param(Name::anon().str("u.dot")))
    );
    assert_eq!(region.read_kernel_nat_u64(15).unwrap(), 7);
}

#[test]
fn lean_v1_heap_nat_remains_unmeasured_not_raw_word_or_low_limb() {
    let mut raw = lean_v1_raw();
    let numeric = raw.num(1, 1u64 << 63);
    let value = u64::from_le_bytes(
        raw.bytes[(numeric - BASE) as usize + 16..(numeric - BASE) as usize + 24]
            .try_into()
            .unwrap(),
    );
    assert!(raw.region().read_kernel_nat_u64(value).is_err());
    assert!(raw.region().read_kernel_name_ptr(numeric).is_err());
}

#[test]
fn lean_v1_real_files_keep_complete_constant_populations() {
    for (file, expected) in [("Minimal", 5), ("Inductive", 25), ("Structure", 18)] {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/fixtures/olean/v4.13.0/custom")
            .join(format!("{file}.olean"));
        let mut env = clean_kernel::env::Environment::default();
        let summary = crate::load_olean_file_with_import_policy(
            &mut env,
            &path,
            crate::OleanImportPolicy::new(crate::UnpinnedOleanImportPolicy::Allow),
        )
        .expect("actual checked-in v4.13 file must load through the direct importer");
        // The public loader intentionally declines compiler artifacts. Keep
        // those exact rows in the denominator instead of requiring admission.
        assert_eq!(
            summary.added_constants + summary.skipped_constants.len(),
            expected,
            "{file}: {summary:?}"
        );
        assert_eq!(summary.duplicate_constants, 0, "{file}");
        assert_eq!(env.constants().count(), summary.added_constants, "{file}");
        let bytes = std::fs::read(&path).unwrap();
        let header = crate::parse_header(&bytes).unwrap();
        let region = CompactedRegion::new(&bytes, header.base_addr);
        let root = region.ptr_to_offset(region.root_ptr().unwrap()).unwrap();
        let array = region
            .ptr_to_offset(region.read_u64_at(root + 16).unwrap())
            .unwrap();
        let count = region.read_usize_at(array + 8, "real raw names").unwrap();
        assert_eq!(count, expected);
        let raw: Vec<Name> = (0..count)
            .map(|i| {
                let slot = region
                    .array_elem_offset(array, i, "real raw names")
                    .unwrap();
                region
                    .read_kernel_name_ptr(region.read_u64_at(slot).unwrap())
                    .unwrap()
            })
            .collect();
        let mut accounted: BTreeSet<Name> = env.constants().map(|c| c.name.clone()).collect();
        for skipped in &summary.skipped_constants {
            assert_eq!(
                skipped.reason,
                "compiler/code-generator artifact (not kernel-checkable)"
            );
            let candidates: Vec<_> = raw
                .iter()
                .filter(|n| n.to_string() == skipped.name)
                .collect();
            assert_eq!(
                candidates.len(),
                1,
                "display-only skipped identity must be unambiguous in this fixture"
            );
            assert!(
                accounted.insert(candidates[0].clone()),
                "duplicate skipped row"
            );
        }
        assert_eq!(accounted, raw.into_iter().collect());
    }
}

#[test]
fn lean_v1_real_envelope_near_twins_refuse_without_fallback() {
    let original = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tests/fixtures/olean/v4.13.0/custom/Inductive.olean"
    ));
    let base = u64::from_le_bytes(original[48..56].try_into().unwrap());
    let root = u64::from_le_bytes(original[56..64].try_into().unwrap());
    let offset = (root - base) as usize;
    let temp = tempfile::tempdir().unwrap();
    for (relative, value) in [(0, 1), (4, 47), (4, 49), (4, 56), (6, 4), (7, 1)] {
        let mut bytes = original.to_vec();
        bytes[offset + relative] = value;
        let path = temp
            .path()
            .join(format!("mutated-{relative}-{value}.olean"));
        std::fs::write(&path, bytes).unwrap();
        let mut env = clean_kernel::env::Environment::default();
        assert!(
            crate::load_olean_file_with_import_policy(
                &mut env,
                &path,
                crate::OleanImportPolicy::new(crate::UnpinnedOleanImportPolicy::Allow),
            )
            .is_err(),
            "mutated root field {relative}={value}"
        );
        assert_eq!(env.constants().count(), 0);
    }
}

#[test]
fn modern_envelope_cannot_relabel_malformed_bytes_as_lean_v1() {
    let mut raw = Raw::new(Format::Modern);
    let name = raw.str(1, "known");
    assert!(raw.region().read_kernel_name_ptr(name).is_ok());
    // A modern file with a legacy-sized root must refuse; no retry/fallback.
    raw.byte(raw.root, 4, 48);
    assert!(raw.region().read_kernel_name_ptr(name).is_err());
    let mut old = lean_v1_raw();
    let name = old.str(1, "known");
    old.byte(old.root, 4, 56);
    assert!(old.region().read_kernel_name_ptr(name).is_err());
}

#[test]
fn modern_and_legacy_names_preserve_str_num_and_parent_identity() {
    for format in [Format::Modern, Format::Legacy] {
        let mut raw = Raw::new(format);
        let a = raw.str(1, "A");
        let hierarchy = raw.str(a, "B");
        let quoted = raw.str(1, "A.B");
        let empty = raw.str(1, "");
        let unicode = raw.str(1, "fidèle");
        let num = raw.num(a, 7);
        let digit = raw.str(a, "7");
        let padded = raw.str(a, "07");
        let pairs = [
            (hierarchy, Name::anon().str("A").str("B")),
            (quoted, Name::anon().str("A.B")),
            (empty, Name::anon().str("")),
            (unicode, Name::anon().str("fidèle")),
            (num, Name::anon().str("A").num(7)),
            (digit, Name::anon().str("A").str("7")),
            (padded, Name::anon().str("A").str("07")),
        ];
        let region = raw.region();
        for (pointer, expected) in &pairs {
            assert_eq!(region.read_kernel_name_ptr(*pointer).unwrap(), *expected);
        }
        assert_eq!(
            pairs
                .iter()
                .map(|(p, _)| region.read_kernel_name_ptr(*p).unwrap())
                .collect::<BTreeSet<_>>()
                .len(),
            pairs.len()
        );
        assert_eq!(region.read_kernel_name_ptr(1).unwrap(), Name::anon());
    }
}

#[test]
fn real_legacy_exporter_allocated_anonymous_parent_is_supported() {
    let bytes =
        crate::OleanExporter::export_minimal(&[("Legacy.Name", false)], &[], &[], &"a".repeat(40))
            .unwrap();
    let header = crate::header::OleanHeader::parse(&bytes).unwrap();
    let region = CompactedRegion::new(&bytes, header.base_addr);
    let root = region.ptr_to_offset(region.root_ptr().unwrap()).unwrap();
    let imports = region
        .ptr_to_offset(region.read_u64_at(root + 8).unwrap())
        .unwrap();
    let import = region
        .ptr_to_offset(region.read_u64_at(imports + 24).unwrap())
        .unwrap();
    let name = region.read_u64_at(import + 8).unwrap();
    assert_eq!(
        region.read_kernel_name_ptr(name).unwrap(),
        Name::anon().str("Legacy").str("Name")
    );
}

#[test]
fn modern_scalar_and_inline_mpz_numbers_are_never_raw_words_or_low_limb_aliases() {
    let mut raw = Raw::new(Format::Modern);
    let pointers = [0, 7, u64::MAX >> 1, 1u64 << 63, u64::MAX].map(|n| (raw.num(1, n), n));
    let too_large = raw.mpz(&[0, 1], 2);
    let name = raw.name(2, 1, too_large);
    let region = raw.region();
    for (pointer, expected) in pointers {
        assert_eq!(
            region.read_kernel_name_ptr(pointer).unwrap(),
            Name::anon().num(expected)
        );
    }
    assert!(region.read_kernel_name_ptr(name).is_err());
    assert!(region.read_kernel_nat_u64(too_large).is_err());
}

#[test]
fn nat_mpz_rejects_every_unmeasured_flag_sign_allocation_and_layout() {
    for mutation in 0..14 {
        let mut raw = Raw::new(Format::Modern);
        let pointer = raw.mpz(&[1u64 << 63], 1);
        match mutation {
            0 => raw.bytes[6] = 0,
            1 => raw.bytes[6] = 2,
            2 => raw.bytes[6] = 3,
            3 => raw.word(pointer, 8, (u64::from(u32::MAX) << 32) | 1),
            4 => raw.word(pointer, 8, 1),
            5 => raw.word(pointer, 8, 1u64 << 32),
            6 => raw.word(pointer, 8, (1u64 << 32) | 2),
            7 => raw.word(pointer, 16, pointer + 16),
            8 => raw.word(pointer, 24, 7),
            9 => raw.byte(pointer, 4, 40),
            10 => raw.byte(pointer, 7, tags::STRING),
            11 => raw.byte(pointer, 6, 1),
            12 => raw.byte(pointer, 0, 1),
            _ => {
                raw.bytes.truncate((pointer - BASE) as usize + 31);
            }
        }
        assert!(
            raw.region().read_kernel_nat_u64(pointer).is_err(),
            "mutation {mutation}"
        );
    }
    assert!(Raw::new(Format::Modern)
        .region()
        .read_kernel_nat_u64(0)
        .is_err());
}

#[test]
fn malformed_names_and_strings_do_not_enter_the_typed_cache() {
    for mutation in 0..13 {
        let mut raw = Raw::new(Format::Modern);
        let string = raw.string("hello");
        let name = raw.name(1, 1, string);
        match mutation {
            0 => raw.byte(name, 0, 1),
            1 => raw.byte(name, 4, 0),
            2 => raw.byte(name, 6, 1),
            3 => raw.byte(name, 7, 3),
            4 => raw.word(name, 8, name),
            5 => raw.word(name, 8, 3),
            6 => raw.word(string, 8, 1_048_577),
            7 => raw.word(string, 16, 1),
            8 => raw.word(string, 24, 1),
            9 => raw.byte(string, 32, 0xff),
            10 => raw.byte(string, 37, b'x'),
            11 => raw.byte(string, 0, 1),
            _ => raw.byte(string, 6, 1),
        }
        let region = raw.region();
        assert!(
            region.read_kernel_name_ptr(name).is_err(),
            "mutation {mutation}"
        );
        assert!(!region.typed_names.borrow().contains_key(&name));
    }
}

#[test]
fn module_mode_does_not_fall_back_on_malformed_name_or_root_header() {
    for format in [Format::Modern, Format::Legacy] {
        let mut raw = Raw::new(format);
        let pointer = raw.num(1, 7);
        raw.byte(pointer, 4, if format == Format::Modern { 0 } else { 32 });
        assert!(raw.region().read_kernel_name_ptr(pointer).is_err());
    }
    for mutation in 0..4 {
        let mut raw = Raw::new(Format::Modern);
        let pointer = raw.num(1, 7);
        match mutation {
            0 => raw.byte(raw.root, 0, 1),
            1 => raw.byte(raw.root, 7, 1),
            2 => raw.byte(raw.root, 6, 4),
            _ => raw.byte(raw.root, 4, 48),
        }
        assert!(
            raw.region().read_kernel_name_ptr(pointer).is_err(),
            "root mutation {mutation}"
        );
    }
}

#[test]
fn cached_parent_cannot_evade_name_depth_and_regions_do_not_share_identity() {
    let mut raw = Raw::new(Format::Modern);
    let mut parent = 1;
    let mut pointers = Vec::new();
    for _ in 0..257 {
        parent = raw.num(parent, 0);
        pointers.push(parent);
    }
    assert!(raw.region().read_kernel_name_ptr(pointers[256]).is_err());
    let region = raw.region();
    assert!(region.read_kernel_name_ptr(pointers[255]).is_ok());
    assert!(region.read_kernel_name_ptr(pointers[256]).is_err());
    let mut left = Raw::new(Format::Modern);
    let lp = left.str(1, "left");
    let mut right = Raw::new(Format::Modern);
    let rp = right.str(1, "rght");
    assert_eq!(lp, rp);
    assert_ne!(
        left.region().read_kernel_name_ptr(lp).unwrap(),
        right.region().read_kernel_name_ptr(rp).unwrap()
    );
}

#[test]
fn exact_legacy_allocated_anonymous_depth_256_succeeds_and_257_refuses() {
    let mut raw = Raw::new(Format::Legacy);
    let mut parent = raw.object(0, &[], 0, &[]);
    let mut pointers = Vec::new();
    for _ in 0..257 {
        parent = raw.num(parent, 0);
        pointers.push(parent);
    }
    // Both a cold full walk and a walk meeting cached parent identity must
    // count constructors, not the final allocated anonymous sentinel.
    assert!(raw.region().read_kernel_name_ptr(pointers[255]).is_ok());
    assert!(raw.region().read_kernel_name_ptr(pointers[256]).is_err());
    let region = raw.region();
    assert!(region.read_kernel_name_ptr(pointers[254]).is_ok());
    assert!(region.read_kernel_name_ptr(pointers[255]).is_ok());
    assert!(region.read_kernel_name_ptr(pointers[256]).is_err());
}

#[test]
fn typed_level_parameters_and_name_lists_keep_exact_identity_and_order() {
    for format in [Format::Modern, Format::Legacy] {
        let mut raw = Raw::new(format);
        let dotted = raw.str(1, "u.dot");
        let u = raw.str(1, "u");
        let nested = raw.str(u, "dot");
        let digit = raw.str(1, "07");
        let num = raw.num(1, 7);
        let names = raw.list(&[dotted, nested, digit, num, dotted]);
        let p = raw.level(4, &[dotted]);
        let q = raw.level(4, &[nested]);
        let succ = raw.level(1, &[p]);
        let max = raw.level(2, &[succ, q]);
        let imax = raw.level(3, &[p, q]);
        let levels = raw.list(&[1, p, succ, max, imax]);
        let region = raw.region();
        let pn = Name::anon().str("u.dot");
        let qn = Name::anon().str("u").str("dot");
        assert_eq!(
            region.read_kernel_name_list(names).unwrap(),
            vec![
                pn.clone(),
                qn.clone(),
                Name::anon().str("07"),
                Name::anon().num(7),
                pn.clone()
            ]
        );
        let p = Level::param(pn);
        let q = Level::param(qn);
        assert_eq!(
            region.read_kernel_level_list(levels).unwrap(),
            vec![
                Level::zero(),
                p.clone(),
                Level::succ(p.clone()),
                Level::max(Level::succ(p.clone()), q.clone()),
                Level::imax(p, q)
            ]
        );
        assert!(region.read_kernel_name_list(1).unwrap().is_empty());
        assert!(region.read_kernel_level_list(1).unwrap().is_empty());
    }
}

#[test]
fn malformed_typed_lists_and_failed_members_are_not_silently_dropped() {
    for mutation in 0..6 {
        let mut raw = Raw::new(Format::Modern);
        let name = raw.str(1, "ok");
        let list = raw.list(&[name]);
        match mutation {
            0 => raw.word(list, 16, list),
            1 => raw.word(list, 16, 3),
            2 => raw.byte(list, 7, 0),
            3 => raw.byte(list, 6, 1),
            4 => raw.byte(list, 0, 1),
            _ => raw.word(list, 8, 3),
        }
        assert!(
            raw.region().read_kernel_name_list(list).is_err(),
            "mutation {mutation}"
        );
    }
    let mut raw = Raw::new(Format::Modern);
    let bad = raw.level(5, &[1]);
    let list = raw.list(&[1, bad, 1]);
    assert!(raw.region().read_kernel_level_list(list).is_err());
}

#[test]
fn typed_list_item_bound_is_exact_for_complete_population() {
    let mut raw = Raw::new(Format::Modern);
    let mut pointer = 1;
    for _ in 0..100_000 {
        pointer = raw.object(1, &[1, pointer], 24, &[]);
    }
    let at_bound = pointer;
    let over = raw.object(1, &[1, pointer], 24, &[]);
    assert_eq!(
        raw.region().read_kernel_name_list(at_bound).unwrap().len(),
        100_000
    );
    assert!(raw.region().read_kernel_name_list(over).is_err());
}

#[test]
fn typed_levels_refuse_cycles_metavariables_bad_fields_and_unknown_size() {
    for mutation in 0..6 {
        let mut raw = Raw::new(Format::Modern);
        let pointer = raw.level(1, &[1]);
        match mutation {
            0 => raw.word(pointer, 8, pointer),
            1 => raw.byte(pointer, 7, 5),
            2 => raw.byte(pointer, 7, 6),
            3 => raw.byte(pointer, 6, 2),
            4 => raw.byte(pointer, 0, 1),
            _ => raw.byte(pointer, 4, 123),
        }
        assert!(
            raw.region().read_kernel_level_ptr(pointer).is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn typed_level_depth_and_visit_budget_refuse_large_dags_without_conflating_sharing() {
    let mut raw = Raw::new(Format::Modern);
    let mut pointer = 1;
    for _ in 0..256 {
        pointer = raw.level(1, &[pointer]);
    }
    assert!(raw.region().read_kernel_level_ptr(pointer).is_ok());
    let over = raw.level(1, &[pointer]);
    assert!(raw.region().read_kernel_level_ptr(over).is_err());
    let mut dag = 1;
    for _ in 0..8 {
        dag = raw.level(2, &[dag, dag]);
    }
    assert!(raw.region().read_kernel_level_ptr(dag).is_ok());
    for _ in 0..9 {
        dag = raw.level(2, &[dag, dag]);
    }
    assert!(raw.region().read_kernel_level_ptr(dag).is_err());
}
