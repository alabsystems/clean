// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Numeric ABI correction for the explicitly lossy dotted String projection.
use super::*;

const BASE: u64 = 0x10000;

#[derive(Clone, Copy)]
enum Format {
    LeanV1,
    LeanV2,
    CleanLegacy,
}

struct Raw {
    bytes: Vec<u8>,
    format: Format,
    root: u64,
}

impl Raw {
    fn new(format: Format) -> Self {
        let modern = matches!(format, Format::LeanV2);
        let mut bytes = vec![0; if modern { 96 } else { 64 }];
        bytes[..5].copy_from_slice(b"olean");
        let root_slot = if modern {
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
            format,
            root: 0,
        };
        raw.root = raw.object(
            0,
            &[1; 5],
            match format {
                Format::LeanV1 => 48,
                Format::LeanV2 => 56,
                Format::CleanLegacy => 0,
            },
            if modern { &[0; 8] } else { &[] },
        );
        raw.bytes[root_slot..root_slot + 8].copy_from_slice(&raw.root.to_le_bytes());
        raw
    }

    fn object(&mut self, tag: u8, fields: &[u64], size: u16, tail: &[u8]) -> u64 {
        while !self.bytes.len().is_multiple_of(8) {
            self.bytes.push(0);
        }
        let ptr = BASE + self.bytes.len() as u64;
        self.bytes.extend_from_slice(&[0; 4]);
        self.bytes.extend_from_slice(&size.to_le_bytes());
        self.bytes.extend_from_slice(&[fields.len() as u8, tag]);
        for field in fields {
            self.bytes.extend_from_slice(&field.to_le_bytes());
        }
        self.bytes.extend_from_slice(tail);
        ptr
    }

    fn word(&mut self, ptr: u64, rel: usize, word: u64) {
        let start = (ptr - BASE) as usize + rel;
        self.bytes[start..start + 8].copy_from_slice(&word.to_le_bytes());
    }

    fn byte(&mut self, ptr: u64, rel: usize, value: u8) {
        self.bytes[(ptr - BASE) as usize + rel] = value;
    }

    fn name(&mut self, tag: u8, parent: u64, field: u64) -> u64 {
        let legacy = matches!(self.format, Format::CleanLegacy);
        self.object(
            tag,
            &[parent, field],
            if legacy { 0 } else { 32 },
            if legacy { &[] } else { &[0; 8] },
        )
    }

    fn string_name(&mut self, parent: u64, value: &str) -> u64 {
        let text = self.object(tags::STRING, &[], 0, &[]);
        for word in [
            value.len() as u64 + 1,
            value.len() as u64 + 1,
            value.chars().count() as u64,
        ] {
            self.bytes.extend_from_slice(&word.to_le_bytes());
        }
        self.bytes.extend_from_slice(value.as_bytes());
        self.bytes.push(0);
        self.name(1, parent, text)
    }

    fn mpz(&mut self, limbs: &[u64]) -> u64 {
        let ptr = self.object(tags::MPZ, &[], (24 + 8 * limbs.len()) as u16, &[]);
        self.bytes
            .extend_from_slice(&(limbs.len() as i32).to_le_bytes());
        self.bytes
            .extend_from_slice(&(limbs.len() as i32).to_le_bytes());
        self.bytes.extend_from_slice(&(ptr + 24).to_le_bytes());
        for limb in limbs {
            self.bytes.extend_from_slice(&limb.to_le_bytes());
        }
        ptr
    }

    fn read(&self, ptr: u64) -> OleanResult<String> {
        CompactedRegion::new(&self.bytes, BASE).read_name_at((ptr - BASE) as usize)
    }
}

#[test]
fn modern_tagged_numbers_are_unboxed() {
    let mut raw = Raw::new(Format::LeanV2);
    for n in [0, 7, (1u64 << 63) - 1] {
        let name = raw.name(2, 1, (n << 1) | 1);
        assert_eq!(raw.read(name).unwrap(), n.to_string());
    }
}

#[test]
fn lean_v1_tagged_numbers_are_unboxed_without_heap_guessing() {
    let mut raw = Raw::new(Format::LeanV1);
    let name = raw.name(2, 1, 15);
    assert_eq!(raw.read(name).unwrap(), "7");
    let heap = raw.mpz(&[1u64 << 63]);
    let boxed = raw.name(2, 1, heap);
    assert!(raw.read(boxed).is_err());
}

#[test]
fn modern_single_limb_boxed_numbers_are_not_addresses() {
    let mut raw = Raw::new(Format::LeanV2);
    for n in [1u64 << 63, u64::MAX] {
        let heap = raw.mpz(&[n]);
        let name = raw.name(2, 1, heap);
        assert_eq!(raw.read(name).unwrap(), n.to_string());
    }
}

#[test]
fn clean_export_raw_numbers_remain_raw() {
    let mut raw = Raw::new(Format::CleanLegacy);
    for n in [0, 7, 1u64 << 63, u64::MAX] {
        let name = raw.name(2, 1, n);
        assert_eq!(raw.read(name).unwrap(), n.to_string());
    }
}

#[test]
fn unfinished_clean_export_is_explicit_not_a_modern_retry() {
    // OleanExporter::with_base_addr reserves exactly this all-zero prefix
    // before writing its final file header and ModuleData root.
    let mut raw = Raw::new(Format::CleanLegacy);
    let name = raw.name(2, 1, 7);
    raw.bytes[..64].fill(0);
    assert_eq!(raw.read(name).unwrap(), "7");
    raw.byte(name, 4, 32);
    assert!(
        raw.read(name).is_err(),
        "scratch encoding still requires cs_sz=0"
    );

    let mut modern = Raw::new(Format::LeanV2);
    let name = modern.name(2, 1, 15);
    modern.bytes[0] = b'x';
    assert!(
        modern.read(name).is_err(),
        "failed modern header is not scratch"
    );
}

#[test]
fn module_layout_selects_encoding_without_object_fallback() {
    for (format, wrong_size) in [(Format::LeanV2, 0), (Format::CleanLegacy, 32)] {
        let mut raw = Raw::new(format);
        let name = raw.name(2, 1, 15);
        raw.byte(name, 4, wrong_size);
        assert!(raw.read(name).is_err());
    }
    let mut raw = Raw::new(Format::LeanV2);
    let name = raw.name(2, 1, 15);
    raw.byte(raw.root, 4, 48);
    assert!(raw.read(name).is_err());
}

#[test]
fn malformed_numeric_name_headers_refuse() {
    for (offset, value) in [(0, 1), (4, 24), (5, 1), (6, 1), (7, 3)] {
        let mut raw = Raw::new(Format::LeanV2);
        let name = raw.name(2, 1, 15);
        raw.byte(name, offset, value);
        assert!(raw.read(name).is_err(), "header mutation at {offset}");
    }
}

#[test]
fn null_and_out_of_region_nats_refuse() {
    for value in [0, BASE - 8, BASE + 0x100000] {
        let mut raw = Raw::new(Format::LeanV2);
        let name = raw.name(2, 1, value);
        assert!(raw.read(name).is_err());
    }
}

#[test]
fn malformed_boxed_nat_headers_and_payloads_refuse() {
    for (offset, value) in [
        (0, 1),
        (4, 24),
        (6, 1),
        (7, 249),
        (8, 2),
        (12, 0),
        (15, 255),
        (16, 0),
        (31, 0),
    ] {
        let mut raw = Raw::new(Format::LeanV2);
        let heap = raw.mpz(&[1u64 << 63]);
        let name = raw.name(2, 1, heap);
        raw.byte(heap, offset, value);
        assert!(raw.read(name).is_err(), "MPZ mutation at {offset}");
    }
    let mut raw = Raw::new(Format::LeanV2);
    let heap = raw.mpz(&[1u64 << 63]);
    let name = raw.name(2, 1, heap);
    raw.bytes[6] = 0;
    assert!(raw.read(name).is_err(), "unmeasured non-GMP encoding");
}

#[test]
fn over_u64_numbers_are_refused_without_truncation() {
    let mut raw = Raw::new(Format::LeanV2);
    let heap = raw.mpz(&[0, 1]);
    let name = raw.name(2, 1, heap);
    assert!(raw.read(name).is_err());
}

#[test]
fn truncated_numeric_name_refuses_missing_cached_word() {
    let mut raw = Raw::new(Format::LeanV2);
    let name = raw.name(2, 1, 15);
    raw.bytes.truncate(raw.bytes.len() - 1);
    assert!(raw.read(name).is_err());
}

#[test]
fn malformed_numeric_parents_and_cycle_refuse() {
    for parent in [0, 3] {
        let mut raw = Raw::new(Format::LeanV2);
        let name = raw.name(2, parent, 15);
        assert!(raw.read(name).is_err());
    }
    let mut raw = Raw::new(Format::LeanV2);
    let name = raw.name(2, 1, 15);
    raw.word(name, 8, name);
    assert!(raw.read(name).is_err());
}

#[test]
fn dotted_projection_still_loses_string_constructor_identity() {
    let mut raw = Raw::new(Format::LeanV2);
    let prefix = raw.string_name(1, "P");
    let numeric = raw.name(2, prefix, 15);
    let string = raw.string_name(prefix, "7");
    let quoted = raw.string_name(1, "P.7");
    let region = CompactedRegion::new(&raw.bytes, BASE);
    assert_ne!(
        region.read_kernel_name_ptr(numeric).unwrap(),
        region.read_kernel_name_ptr(string).unwrap()
    );
    assert_ne!(
        region.read_kernel_name_ptr(string).unwrap(),
        region.read_kernel_name_ptr(quoted).unwrap()
    );
    assert_eq!(raw.read(numeric).unwrap(), raw.read(string).unwrap());
    assert_eq!(raw.read(string).unwrap(), raw.read(quoted).unwrap());
}

/// `numeric_probe/NumericProbeSeven.olean` (fixture family F5, minted by the
/// pinned Lean's own `writeModule` through `GenNumericProbe.lean`) read against
/// the independent upstream oracle (`oracle/DumpOlean.lean`, run by the same
/// pinned binary): seven `constNames`, six of which fit a `u64` and one of
/// which (`NumericProbe.<2^64>`) the oracle prints as a bare integer above
/// `u64::MAX`, so `as_u64()` is `None` and the raw reader must refuse that row.
/// The 7 and the (6, 1) split are the family's declared design
/// (`GenNumericProbe.lean`, `probeNames`), measured `constNames = 7` in its
/// README. Fails closed when the pinned toolchain is absent.
#[test]
fn actual_seven_name_oracle_preserves_population_and_refusal() {
    let fixture =
        crate::test_support::compiled_fixture_dir("numeric_probe").join("NumericProbeSeven.olean");
    let data = std::fs::read(&fixture).unwrap();
    let oracle = crate::test_support::run_oracle(&[fixture.to_str().unwrap()]);
    let header = OleanHeader::parse(&data).unwrap();
    let region = CompactedRegion::new(&data, header.base_addr);
    let root = region.ptr_to_offset(region.root_ptr().unwrap()).unwrap();
    let array = region
        .ptr_to_offset(region.read_u64_at(root + 16).unwrap())
        .unwrap();
    let count = region.read_u64_at(array + 8).unwrap();
    let expected = oracle["parts"][0]["const_names"].as_array().unwrap();
    assert_eq!(count, 7);
    assert_eq!(expected.len(), 7);
    let mut supported = 0;
    let mut refused = 0;
    for (index, name) in expected.iter().enumerate() {
        let pointer = region.read_u64_at(array + 24 + index * 8).unwrap();
        let observed = region.read_name_at(region.ptr_to_offset(pointer).unwrap());
        let components = name.as_array().unwrap();
        let oversized = components
            .iter()
            .any(|part| part["kind"] == "num" && part["value"].as_u64().is_none());
        if oversized {
            assert!(
                observed.is_err(),
                "over-u64 raw row {index} must remain refused"
            );
            refused += 1;
        } else {
            let projection = components
                .iter()
                .map(|part| {
                    if part["kind"] == "str" {
                        part["value"].as_str().unwrap().to_owned()
                    } else {
                        part["value"].as_u64().unwrap().to_string()
                    }
                })
                .collect::<Vec<_>>()
                .join(".");
            assert_eq!(observed.unwrap(), projection, "actual raw row {index}");
            supported += 1;
        }
    }
    assert_eq!((supported, refused), (6, 1));
}
