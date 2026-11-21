// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Exercise the real bounded extension decoder without running an oracle.
use super::*;
use clean_kernel::env::{CompilerExternArity, CompilerExternEntry, CompilerExternMetadata};

const BASE: u64 = 0x10000;
struct Objects(Vec<u8>);
impl Objects {
    fn new() -> Self {
        Self(vec![0; 64])
    }
    fn align(&mut self) {
        while self.0.len() % 8 != 0 {
            self.0.push(0);
        }
    }
    fn object(&mut self, tag: u8, fields: &[u64]) -> u64 {
        self.align();
        let pointer = BASE + self.0.len() as u64;
        self.0
            .extend_from_slice(&[0, 0, 0, 0, 0, 0, fields.len() as u8, tag]);
        for field in fields {
            self.0.extend_from_slice(&field.to_le_bytes());
        }
        pointer
    }
    fn string(&mut self, value: &str) -> u64 {
        let pointer = self.object(tags::STRING, &[]);
        for value in [
            (value.len() + 1) as u64,
            (value.len() + 1) as u64,
            value.chars().count() as u64,
        ] {
            self.0.extend_from_slice(&value.to_le_bytes());
        }
        self.0.extend_from_slice(value.as_bytes());
        self.0.push(0);
        self.align();
        pointer
    }
    fn name(&mut self, value: &str) -> u64 {
        let anonymous = self.object(0, &[]);
        let string = self.string(value);
        self.object(1, &[anonymous, string])
    }
    fn entry(&mut self, kind: u8, backend: &str, text: &str) -> u64 {
        let backend = self.name(backend);
        if kind == 0 {
            return self.object(kind, &[backend]);
        }
        let text = self.string(text);
        self.object(kind, &[backend, text])
    }
    fn list(&mut self, entries: &[u64]) -> u64 {
        entries
            .iter()
            .rev()
            .fold(1, |tail, entry| self.object(1, &[*entry, tail]))
    }
}

#[test]
fn decoded_externs_keep_every_kind_backend_order_and_legacy_arity() {
    for arity in [
        CompilerExternArity::Unspecified,
        CompilerExternArity::Legacy(None),
        CompilerExternArity::Legacy(Some(3)),
    ] {
        let mut data = Objects::new();
        let entries = [
            data.entry(2, "llvm", "first"),
            data.entry(2, "c", "other"),
            data.entry(0, "all", ""),
            data.entry(1, "c", "#1"),
            data.entry(3, "cpp", "foreign"),
            7,
        ];
        let list = data.list(&entries);
        let descriptor = match &arity {
            CompilerExternArity::Unspecified => list,
            CompilerExternArity::Legacy(None) => data.object(0, &[1, list]),
            CompilerExternArity::Legacy(Some(value)) => {
                let some = data.object(1, &[(*value << 1) | 1]);
                data.object(0, &[some, list])
            }
        };
        let target = data.name("subject");
        let row = data.object(0, &[target, descriptor]);
        let region = CompactedRegion::new(&data.0, BASE);
        let read = Reader {
            region: &region,
            layout: TypedModuleLayout::LeanV2,
            legacy: false,
            remaining_items: Cell::new(MAX_TOTAL_ARRAY_ITEMS),
        };
        let TypedExtensionEntry::Extern {
            decl,
            symbol,
            metadata,
        } = read.extern_row(row).expect("all represented fields decode")
        else {
            panic!("extern")
        };
        assert_eq!(decl, Name::from_string("subject"));
        assert_eq!(symbol, "first");
        let CompilerExternMetadata::Complete(actual) = metadata else {
            panic!("complete represented data")
        };
        assert_eq!(actual.arity, arity);
        assert_eq!(
            actual.entries,
            vec![
                CompilerExternEntry::Standard {
                    backend: Name::from_string("llvm"),
                    symbol: "first".into()
                },
                CompilerExternEntry::Standard {
                    backend: Name::from_string("c"),
                    symbol: "other".into()
                },
                CompilerExternEntry::Adhoc {
                    backend: Name::from_string("all")
                },
                CompilerExternEntry::Inline {
                    backend: Name::from_string("c"),
                    pattern: "#1".into()
                },
                CompilerExternEntry::Foreign {
                    backend: Name::from_string("cpp"),
                    symbol: "foreign".into()
                },
                CompilerExternEntry::Opaque,
            ]
        );
    }
}

#[test]
fn unknown_extern_constructor_never_becomes_a_standard_symbol() {
    let mut data = Objects::new();
    let bad = data.entry(5, "c", "recognized_spelling");
    let list = data.list(&[bad]);
    let target = data.name("subject");
    let row = data.object(0, &[target, list]);
    let region = CompactedRegion::new(&data.0, BASE);
    let read = Reader {
        region: &region,
        layout: TypedModuleLayout::LeanV2,
        legacy: false,
        remaining_items: Cell::new(MAX_TOTAL_ARRAY_ITEMS),
    };
    assert!(read.extern_row(row).is_err());
}
