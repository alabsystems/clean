// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The world table `build.rs` mints from `lean_worlds.tsv`, checked against
//! the header parser the importer uses (an independent reader of the same
//! fixture bytes), and the part-writer classification.

use super::{lean_worlds, part_writer_of_bytes, HeaderIdentity, PartWriter, WorldState};
use crate::header::OleanHeader;
use crate::OleanExporter;
use std::path::{Path, PathBuf};

const TABLE: &str = include_str!("../lean_worlds.tsv");

fn workspace() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// `(world, state, fixtures)` per row of `lean_worlds.tsv`.
fn tsv_rows() -> Vec<(String, String, Vec<String>)> {
    TABLE
        .lines()
        .filter(|line| !line.trim().is_empty() && !line.starts_with('#'))
        .map(|line| {
            let columns: Vec<&str> = line.split('\t').collect();
            assert_eq!(columns.len(), 4, "four columns: {line:?}");
            (
                columns[0].to_string(),
                columns[1].to_string(),
                columns[3].split(' ').map(str::to_string).collect(),
            )
        })
        .collect()
}

#[test]
fn test_world_table_has_exactly_one_oracle_and_it_is_the_lean_toolchain_pin() {
    let pin = std::fs::read_to_string(workspace().join("lean-toolchain")).expect("lean-toolchain");
    let oracles: Vec<_> = lean_worlds()
        .iter()
        .filter(|row| row.state == WorldState::Oracle)
        .collect();
    assert_eq!(oracles.len(), 1, "exactly one oracle: {oracles:?}");
    assert_eq!(
        Some(oracles[0].world),
        pin.trim().rsplit(':').next(),
        "the oracle is the lean-toolchain pin"
    );
}

#[test]
fn test_world_table_rows_follow_the_tsv_with_distinct_worlds_and_identities() {
    let rows = tsv_rows();
    let table = lean_worlds();
    assert_eq!(table.len(), rows.len(), "one row per TSV row");
    for (row, (world, state, _)) in table.iter().zip(&rows) {
        assert_eq!(row.world, world, "TSV order");
        assert_eq!(row.state.label(), state, "{world}: state");
    }
    for (i, a) in table.iter().enumerate() {
        for b in &table[i + 1..] {
            assert_ne!(a.world, b.world, "worlds are distinct");
            assert_ne!(
                a.identity, b.identity,
                "{} and {} share an identity",
                a.world, b.world
            );
        }
    }
}

/// Every fixture a row names is a Lean-written part whose identity, read
/// by the importer's header parser, is the row's.
#[test]
fn test_world_table_identities_agree_with_the_header_parser_on_every_fixture() {
    for (row, (world, _, fixtures)) in lean_worlds().iter().zip(tsv_rows()) {
        for fixture in fixtures {
            let bytes = std::fs::read(workspace().join(&fixture)).expect("tracked fixture");
            let header = OleanHeader::parse(&bytes).expect("fixture header parses");
            assert_eq!(
                HeaderIdentity::of_header(&header),
                row.identity,
                "{world}: {fixture}"
            );
            assert_eq!(
                header.lean_version.as_deref(),
                row.lean_version,
                "{fixture}"
            );
            assert_eq!(
                part_writer_of_bytes(&bytes).expect("classifies"),
                PartWriter::Lean {
                    identity: row.identity,
                    lean_version: header.lean_version.clone(),
                },
                "{fixture} is Lean-written"
            );
        }
    }
}

#[test]
fn test_part_writer_clean_exporter_output_is_of_no_world() {
    let bytes = OleanExporter::export_minimal(
        &[("Init", false)],
        &["Clean.x"],
        &[],
        "1ea5000000000000000000000000000000000000",
    )
    .expect("export");
    assert_eq!(
        part_writer_of_bytes(&bytes).expect("classifies"),
        PartWriter::Clean
    );
}

/// The same githash a Lean v1 part carries does not make Clean's exporter
/// output Lean-written: the root ModuleData layout decides.
#[test]
fn test_part_writer_clean_output_with_a_lean_githash_is_still_clean() {
    let v13 = std::fs::read(workspace().join("tests/fixtures/olean/v4.13.0/custom/Minimal.olean"))
        .expect("fixture");
    let githash = std::str::from_utf8(&v13[6..46]).expect("ascii githash");
    let bytes = OleanExporter::export_minimal(&[], &["Clean.y"], &[], githash).expect("export");
    assert_eq!(&bytes[6..46], &v13[6..46], "same header githash");
    assert_eq!(
        part_writer_of_bytes(&bytes).expect("classifies"),
        PartWriter::Clean
    );
}

/// A v3 header (Lean v4.36.0-rc1's closure format) is read by the 88-byte
/// layout so that its refusal can name it.
#[test]
fn test_part_writer_reads_a_v3_header_identity() {
    let mut bytes = vec![0u8; 96];
    bytes[..5].copy_from_slice(b"olean");
    bytes[5] = 3;
    bytes[6] = 1;
    bytes[7..18].copy_from_slice(b"4.36.0-rc1\0");
    bytes[40..80].copy_from_slice(b"0123456789abcdef0123456789abcdef01234567");
    let PartWriter::Lean {
        identity,
        lean_version,
    } = part_writer_of_bytes(&bytes).expect("classifies")
    else {
        panic!("a v3 part is Lean-written");
    };
    assert_eq!(lean_version.as_deref(), Some("4.36.0-rc1"));
    assert_eq!(
        identity.describe(),
        "olean v3, flags 0x01, githash 0123456789abcdef0123456789abcdef01234567"
    );
    assert!(
        part_writer_of_bytes(&bytes[..80]).is_err(),
        "a truncated v3 header is not classified"
    );
}
