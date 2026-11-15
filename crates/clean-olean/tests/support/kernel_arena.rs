// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The vendored Kernel Arena round 2026-09 (Zenodo record 22944094, DOI
//! 10.5281/zenodo.22944094, Apache-2.0), shared by `tests/ndjson_front_door.rs`
//! and `tests/kernel_arena_battery.rs`, each of which includes this file with
//! `#[path]`.
//!
//! The archive is vendored byte for byte (decision R115 in `docs/DECISIONS.md`:
//! 3.5 MB compressed, so no fetch, and no offline refusal). Its sha256 is
//! checked before a byte of it is read, and it is read in memory: the gzip
//! stream through `flate2`, the tar stream by the reader below (ustar with pax
//! extended headers, which is what the archive holds), never extracted to disk
//! and never executed.

use std::collections::BTreeMap;
use std::io::Read;
use std::path::PathBuf;

use sha2::{Digest, Sha256};

/// The round's directory under `tests/fixtures`.
pub fn round_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/kernel_arena/round-2026-09")
}

/// The archive's pinned sha256 (the plan item's `98a69742…3bee0d`).
pub const ARCHIVE_SHA256: &str = "98a69742b538296c5f413d0527dfeef8c4d1815fe64b12c8623cd33de63bee0d";

/// The number of tests the archive holds: 71 bad, 122 good.
pub const ARCHIVE_FILES: usize = 193;

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// sha256 of `bytes`, lower-case hex.
pub fn sha256_hex(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
}

/// Every file of the archive, by path (`bad/bugs/orphan-rec.ndjson`, ...).
///
/// # Panics
///
/// When the archive is missing, its sha256 is not the pinned one, or its tar
/// stream holds anything but regular files and pax headers.
pub fn archive() -> BTreeMap<String, Vec<u8>> {
    let path = round_dir().join("lean-arena-round-2026-09-tests.tar.gz");
    let compressed = std::fs::read(&path)
        .unwrap_or_else(|e| panic!("{}: the vendored arena archive: {e}", path.display()));
    let digest = sha256_hex(&compressed);
    assert_eq!(
        digest,
        ARCHIVE_SHA256,
        "{}: sha256 {digest}, pinned {ARCHIVE_SHA256}; refusing to read it",
        path.display()
    );
    let mut raw = Vec::new();
    flate2::read::GzDecoder::new(compressed.as_slice())
        .read_to_end(&mut raw)
        .expect("the archive's gzip stream");
    let files = untar(&raw);
    assert_eq!(files.len(), ARCHIVE_FILES, "the archive's file count");
    files
}

fn octal(field: &[u8]) -> usize {
    let text: String = field
        .iter()
        .take_while(|&&b| b != 0)
        .map(|&b| char::from(b))
        .collect();
    usize::from_str_radix(text.trim(), 8).unwrap_or_else(|e| panic!("tar octal {text:?}: {e}"))
}

fn text(field: &[u8]) -> String {
    let end = field.iter().position(|&b| b == 0).unwrap_or(field.len());
    String::from_utf8(field[..end].to_vec()).expect("tar name is UTF-8")
}

/// pax records `"<len> <key>=<value>\n"`.
fn pax(records: &[u8]) -> BTreeMap<String, String> {
    let mut out = BTreeMap::new();
    let mut rest = records;
    while !rest.is_empty() {
        let space = rest
            .iter()
            .position(|&b| b == b' ')
            .expect("pax record length");
        let len: usize = std::str::from_utf8(&rest[..space])
            .expect("pax length")
            .parse()
            .expect("pax length");
        let record = std::str::from_utf8(&rest[space + 1..len - 1]).expect("pax record");
        let (key, value) = record.split_once('=').expect("pax key=value");
        out.insert(key.to_owned(), value.to_owned());
        rest = &rest[len..];
    }
    out
}

fn untar(raw: &[u8]) -> BTreeMap<String, Vec<u8>> {
    let mut files = BTreeMap::new();
    let mut pos = 0usize;
    let mut pending: BTreeMap<String, String> = BTreeMap::new();
    while pos + 512 <= raw.len() {
        let header = &raw[pos..pos + 512];
        if header.iter().all(|&b| b == 0) {
            break;
        }
        let mut size = octal(&header[124..136]);
        let kind = header[156];
        let body_start = pos + 512;
        if kind == b'x' {
            pending = pax(&raw[body_start..body_start + size]);
        } else {
            assert!(
                kind == b'0' || kind == 0,
                "tar entry of type {:?}: the arena archive holds regular files only",
                char::from(kind)
            );
            if let Some(s) = pending.get("size") {
                size = s.parse().expect("pax size");
            }
            let name = match pending.get("path") {
                Some(path) => path.clone(),
                None => {
                    let prefix = text(&header[345..500]);
                    let name = text(&header[0..100]);
                    if prefix.is_empty() {
                        name
                    } else {
                        format!("{prefix}/{name}")
                    }
                }
            };
            files.insert(name, raw[body_start..body_start + size].to_vec());
            pending.clear();
        }
        pos = body_start + size.div_ceil(512) * 512;
    }
    files
}

/// The vendored round table (`scripts/kernel_arena_round.py`).
pub fn table() -> serde_json::Value {
    let path = round_dir().join("round-2026-09.table.json");
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("{}: the vendored round table: {e}", path.display()));
    serde_json::from_str(&text).expect("the round table is JSON")
}
