// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
#![cfg(feature = "kcheck-trace")]

//! K2's feature-gated candidate-advice producer over real export bytes.
//!
//! The producer is an independent tracing-core run beside the fenced reference
//! entry, not the production checker. Only `kcheck` can decide that a frame
//! replays.

use std::collections::BTreeMap;
use std::io::{Cursor, Read};
use std::path::{Path, PathBuf};
use std::process::Command;

use serde_json::Value;
use sha2::{Digest, Sha256};

const EXPECTED_FIXTURE_SHA256: &str =
    "d5b0062a92a82c626d0ba96108440ff6ba928e03ef74cd8709e648d71256cadf";
const DECLARATION_KINDS: [&str; 6] = ["def", "thm", "opaque", "axiom", "quot", "inductive"];

fn fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/lean/v4.30.0-rc2/lean4export_minted")
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

/// Decompress the fixture and authenticate it before a caller can use it.
fn fixture_bytes() -> Vec<u8> {
    let path = fixture_dir().join("prelude_roots.ndjson.gz");
    let compressed =
        std::fs::read(&path).unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
    let mut bytes = Vec::new();
    flate2::read::GzDecoder::new(compressed.as_slice())
        .read_to_end(&mut bytes)
        .expect("prelude_roots.ndjson.gz is a gzip stream");

    let sidecar_path = fixture_dir().join("prelude_roots.ndjson.sidecar.json");
    let sidecar: Value = serde_json::from_slice(
        &std::fs::read(&sidecar_path)
            .unwrap_or_else(|error| panic!("read {}: {error}", sidecar_path.display())),
    )
    .expect("the fixture sidecar is JSON");
    let actual = hex(&Sha256::digest(&bytes));
    assert_eq!(
        sidecar["export"]["sha256"].as_str(),
        Some(actual.as_str()),
        "the decompressed fixture must match its sidecar before use"
    );
    assert_eq!(actual, EXPECTED_FIXTURE_SHA256);
    bytes
}

fn declaration_records(bytes: &[u8]) -> Vec<(usize, &'static str)> {
    bytes
        .split(|byte| *byte == b'\n')
        .enumerate()
        .filter_map(|(index, line)| {
            if line.is_empty() {
                return None;
            }
            let value: Value = serde_json::from_slice(line)
                .unwrap_or_else(|error| panic!("NDJSON line {}: {error}", index + 1));
            let object = value
                .as_object()
                .unwrap_or_else(|| panic!("NDJSON line {} is not an object", index + 1));
            DECLARATION_KINDS
                .into_iter()
                .find(|kind| object.contains_key(*kind))
                .map(|kind| (index + 1, kind))
        })
        .collect()
}

fn read_uleb128(bytes: &[u8], cursor: &mut usize) -> usize {
    let mut value = 0usize;
    let mut shift = 0u32;
    loop {
        let byte = *bytes
            .get(*cursor)
            .unwrap_or_else(|| panic!("truncated frame length at byte {cursor}"));
        *cursor += 1;
        let low = usize::from(byte & 0x7f);
        value |= low
            .checked_shl(shift)
            .unwrap_or_else(|| panic!("frame length overflows usize at byte {cursor}"));
        if byte & 0x80 == 0 {
            return value;
        }
        shift += 7;
        assert!(
            shift < usize::BITS,
            "overlong frame length at byte {cursor}"
        );
    }
}

fn decode_frames(bytes: &[u8]) -> Vec<Vec<u8>> {
    let mut cursor = 0usize;
    let mut frames = Vec::new();
    while cursor < bytes.len() {
        let length = read_uleb128(bytes, &mut cursor);
        let end = cursor
            .checked_add(length)
            .expect("frame endpoint fits in usize");
        assert!(end <= bytes.len(), "frame at byte {cursor} is truncated");
        frames.push(bytes[cursor..end].to_vec());
        cursor = end;
    }
    frames
}

#[test]
fn emits_one_frame_per_pinned_export_declaration() {
    let export = fixture_bytes();
    let records = declaration_records(&export);
    assert_eq!(records.len(), 310, "fixture declaration-record count");

    let temp = tempfile::tempdir().expect("temporary output directory");
    let export_path = temp.path().join("prelude_roots.ndjson");
    let advice_path = temp.path().join("advice.bin");
    std::fs::write(&export_path, &export).expect("write decompressed fixture");
    let output = Command::new(env!("CARGO_BIN_EXE_kcheck_advice_emit"))
        .arg(&export_path)
        .args(["--out"])
        .arg(&advice_path)
        .output()
        .expect("run kcheck_advice_emit");
    assert!(
        output.status.success(),
        "kcheck_advice_emit failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stdout = std::str::from_utf8(&output.stdout).expect("summary is UTF-8");
    assert_eq!(stdout.lines().count(), 1, "summary must be one JSON line");
    let summary: Value = serde_json::from_str(stdout).expect("summary is JSON");
    let encoded = std::fs::read(&advice_path).expect("read advice.bin");
    let frames = decode_frames(&encoded);
    assert_eq!(frames.len(), 310);
    assert_eq!(summary["frames"], 310);
    let non_empty = frames.iter().filter(|frame| !frame.is_empty()).count();
    assert_eq!(summary["non_empty"], non_empty);
    assert_eq!(summary["sha256"], hex(&Sha256::digest(&encoded)));

    let id_index = records
        .iter()
        .position(|(line, kind)| *line == 8155 && *kind == "def")
        .expect("line 8155 is the `id` definition record");
    let expected_id = [0x01, 0x28, 0x16, 0x16, 0x16, 0x16, 0x16, 0x16, 0x16, 0x02];
    assert_eq!(
        frames[id_index],
        expected_id,
        "`id` candidate advice differs from the predicted journal bytes: got {}",
        hex(&frames[id_index])
    );

    let mut empty_kind_counts = BTreeMap::<&str, usize>::new();
    for ((line, kind), frame) in records.iter().zip(&frames) {
        if matches!(*kind, "inductive" | "quot" | "axiom") {
            assert!(
                frame.is_empty(),
                "{kind} declaration record at line {line} must have an empty frame; got {}",
                hex(frame)
            );
            *empty_kind_counts.entry(*kind).or_default() += 1;
        }
    }
    assert_eq!(empty_kind_counts.get("inductive"), Some(&49));
    assert_eq!(empty_kind_counts.get("quot"), Some(&4));
    assert_eq!(empty_kind_counts.get("axiom"), Some(&1));
}

#[test]
fn replay_candidate_cli_emits_the_observed_unit_conversion() {
    let export = fixture_bytes();
    let records = declaration_records(&export);
    let unit = records
        .iter()
        .position(|r| *r == (543, "def"))
        .expect("Unit.unit declaration line");
    let temp = tempfile::tempdir().expect("temporary output directory");
    let export_path = temp.path().join("prelude.ndjson");
    let advice_path = temp.path().join("candidate.bin");
    std::fs::write(&export_path, export).expect("write pinned fixture");
    let output = Command::new(env!("CARGO_BIN_EXE_kcheck_advice_emit"))
        .arg("--replay-candidates")
        .arg(export_path)
        .arg("--out")
        .arg(&advice_path)
        .output()
        .expect("run replay candidate emitter");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let encoded = std::fs::read(advice_path).expect("read native candidate wire");
    let frames = decode_frames(&encoded);
    assert_eq!(frames.len(), records.len());
    // DEPTH 100000, STOP at type formation, DELTA_R for Unit, then CONST.
    assert_eq!(frames[unit], [0x01, 0xa0, 0x8d, 0x06, 0x16, 0x10, 0x04]);
}

/// The header and canonical Nat block used by P3, followed by its False block.
fn p3_export_prefix() -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/lean/v4.30.0-rc2/ndjson_minted/nat_add_literal.ndjson");
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
    let mut lines: Vec<&str> = text.lines().take(51).collect();
    assert!(
        lines[50].starts_with(r#"{"inductive""#),
        "line 51 must close the Nat block: {}",
        lines[50]
    );
    assert_eq!(
        lines[17], r#"{"const":{"name":2,"us":[]},"ie":6}"#,
        "expression 6 must be Nat.zero"
    );
    lines.extend([
        r#"{"in":12,"str":{"pre":0,"str":"False"}}"#,
        r#"{"in":13,"str":{"pre":12,"str":"rec"}}"#,
        r#"{"ie":36,"sort":0}"#,
        r#"{"const":{"name":12,"us":[]},"ie":37}"#,
        r#"{"ie":38,"sort":2}"#,
        r#"{"forallE":{"binderInfo":"default","body":38,"name":6,"type":37},"ie":39}"#,
        r#"{"bvar":1,"ie":40}"#,
        r#"{"bvar":0,"ie":41}"#,
        r#"{"app":{"arg":41,"fn":40},"ie":42}"#,
        r#"{"forallE":{"binderInfo":"default","body":42,"name":6,"type":37},"ie":43}"#,
        r#"{"forallE":{"binderInfo":"default","body":43,"name":5,"type":39},"ie":44}"#,
        r#"{"inductive":{"ctors":[],"recs":[{"all":[12],"isUnsafe":false,"k":false,"levelParams":[7],"name":13,"numIndices":0,"numMinors":0,"numMotives":1,"numParams":0,"rules":[],"type":44}],"types":[{"all":[12],"ctors":[],"isRec":false,"isReflexive":false,"isUnsafe":false,"levelParams":[],"name":12,"numIndices":0,"numNested":0,"numParams":0,"type":36}]}}"#,
    ]);
    let mut output = lines.join("\n");
    output.push('\n');
    output
}

#[test]
fn planted_theorem_and_atomic_records_have_empty_frames() {
    let planted = format!(
        "{}{}\n{}\n",
        p3_export_prefix(),
        r#"{"in":14,"str":{"pre":0,"str":"planted"}}"#,
        r#"{"thm":{"all":[14],"levelParams":[],"name":14,"type":37,"value":6}}"#,
    );
    use clean_olean::ndjson::advice::{
        export_advice_frames, export_advice_frames_from, AdviceFrameSource,
    };

    let (frames, count) = export_advice_frames(Cursor::new(planted.as_bytes()))
        .expect("the planted export is readable even though the fenced entry refuses its theorem");
    let candidate =
        export_advice_frames_from(Cursor::new(planted), AdviceFrameSource::ReplayCandidate)
            .expect("the candidate producer can read the planted export");
    assert_eq!(
        candidate,
        (frames.clone(), count),
        "neither native mode emits a partial or refused frame"
    );
    assert_eq!(count, 3);
    assert_eq!(frames.len(), 3);
    assert!(frames[0].is_empty(), "the Nat inductive frame is empty");
    assert!(frames[1].is_empty(), "the False inductive frame is empty");
    assert!(
        frames[2].is_empty(),
        "the fenced entry refused `planted`, so its frame must be empty; got {}",
        hex(&frames[2])
    );
}
