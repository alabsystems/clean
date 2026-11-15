// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lake-style payload companions must share a non-overlapping pointer layout.

use super::OleanExporter;
use crate::header::{OleanHeader, HEADER_SIZE, HEADER_SIZE_V2};
use crate::payload::{decode_clean_payload, encode_clean_payload, CleanPayload};
use clean_kernel::env::{ConstantInfo, ConstantKind, Environment, Reducibility};
use clean_kernel::{Expr, Name};

const HASH: &str = "1ea5000000000000000000000000000000000000";

fn payload(name: &str) -> CleanPayload {
    payload_of(&[name])
}

/// One `Type := Prop` definition per name.
fn payload_of(names: &[&str]) -> CleanPayload {
    CleanPayload {
        constants: names
            .iter()
            .map(|name| ConstantInfo {
                name: Name::from_string(name),
                level_params: vec![],
                type_: Expr::type_(),
                value: Some(Expr::prop()),
                is_reducible: false,
                reducibility: Reducibility::Regular(0),
                kind: ConstantKind::Definition,
            })
            .collect(),
        ..CleanPayload::default()
    }
}

fn base(payload: &CleanPayload, names: &[&str]) -> Vec<u8> {
    OleanExporter::export_with_payload(&[], names, &[], HASH, payload).expect("base export")
}

fn successor(previous: &[u8], payload: &CleanPayload, names: &[&str]) -> Vec<u8> {
    OleanExporter::export_with_payload_after(previous, &[], names, &[], HASH, payload)
        .expect("companion export")
}

fn assert_follows(previous: &[u8], next: &[u8]) {
    let prior_header = OleanHeader::parse(previous).expect("predecessor header");
    let header = OleanHeader::parse(next).expect("companion header");
    let end = prior_header.base_addr + previous.len() as u64;
    assert_eq!(header.base_addr, (end + 7) & !7);
    assert!(header.base_addr >= end);
    assert!(header.base_addr - end < 8);
    assert_eq!(header.version, prior_header.version);
    assert_eq!(header.flags, prior_header.flags);
    assert_eq!(header.lean_version, prior_header.lean_version);
    assert_eq!(header.git_hash, prior_header.git_hash);
}

const ALL: [&str; 3] = ["Layout.public", "Layout.server", "Layout.private"];

/// The three parts of one Clean-built (non-module) artifact: a base declaring `base_names`, a
/// server part declaring `Layout.server` and a private part declaring `Layout.private`, written
/// into a fresh directory. Returns the directory and the parts' bytes.
fn layout_dir(base_names: &[&str]) -> (tempfile::TempDir, [Vec<u8>; 3]) {
    let public_payload = payload_of(base_names);
    let public = base(&public_payload, base_names);
    let server = successor(&public, &payload("Layout.server"), &["Layout.server"]);
    let private = successor(&server, &payload("Layout.private"), &["Layout.private"]);
    assert_follows(&public, &server);
    assert_follows(&server, &private);
    let compact_len = public.len() - encode_clean_payload(&public_payload).expect("footer").len();
    assert!(
        OleanHeader::parse(&server).unwrap().base_addr
            > OleanHeader::parse(&public).unwrap().base_addr + compact_len as u64
    );
    let dir = tempfile::TempDir::new().expect("owned fixture directory");
    for (suffix, bytes) in [
        ("olean", &public),
        ("olean.server", &server),
        ("olean.private", &private),
    ] {
        std::fs::write(dir.path().join(format!("Layout.{suffix}")), bytes).expect("write part");
    }
    (dir, [public, server, private])
}

/// A non-module artifact is read through its `.olean`, so its companions may only restate
/// names the `.olean` declares (R113); `clean lake build` writes every name into the `.olean`
/// and empty companions. Here the base declares all three and each companion restates one.
#[test]
fn payload_companions_follow_full_extents_and_round_trip_all_parts() {
    let (dir, parts) = layout_dir(&ALL);
    for (bytes, count) in parts.iter().zip([3, 1, 1]) {
        assert_eq!(
            decode_clean_payload(bytes)
                .unwrap()
                .unwrap()
                .constants
                .len(),
            count
        );
    }
    let mut env = Environment::default();
    let summaries = crate::load_module_with_deps(&mut env, "Layout", &[dir.path().to_path_buf()])
        .expect("actual incremental importer must accept all three parts");
    assert_eq!(summaries.len(), 3);
    for name in ALL {
        let info = env
            .get_const(&Name::from_string(name))
            .expect("each part's constant");
        assert_eq!(info.type_, Expr::type_());
        assert_eq!(info.value, Some(Expr::prop()));
    }
}

/// Negative control: the same layout with a base that declares `Layout.public` alone, so the
/// server part's `Layout.server` is a name the part `lean` reads does not declare. Refused by
/// name (`ImportError::MisplacedDeclaration`, R113).
#[test]
fn payload_companion_only_name_is_refused() {
    let (dir, _) = layout_dir(&["Layout.public"]);
    let err = crate::load_module_with_deps(
        &mut Environment::default(),
        "Layout",
        &[dir.path().to_path_buf()],
    )
    .expect_err("a companion-only name is refused");
    assert!(
        matches!(
            err,
            crate::ImportError::MisplacedDeclaration {
                part: ".olean.server",
                authoritative: ".olean",
                ref name,
                ..
            } if name == "Layout.server"
        ),
        "{err}"
    );
}

#[test]
fn empty_payload_companions_and_absent_server_keep_valid_layout() {
    let empty = CleanPayload::default();
    let public = base(&empty, &[]);
    let server = successor(&public, &empty, &[]);
    let private = successor(&server, &empty, &[]);
    assert_follows(&public, &server);
    assert_follows(&server, &private);
    let dir = tempfile::TempDir::new().expect("owned fixture directory");
    std::fs::write(dir.path().join("Empty.olean"), &public).unwrap();
    std::fs::write(dir.path().join("Empty.olean.server"), &server).unwrap();
    std::fs::write(dir.path().join("Empty.olean.private"), &private).unwrap();
    let mut env = Environment::default();
    let summaries =
        crate::load_module_with_deps(&mut env, "Empty", &[dir.path().to_path_buf()]).unwrap();
    assert_eq!(summaries.len(), 3);
    assert!(summaries.iter().all(|summary| summary.added_constants == 0));

    // No server file is required: the private part can directly follow base.
    let private_only = successor(&public, &empty, &[]);
    std::fs::write(dir.path().join("NoServer.olean"), &public).unwrap();
    std::fs::write(dir.path().join("NoServer.olean.private"), &private_only).unwrap();
    let summaries =
        crate::load_module_with_deps(&mut env, "NoServer", &[dir.path().to_path_buf()]).unwrap();
    assert_eq!(summaries.len(), 2);
}

#[test]
fn incremental_import_still_refuses_old_default_base_overlap() {
    let bytes = base(&CleanPayload::default(), &[]);
    let dir = tempfile::TempDir::new().expect("owned fixture directory");
    std::fs::write(dir.path().join("Overlap.olean"), &bytes).unwrap();
    std::fs::write(dir.path().join("Overlap.olean.private"), &bytes).unwrap();
    let mut env = Environment::default();
    let error = crate::load_module_with_deps(&mut env, "Overlap", &[dir.path().to_path_buf()])
        .expect_err("independent default-base parts still overlap");
    assert!(
        error.to_string().contains("incremental region overlap"),
        "{error}"
    );
}

#[test]
fn companion_export_refuses_bad_header_alignment_and_extents_without_panicking() {
    let empty = CleanPayload::default();
    let bytes = base(&empty, &[]);
    for input in [&[][..], &bytes[..HEADER_SIZE]] {
        assert!(
            OleanExporter::export_with_payload_after(input, &[], &[], &[], HASH, &empty).is_err()
        );
    }
    // These are malformed predecessor controls only, never accepted fixture
    // construction: force predecessor, alignment, and output-only overflows.
    // `u64::MAX` aligned DOWN to the 8-byte grid. Spelled `!7` rather than
    // `u64::MAX & !7`: `u64::MAX` is all ones, so that mask is vacuous and
    // clippy rejects it -- the value is identical, 0xFFFF_FFFF_FFFF_FFF8.
    let maximum_aligned = !7u64;
    let output_overflow_base = maximum_aligned - ((bytes.len() as u64 + 7) & !7);
    for address in [1, maximum_aligned, output_overflow_base] {
        let mut malformed = bytes.clone();
        malformed[48..56].copy_from_slice(&address.to_le_bytes());
        let error =
            OleanExporter::export_with_payload_after(&malformed, &[], &[], &[], HASH, &empty)
                .expect_err(
                    "malformed or overflowing predecessor must refuse before writing pointers",
                );
        assert!(matches!(error, crate::error::OleanError::Region(_)));
    }
    let mut wrong_hash = bytes.clone();
    wrong_hash[6] = b'2';
    assert!(
        OleanExporter::export_with_payload_after(&wrong_hash, &[], &[], &[], HASH, &empty).is_err()
    );
    // A v2 predecessor's format/flags cannot be silently reinterpreted as the
    // v1 format emitted by this payload exporter, even with a matching hash.
    for flags in [0, 1] {
        let mut v2 = vec![0; HEADER_SIZE_V2 + 8];
        v2[..5].copy_from_slice(b"olean");
        v2[5] = 2;
        v2[6] = flags;
        v2[7..10].copy_from_slice(b"4.0");
        v2[40..80].copy_from_slice(HASH.as_bytes());
        v2[80..88].copy_from_slice(&0x10000u64.to_le_bytes());
        assert!(
            OleanExporter::export_with_payload_after(&v2, &[], &[], &[], HASH, &empty).is_err()
        );
    }
}

#[test]
fn aligned_zero_base_is_a_valid_predecessor_address() {
    let mut exporter = OleanExporter::with_base_addr(0);
    let module = exporter.write_module_data(&[], &[], &[]);
    exporter.set_root(module);
    let public = exporter.finalize(HASH).expect("valid zero-base module");
    let private = successor(&public, &CleanPayload::default(), &[]);
    assert_follows(&public, &private);
    let dir = tempfile::TempDir::new().expect("owned fixture directory");
    std::fs::write(dir.path().join("Zero.olean"), &public).unwrap();
    std::fs::write(dir.path().join("Zero.olean.private"), &private).unwrap();
    let mut env = Environment::default();
    let summaries =
        crate::load_module_with_deps(&mut env, "Zero", &[dir.path().to_path_buf()]).unwrap();
    assert_eq!(summaries.len(), 2);
}
