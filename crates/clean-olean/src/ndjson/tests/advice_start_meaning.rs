// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! PR-70 measures the canonical library over four archived exports of one checker definition.
//! Reading the NDJSON structural tier supplies metadata to the digest. The separate pinned
//! Lean comparison checks the submitted type and body in the unchanged resident environment.

use crate::meaning_digest::{MeaningDigests, Package};
use crate::ndjson::load::load_export;
use crate::ndjson::source::NdjsonSource;
use crate::{read_artifact, ArtifactDepth};
use clean_kernel::Name;
use flate2::read::GzDecoder;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::io::{Cursor, Read};
use std::path::Path;

fn uncompress(path: &Path) -> Vec<u8> {
    let file = std::fs::File::open(path).expect("open archived input");
    let mut bytes = Vec::new();
    GzDecoder::new(file)
        .read_to_end(&mut bytes)
        .expect("read complete archived input");
    bytes
}

fn hex(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn observation(bytes: &[u8], package: &Package, root: &Name) -> Value {
    let source = NdjsonSource::as_written(Cursor::new(bytes)).expect("export header");
    let loaded = load_export(source).expect("read export into its structural environment");
    let digests = MeaningDigests::new(&loaded.env, package);
    let reachable = digests
        .closure(root)
        .expect("every reachable package name is resident");
    let mut records = BTreeMap::new();
    for name in &reachable {
        assert!(
            !loaded.refused.contains_key(name),
            "structural refusal for {name}"
        );
        assert!(
            !loaded.not_replayable.contains_key(name),
            "unreplayable {name}"
        );
        // Isolate each constant's own record under a singleton inventory, for comparison
        // only. The reported package digest below uses the complete module inventory.
        let singleton = Package::of_names(BTreeSet::from([name.clone()]));
        let local = MeaningDigests::new(&loaded.env, &singleton);
        records.insert(
            name.to_unambiguous_string(),
            local.digest(name).expect("own record"),
        );
    }
    let constant = loaded.env.get_const(root).expect("real root");
    let refusals: BTreeMap<_, _> = loaded
        .refused
        .iter()
        .map(|(name, reason)| (name.to_unambiguous_string(), reason))
        .collect();
    json!({
        "input_sha256": hex(bytes),
        "digest": digests.digest(root).expect("canonical package digest"),
        "root_is_reducible": constant.is_reducible,
        "root_reducibility": format!("{:?}", constant.reducibility),
        "reachable_singleton_digests": records,
        "structural_refusals_in_stream": refusals.len(),
        "structural_refusals": refusals,
        "unreplayable_in_stream": loaded.not_replayable.len()
    })
}

#[test]
fn original_advice_start_module_meanings() {
    let report =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../reports/self-proof-w3-advice-start");
    let bytes = uncompress(&report.join("canonical/Token.olean.gz"));
    assert_eq!(
        hex(&bytes),
        "0eff27371b8500fea76d40fd55be52664b64b301b13ee0c1a649477ca95e2963"
    );
    let dir = tempfile::tempdir().expect("private artifact directory");
    let olean = dir.path().join("Token.olean");
    std::fs::write(&olean, &bytes).expect("materialize unchanged Lean output");
    let artifact =
        read_artifact("KCheck.Token", &olean, ArtifactDepth::Names).expect("module-owned names");
    let package = Package::of_module_names([("KCheck.Token".to_owned(), artifact.names)]);
    let inventory: Vec<_> = package
        .names()
        .iter()
        .map(Name::to_unambiguous_string)
        .collect();
    let root = Name::from_string("KCheck.Advice.start");
    let mut subjects = BTreeMap::new();
    for label in ["resident", "original", "changed_result", "changed_type"] {
        let stream = uncompress(&report.join(format!("{label}.ndjson.gz")));
        subjects.insert(label, observation(&stream, &package, &root));
        if label == "original" {
            // A separate diagnostic changes only the observed regular height in the
            // exact original definition row, leaving all other export bytes intact.
            assert_eq!(
                hex(&stream),
                "83e08b3eec1f2f3e602a3b3b47785034af44a9aa168372e4584409b52c24d13e"
            );
            let text = std::str::from_utf8(&stream).expect("wire text");
            let row = r#"{"def":{"all":[77],"hints":{"regular":1},"levelParams":[],"name":77,"safety":"safe","type":779,"value":788}}"#;
            assert_eq!(text.lines().filter(|line| *line == row).count(), 1);
            let changed = text.replace(row, &row.replace("regular\":1", "regular\":2"));
            assert_eq!(
                stream
                    .iter()
                    .zip(changed.bytes())
                    .filter(|(a, b)| **a != *b)
                    .count(),
                1
            );
            subjects.insert(
                "root_height_control",
                observation(changed.as_bytes(), &package, &root),
            );
        }
    }
    println!(
        "PR70_MEANINGS={}",
        json!({"module": "KCheck.Token","inventory":inventory,
             "token_olean_sha256":hex(&bytes),"subjects": subjects})
    );
}
