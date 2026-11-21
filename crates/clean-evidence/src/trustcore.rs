// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Compare the existing TrustCore launch-evidence records to the current sources.

mod finding;
mod record;

pub use finding::{StalenessFinding, TrustcoreError};
pub use record::{RecordError, FIGURE, GATE_COMMAND, PRODUCER_ID};

use crate::digest::{sha256_file, sha256_module_tree};
use serde_json::Value;
use std::{fs, io, path::Path};

pub const MODULE_FILE: &str = "crates/clean-cli/src/cmd_replacement.rs";
const MODULE_DIR: &str = "crates/clean-cli/src/cmd_replacement";
pub const MODULE_TREE_KEY: &str = "crates/clean-cli/src/cmd_replacement/**/*.rs";
pub const DIGEST_SOURCE: &str = "crates/clean-evidence/src/digest.rs";
pub const DIGEST_MODULE_SOURCE: &str = "crates/clean-evidence/src/lib.rs";
pub const KERNEL_SCHEMA: &str = "clean-kernel-soundness-launch-evidence-v2";
pub const DENY_SORRY_SCHEMA: &str = "clean-deny-sorry-launch-evidence-v2";

/// The three receipts and the schema each must name; the axiom-audit receipt
/// keeps its existing schema, so only its pins are compared.
pub(crate) const ARTIFACTS: [(&str, Option<&str>); 3] = [
    (
        "reports/kernel-soundness-launch-evidence.json",
        Some(KERNEL_SCHEMA),
    ),
    (
        "reports/deny-sorry-launch-evidence.json",
        Some(DENY_SORRY_SCHEMA),
    ),
    ("reports/axiom-audit-launch-evidence.json", None),
];

/// Current input digests and any evidence records that did not match them.
#[derive(Debug)]
#[non_exhaustive]
pub struct StalenessCheck {
    pub file_sha256: String,
    pub tree_sha256: String,
    pub digest_source_sha256: String,
    pub digest_module_sha256: String,
    pub findings: Vec<StalenessFinding>,
}

/// Compare the source-file pin in all three records. The kernel-soundness
/// and deny-sorry receipts also require the v2 schema, module tree and both
/// paths that supply the shared digest. Axiom audit uses its existing schema.
pub fn check(root: &Path) -> Result<StalenessCheck, TrustcoreError> {
    let hash = |input: &'static str, digest: fn(&Path) -> io::Result<String>| {
        digest(&root.join(input)).map_err(|source| TrustcoreError::Hash { input, source })
    };
    let file_sha256 = hash(MODULE_FILE, sha256_file)?;
    let tree_sha256 = hash(MODULE_DIR, sha256_module_tree)?;
    let digest_source_sha256 = hash(DIGEST_SOURCE, sha256_file)?;
    let digest_module_sha256 = hash(DIGEST_MODULE_SOURCE, sha256_file)?;
    let mut findings = Vec::new();
    for (artifact, schema) in ARTIFACTS {
        let source = match fs::read(root.join(artifact))
            .and_then(|bytes| serde_json::from_slice::<Value>(&bytes).map_err(io::Error::other))
        {
            Ok(source) => source,
            Err(error) => {
                findings.push(StalenessFinding::Unreadable {
                    artifact,
                    reason: error.to_string(),
                });
                continue;
            }
        };
        let Some(pins) = source.get("source_sha256").and_then(Value::as_object) else {
            findings.push(StalenessFinding::MissingPinMap { artifact });
            continue;
        };
        compare_pin(artifact, pins, MODULE_FILE, &file_sha256, &mut findings);
        if let Some(expected) = schema {
            if source.get("schema_version").and_then(Value::as_str) != Some(expected) {
                findings.push(StalenessFinding::WrongSchema { artifact, expected });
            }
            for (input, current) in [
                (DIGEST_SOURCE, digest_source_sha256.as_str()),
                (DIGEST_MODULE_SOURCE, digest_module_sha256.as_str()),
            ] {
                compare_pin(artifact, pins, input, current, &mut findings);
            }
        }
        match pins.get(MODULE_TREE_KEY).filter(|pin| !pin.is_null()) {
            None if schema.is_some() => {
                findings.push(StalenessFinding::MissingTreePin { artifact });
            }
            Some(pin) if pin.as_str() != Some(&tree_sha256) => {
                findings.push(StalenessFinding::TreePinMismatch {
                    artifact,
                    pinned: pin_text(pin),
                    current: tree_sha256.clone(),
                });
            }
            _ => {}
        }
    }
    Ok(StalenessCheck {
        file_sha256,
        tree_sha256,
        digest_source_sha256,
        digest_module_sha256,
        findings,
    })
}

fn compare_pin(
    artifact: &'static str,
    pins: &serde_json::Map<String, Value>,
    input: &'static str,
    current: &str,
    findings: &mut Vec<StalenessFinding>,
) {
    match pins.get(input).filter(|pin| !pin.is_null()) {
        None => findings.push(StalenessFinding::MissingPin { artifact, input }),
        Some(pin) if pin.as_str() != Some(current) => {
            findings.push(StalenessFinding::PinMismatch {
                artifact,
                input,
                pinned: pin_text(pin),
                current: current.to_owned(),
            });
        }
        Some(_) => {}
    }
}

fn pin_text(pin: &Value) -> String {
    match pin.as_str() {
        Some(text) => text.to_owned(),
        None => pin.to_string(),
    }
}
