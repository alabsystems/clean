// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The TrustCore launch receipts, read through the EV0 digest check in
//! `clean-evidence` (the same check the standalone `clean-evidence` binary
//! runs). These records pin their input digests, so freshness is decided.

use super::reading::{FreshnessReading, Outcome, Reading};
use crate::EvidenceCheckError;
use clean_evidence::trustcore;
use serde_json::json;
use std::path::Path;

pub(super) const TRUSTCORE_FIGURE: &str = "evidence.trustcore_receipts";
pub(super) const TRUSTCORE_INPUTS: &[&str] = &[
    "reports/kernel-soundness-launch-evidence.json",
    "reports/deny-sorry-launch-evidence.json",
    "reports/axiom-audit-launch-evidence.json",
    trustcore::MODULE_FILE,
    trustcore::MODULE_TREE_KEY,
    trustcore::DIGEST_SOURCE,
    trustcore::DIGEST_MODULE_SOURCE,
];

pub(super) fn read(root: &Path) -> Result<Outcome, EvidenceCheckError> {
    let checked = trustcore::check(root)
        .map_err(|error| EvidenceCheckError::Unavailable(error.to_string()))?;
    let findings: Vec<String> = checked.findings.iter().map(ToString::to_string).collect();
    let freshness = if findings.is_empty() {
        FreshnessReading::fresh("every receipt pins the current source digests")
    } else {
        FreshnessReading::stale(findings.join("; "))
    };
    let mut reading = Reading::new(
        json!({"stale_findings": findings.len()}),
        format!(
            "{} stale finding(s) across the three TrustCore receipts",
            findings.len()
        ),
        freshness,
    );
    reading.labels = vec![format!(
        "module tree {} sha256 {}",
        trustcore::MODULE_TREE_KEY,
        checked.tree_sha256
    )];
    reading.non_claims = vec![
        "a fresh receipt says its pinned sources are current, not that its verdict is right"
            .to_owned(),
    ];
    Ok(Outcome::Measured(Box::new(reading)))
}
