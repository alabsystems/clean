// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The opt-in subject export of the self-proof qualification tests: when the
//! runner under `reports/` sets the test's `CLEAN_*_EXPORT_PATH`, the owned
//! subject's dependency cone is written there as an NDJSON export (for the
//! quorum's other checkers) and its summary is printed on stderr as
//! `<label>: <json>`. The capture is a diagnostic beside the test, never part
//! of its subject: every assertion of the including test runs whether or not
//! the variable is set, which is why the conditional lives here and not in a
//! test body (`scripts/check_self_skipping_tests.py`).
//!
//! Included through `#[path]` by `cic_l_level_order.rs`, `cic_l_level_scope.rs`,
//! `cic_l_universe_translation.rs`, `kcheck_inference_complete.rs`,
//! `kcheck_nat_acceptance.rs` and `kcheck_static_complete.rs`.

use std::collections::BTreeSet;

use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_olean::ndjson::{write_export, ExportWriteMeta};

/// Writes `targets`' cone out of `loaded` to the path in `var`, if it is set,
/// and prints `<label>: <summary>`; does nothing when `var` is unset. A failed
/// capture fails the test.
pub fn capture_if_requested(
    var: &str,
    label: &str,
    loaded: &Environment,
    targets: &BTreeSet<Name>,
) {
    let Some(path) = std::env::var_os(var) else {
        return;
    };
    let bytes = std::fs::File::create(path).expect("owned export capture");
    let summary = write_export(
        loaded,
        targets,
        &ExportWriteMeta {
            lean_version: "4.30.0-rc2".to_owned(),
            lean_githash: "3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc".to_owned(),
        },
        std::io::BufWriter::new(bytes),
    )
    .expect("exact owned subject dependency export");
    eprintln!(
        "{label}: {}",
        serde_json::to_string(&summary).expect("export identity")
    );
}
