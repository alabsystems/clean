// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Structural-guarantee #2 grep gate (design §3.2 / §4.3): no `f64`/`f32`
//! anywhere in the crate source, and no ` as ` cast outside the audited
//! `bignat.rs`. This is defence-in-depth layered on the crate-level clippy
//! `deny`s in lib.rs.

use clean_ck0::policy::{scan_violations, ViolationKind};
use std::path::PathBuf;

fn src_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src")
}

#[test]
fn test_no_floats_in_seed_source() {
    let violations: Vec<_> = scan_violations(&src_dir())
        .into_iter()
        .filter(|v| v.kind == ViolationKind::Float)
        .collect();
    assert!(
        violations.is_empty(),
        "f64/f32 found in ck0 seed source (forbidden):\n{}",
        violations
            .iter()
            .map(|v| format!("  {}:{}: {}", v.file.display(), v.line_no, v.line))
            .collect::<Vec<_>>()
            .join("\n")
    );
}

#[test]
fn test_no_unaudited_as_casts() {
    let violations: Vec<_> = scan_violations(&src_dir())
        .into_iter()
        .filter(|v| v.kind == ViolationKind::UnauditedCast)
        .collect();
    assert!(
        violations.is_empty(),
        "`as` cast found outside the audited bignat.rs (forbidden):\n{}",
        violations
            .iter()
            .map(|v| format!("  {}:{}: {}", v.file.display(), v.line_no, v.line))
            .collect::<Vec<_>>()
            .join("\n")
    );
}
