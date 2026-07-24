// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{run_audit_in, AuditSeverity};
use std::fs;
use std::path::Path;
use tempfile::TempDir;

fn fixture(extra_manifest: &str, lib_rs: &str, extras: &[(&str, &str)]) -> TempDir {
    let dir = tempfile::tempdir().expect("tempdir");
    fs::create_dir_all(dir.path().join("src")).expect("src dir");
    fs::write(
        dir.path().join("Cargo.toml"),
        format!(
            "[package]\nname = \"fixture\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n{extra_manifest}"
        ),
    )
    .expect("manifest");
    fs::write(dir.path().join("src/lib.rs"), lib_rs).expect("lib");
    for (path, contents) in extras {
        write_file(dir.path(), path, contents);
    }
    dir
}

fn write_file(root: &Path, relative: &str, contents: &str) {
    let path = root.join(relative);
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).expect("parent");
    }
    fs::write(path, contents).expect("write fixture");
}

#[test]
fn clean_fixture_reports_only_info_findings() {
    let dir = fixture(
        "",
        r#"// Copyright 2026 Andrew Yates
// Author: Test
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

/// clean demo type.
#[non_exhaustive]
pub enum ReadyStatus {
    Ready,
}

/// clean demo function.
pub fn audit_entrypoint() {}
"#,
        &[(
            "tests/smoke.rs",
            r#"// Copyright 2026 Andrew Yates
// Author: Test
// SPDX-License-Identifier: Apache-2.0

#[test]
fn smoke() {}
"#,
        )],
    );

    let report = run_audit_in(dir.path());
    for findings in [
        report.license_compliance,
        report.dependency_audit,
        report.api_stability,
        report.documentation_coverage,
        report.security_review,
    ] {
        assert_eq!(findings.len(), 1);
        assert_eq!(findings[0].severity, AuditSeverity::Info);
    }
}

#[test]
fn audit_flags_missing_header_and_missing_safety_comment() {
    let dir = fixture(
        "",
        r#"#![cfg_attr(test, allow(dead_code))]

pub fn needs_review() {
    let _value = unsafe { 42usize };
}
"#,
        &[],
    );

    let report = run_audit_in(dir.path());
    assert!(report.license_compliance.iter().any(|finding| {
        finding.severity == AuditSeverity::Critical
            && finding.message.contains("missing Apache-2.0")
    }));
    assert!(report.security_review.iter().any(|finding| {
        finding.severity == AuditSeverity::Critical
            && finding.message.contains("missing a nearby SAFETY comment")
    }));
}

#[test]
fn audit_distinguishes_runtime_and_dev_internal_dependencies() {
    let dir = fixture(
        "[dependencies]\nclean-elab.workspace = true\n\n[dev-dependencies]\nclean-parser.workspace = true\n",
        r#"// Copyright 2026 Andrew Yates
// Author: Test
// SPDX-License-Identifier: Apache-2.0

/// Documented item.
#[non_exhaustive]
pub struct Ready;
"#,
        &[],
    );

    let report = run_audit_in(dir.path());
    assert!(report.dependency_audit.iter().any(|finding| {
        finding.severity == AuditSeverity::Critical && finding.message.contains("clean-elab")
    }));
    assert!(report.dependency_audit.iter().any(|finding| {
        finding.severity == AuditSeverity::Warning && finding.message.contains("clean-parser")
    }));
}

#[test]
fn audit_flags_undocumented_and_non_exhaustive_gaps() {
    let dir = fixture(
        "",
        r#"// Copyright 2026 Andrew Yates
// Author: Test
// SPDX-License-Identifier: Apache-2.0

pub enum PublicApi {
    Ready,
}
"#,
        &[],
    );

    let report = run_audit_in(dir.path());
    assert!(report.documentation_coverage.iter().any(|finding| {
        finding.severity == AuditSeverity::Warning
            && finding
                .message
                .contains("public enum `PublicApi` is undocumented")
    }));
    assert!(report.api_stability.iter().any(|finding| {
        finding.severity == AuditSeverity::Warning
            && finding
                .message
                .contains("should consider #[non_exhaustive]")
    }));
}
