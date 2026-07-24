// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Metamath database import and RPN proof verification.

use super::*;
use crate::types::{AxiomProfile, SourceSystem, TrustLevel};

const MOCK_DATABASE: &str = "\
$( Database: test.mm $)
$( File: test.mm $)
ax-mp $a |- ( ph -> ps ) $.
ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
ax-3 $a |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $.
mp2 $p |- ps $= ax-mp ax-1 $.
id $p |- ( ph -> ph ) $= ax-mp ax-1 ax-1 $.
";

const MOCK_MINIMAL_DB: &str = "\
$( Database: minimal.mm $)
ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
thm1 $p |- ( ph -> ph ) $= ax-1 ax-1 $.
";

/// A well-formed Metamath database with complete declarations for RPN
/// verification: constants, variables, floating hypotheses, axioms, theorem.
/// This is a minimal demo0-style database.
const VERIFIABLE_DB: &str = "\
$( Database: demo0.mm $)
$c 0 + = -> ( ) term wff |- $.
$v t r s P Q $.
tt $f term t $.
tr $f term r $.
ts $f term s $.
wp $f wff P $.
wq $f wff Q $.
tze $a term 0 $.
tpl $a term ( t + r ) $.
weq $a wff t = r $.
wim $a wff ( P -> Q ) $.
a1 $a |- ( t = r -> ( t = s -> r = s ) ) $.
a2 $a |- ( t + 0 ) = t $.
${
    min $e |- P $.
    maj $e |- ( P -> Q ) $.
    mp $a |- Q $.
$}
th1 $p |- t = t $= tt tze tpl tt weq tt tt weq tt a2 tt tze tpl tt weq tt tze tpl tt weq tt tt weq wim tt a2 tt tze tpl tt tt a1 mp mp $.
";

#[test]
fn test_import_database_parses_statements() {
    let importer = MetamathImporter::new();
    let db = importer.import_database(MOCK_DATABASE).unwrap();

    assert_eq!(db.name, "test.mm");
    assert_eq!(db.source_file.as_deref(), Some("test.mm"));
    assert_eq!(db.axiom_count(), 3);
    assert_eq!(db.theorem_count(), 2);
    assert_eq!(db.statement_count(), 5);
}

#[test]
fn test_import_database_axiom_labels() {
    let importer = MetamathImporter::new();
    let db = importer.import_database(MOCK_DATABASE).unwrap();

    assert_eq!(db.axiom_labels, vec!["ax-mp", "ax-1", "ax-3"]);
}

#[test]
fn test_import_database_theorem_proof_steps() {
    let importer = MetamathImporter::new();
    let db = importer.import_database(MOCK_DATABASE).unwrap();

    let theorems: Vec<_> = db.statements.iter().filter(|s| s.is_theorem()).collect();
    assert_eq!(theorems.len(), 2);

    match &theorems[0] {
        MetamathStatement::Theorem {
            name, proof_steps, ..
        } => {
            assert_eq!(name, "mp2");
            assert_eq!(proof_steps, &["ax-mp", "ax-1"]);
        }
        other => panic!("expected Theorem, got {other:?}"),
    }
}

#[test]
fn test_import_database_empty_errors() {
    let importer = MetamathImporter::new();
    let result = importer.import_database("");
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        MetamathError::ParseError { .. }
    ));
}

#[test]
fn test_import_database_no_statements_errors() {
    let importer = MetamathImporter::new();
    let result = importer.import_database("$( Just a comment $)");
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        MetamathError::DatabaseError { .. }
    ));
}

#[test]
fn test_import_result_classical_verified() {
    let importer = MetamathImporter::new();
    let db = importer.import_database(MOCK_DATABASE).unwrap();
    let result = importer.import_result(&db);

    assert_eq!(result.name, "test.mm");
    assert_eq!(result.vc_count, 2);
    assert_eq!(result.verified_count, 2);
    assert_eq!(result.axiom_count, 3);
    assert_eq!(result.axiom_profile, AxiomProfile::CLASSICAL);
    assert_eq!(result.trust_level, TrustLevel::AxiomDependent);
    assert_eq!(result.provenance.source, SourceSystem::Metamath);
}

#[test]
fn test_import_result_minimal_verified() {
    let importer = MetamathImporter::new();
    let db = importer.import_database(MOCK_MINIMAL_DB).unwrap();
    let result = importer.import_result(&db);

    assert_eq!(result.vc_count, 1);
    assert_eq!(result.verified_count, 1);
    assert_eq!(result.axiom_profile, AxiomProfile::NONE);
    assert_eq!(result.trust_level, TrustLevel::KernelVerified);
}

#[test]
fn test_import_result_unverified_theorem() {
    // A theorem without proof steps.
    let text = "\
$( Database: partial.mm $)
ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
thm1 $p |- ( ph -> ph ) $.
";
    let importer = MetamathImporter::new();
    let db = importer.import_database(text).unwrap();
    let result = importer.import_result(&db);

    assert_eq!(result.verified_count, 0);
    assert_eq!(result.axiom_profile, AxiomProfile::SMT_ORACLE);
    assert_eq!(result.trust_level, TrustLevel::TrustedOracle);
}

#[test]
fn test_statement_accessors() {
    let axiom = MetamathStatement::Axiom {
        name: "ax-mp".to_string(),
        expression: vec!["|-".to_string()],
    };
    assert_eq!(axiom.name(), "ax-mp");
    assert!(axiom.is_axiom());
    assert!(!axiom.is_theorem());

    let theorem = MetamathStatement::Theorem {
        name: "mp2".to_string(),
        expression: vec!["|-".to_string()],
        proof_steps: vec!["ax-mp".to_string()],
    };
    assert_eq!(theorem.name(), "mp2");
    assert!(!theorem.is_axiom());
    assert!(theorem.is_theorem());
}

#[test]
fn test_classify_database_foundation_classical() {
    let labels = vec!["ax-mp".to_string(), "ax-1".to_string(), "ax-3".to_string()];
    assert_eq!(
        classify_database_foundation(&labels),
        DatabaseFoundation::Classical
    );
}

#[test]
fn test_classify_database_foundation_intuitionistic() {
    let labels = vec!["ax-i1".to_string(), "ax-i2".to_string()];
    assert_eq!(
        classify_database_foundation(&labels),
        DatabaseFoundation::Intuitionistic
    );
}

#[test]
fn test_classify_database_foundation_minimal() {
    let labels = vec!["ax-mp".to_string(), "ax-1".to_string()];
    assert_eq!(
        classify_database_foundation(&labels),
        DatabaseFoundation::Minimal
    );
}

#[test]
fn test_metamath_importer_default() {
    let _importer = MetamathImporter::default();
}

#[test]
fn test_split_at_proof_marker() {
    let tokens = vec![
        "|-".to_string(),
        "ph".to_string(),
        "$=".to_string(),
        "ax-1".to_string(),
        "ax-2".to_string(),
    ];
    let (expr, proof) = split_at_proof_marker(&tokens);
    assert_eq!(expr, vec!["|-", "ph"]);
    assert_eq!(proof, vec!["ax-1", "ax-2"]);
}

#[test]
fn test_split_at_proof_marker_no_proof() {
    let tokens = vec!["|-".to_string(), "ph".to_string()];
    let (expr, proof) = split_at_proof_marker(&tokens);
    assert_eq!(expr, vec!["|-", "ph"]);
    assert!(proof.is_empty());
}

#[test]
fn test_extract_mm_comment_present() {
    let text = "$( Database: set.mm $)\n$( File: set.mm $)";
    assert_eq!(
        extract_mm_comment(text, "Database:"),
        Some("set.mm".to_string())
    );
    assert_eq!(
        extract_mm_comment(text, "File:"),
        Some("set.mm".to_string())
    );
}

#[test]
fn test_extract_mm_comment_missing() {
    assert!(extract_mm_comment("ax-1 $a |- ph $.", "Database:").is_none());
}

// ========================================================================
// import_verified tests (RPN proof replay)
// ========================================================================

#[test]
fn test_import_verified_demo0_succeeds() {
    let importer = MetamathImporter::new();
    let (result, vr) = importer.import_verified(VERIFIABLE_DB).unwrap();

    // th1 should verify
    assert_eq!(vr.verified, 1, "th1 should verify");
    assert_eq!(vr.failed, 0, "no failures expected");
    assert!(vr.axioms > 0, "should have axioms");

    // Trust level should be CertificateReplayed (minimal foundation, all verified).
    assert_eq!(result.trust_level, TrustLevel::CertificateReplayed);
    assert_eq!(result.verified_count, 1);
    assert_eq!(result.provenance.source, SourceSystem::Metamath);
}

#[test]
fn test_import_verified_classical_gets_certificate_replayed() {
    // A verifiable database with ax-3 (classical axiom).
    // Uses the demo0 structure extended with ax-3 for classical detection.
    let db_text = "\
$( Database: classical.mm $)
$c 0 + = -> ( ) term wff |- -. $.
$v t r s P Q $.
tt $f term t $.
tr $f term r $.
ts $f term s $.
wp $f wff P $.
wq $f wff Q $.
tze $a term 0 $.
tpl $a term ( t + r ) $.
weq $a wff t = r $.
wim $a wff ( P -> Q ) $.
wnot $a wff -. P $.
a1 $a |- ( t = r -> ( t = s -> r = s ) ) $.
a2 $a |- ( t + 0 ) = t $.
ax-3 $a |- ( ( -. P -> -. Q ) -> ( Q -> P ) ) $.
${
    min $e |- P $.
    maj $e |- ( P -> Q ) $.
    mp $a |- Q $.
$}
th1 $p |- t = t $= tt tze tpl tt weq tt tt weq tt a2 tt tze tpl tt weq tt tze tpl tt weq tt tt weq wim tt a2 tt tze tpl tt tt a1 mp mp $.
";
    let importer = MetamathImporter::new();
    let (result, vr) = importer.import_verified(db_text).unwrap();

    assert_eq!(
        vr.verified, 1,
        "th1 should verify, failed: {:?}",
        vr.failed_labels
    );
    assert_eq!(vr.failed, 0);
    // Classical foundation (ax-3 present) + all proofs verified = CertificateReplayed
    assert_eq!(result.trust_level, TrustLevel::CertificateReplayed);
    assert_eq!(result.axiom_profile, AxiomProfile::CLASSICAL);
}

#[test]
fn test_import_verified_empty_text_errors() {
    let importer = MetamathImporter::new();
    let result = importer.import_verified("");
    assert!(result.is_err());
}

#[test]
fn test_import_verified_diagnostics_contain_rpn_info() {
    let importer = MetamathImporter::new();
    let (result, _) = importer.import_verified(VERIFIABLE_DB).unwrap();

    // Diagnostics should mention RPN verification.
    let has_rpn = result
        .diagnostics
        .iter()
        .any(|d| d.contains("RPN verified"));
    assert!(
        has_rpn,
        "diagnostics should contain RPN info: {:?}",
        result.diagnostics
    );
}

#[test]
fn test_import_verified_from_file_demo0() {
    let demo0_path = concat!(env!("CARGO_MANIFEST_DIR"), "/../../data/raw/demo0.mm");
    let demo0_path = std::path::Path::new(demo0_path);
    if !demo0_path.exists() {
        eprintln!("SKIP: demo0.mm not found at {}", demo0_path.display());
        return;
    }
    let text = std::fs::read_to_string(demo0_path).unwrap();
    let importer = MetamathImporter::new();
    let (result, vr) = importer.import_verified(&text).unwrap();

    assert!(vr.verified > 0, "demo0.mm should have verified theorems");
    assert_eq!(vr.failed, 0, "demo0.mm should have 0 failures");
    assert_eq!(result.trust_level, TrustLevel::CertificateReplayed);
}

#[test]
fn test_import_verified_set_mm() {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../../data/raw/set.mm");
    let path = std::path::Path::new(path);
    if !path.exists() {
        eprintln!("SKIP: set.mm not found");
        return;
    }
    let text = std::fs::read_to_string(path).unwrap();
    let importer = MetamathImporter::new();
    let (result, vr) = importer.import_verified(&text).unwrap();

    eprintln!(
        "set.mm: rpn_verified={}, rpn_failed={}, compressed_skipped={}, trust={:?}",
        vr.verified, vr.failed, vr.compressed_skipped, result.trust_level
    );
    assert_eq!(vr.failed, 0, "set.mm should have 0 RPN failures");
    assert!(
        vr.verified >= 40000,
        "set.mm should have 40K+ verified theorems"
    );
    assert_eq!(result.trust_level, TrustLevel::CertificateReplayed);
    assert_eq!(result.axiom_profile, AxiomProfile::CLASSICAL);
}
