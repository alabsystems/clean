// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the HOL Light / HOL4 OpenTheory bridge.

use clean_kernel::open_theory::parse_article;
use clean_kernel::{ExprKind, Name as LeanName};

use crate::types::{AxiomProfile, SourceSystem, TrustLevel};

use super::cross_system::{HolUnifier, UnifierStatistics};
use super::error::HolError;
use super::hol4::{Hol4Importer, Hol4Statistics, Hol4Theory};
use super::hol_light::{HolLightImporter, HolLightStatistics, HolLightTheory};
use super::opentheory_bridge::{
    ImportStatistics, ImportedConstantKind, MathverseImportedConstant, OtMathverseBridge,
    HOL_BASE_PROFILE,
};

/// Minimal OpenTheory article proving `x = x` via `refl`.
/// Exports one theorem with no assumptions. Borrowed from kernel tests.
const REFL_ARTICLE: &str = r#"
6
version
"x"
"A"
varType
3
def
var
1
def
varTerm
2
def
refl
4
def
"bool"
typeOp
nil
opType
5
def
"->"
typeOp
3
ref
5
ref
nil
cons
cons
opType
6
def
"->"
typeOp
3
ref
6
ref
nil
cons
cons
opType
7
def
"="
const
7
ref
constTerm
2
ref
appTerm
2
ref
appTerm
8
def
4
ref
nil
8
ref
thm
"#;

/// Article with an assumption: `assume p` pushes `{p} |- p`, `thm` exports it.
const ASSUME_ARTICLE: &str = r#"
6
version
"p"
"bool"
typeOp
nil
opType
1
def
var
varTerm
2
def
assume
3
def
3
ref
2
ref
nil
cons
2
ref
thm
"#;

/// Article with a named constant `foo : A -> bool`.
const CONST_ARTICLE: &str = r#"
6
version
"x"
"A"
varType
3
def
var
1
def
varTerm
2
def
refl
4
def
"bool"
typeOp
nil
opType
5
def
"->"
typeOp
3
ref
5
ref
nil
cons
cons
opType
6
def
"->"
typeOp
3
ref
6
ref
nil
cons
cons
opType
7
def
"="
const
7
ref
constTerm
2
ref
appTerm
2
ref
appTerm
8
def
4
ref
nil
8
ref
thm
"#;

// ============================================================================
// Axiom Profile Tests
// ============================================================================

#[test]
fn test_hol_base_profile_has_classical() {
    assert!(HOL_BASE_PROFILE.contains(AxiomProfile::CLASSICAL));
}

#[test]
fn test_hol_base_profile_has_extensionality() {
    assert!(HOL_BASE_PROFILE.contains(AxiomProfile::EXTENSIONALITY));
}

#[test]
fn test_hol_base_profile_has_hol_embedding() {
    assert!(HOL_BASE_PROFILE.contains(AxiomProfile::HOL_EMBEDDING));
}

#[test]
fn test_hol_base_profile_does_not_have_univalence() {
    // CHOICE==CLASSICAL (same bit), so test with UNIVALENCE instead
    assert!(!HOL_BASE_PROFILE.contains(AxiomProfile::UNIVALENCE));
}

#[test]
fn test_hol_base_profile_does_not_have_mizar() {
    assert!(!HOL_BASE_PROFILE.contains(AxiomProfile::MIZAR_SOFT_TYPE));
}

#[test]
fn test_hol_base_profile_does_not_have_coq() {
    assert!(!HOL_BASE_PROFILE.contains(AxiomProfile::COQ_SPROP));
}

#[test]
fn test_hol_base_profile_is_not_kernel_verified() {
    assert!(!HOL_BASE_PROFILE.is_kernel_verified());
}

#[test]
fn test_hol_base_profile_axiom_count_is_three() {
    assert_eq!(HOL_BASE_PROFILE.axiom_count(), 3);
}

// ============================================================================
// OpenTheory Bridge Tests
// ============================================================================

#[test]
fn test_bridge_imports_refl_article_one_theorem() {
    let article = parse_article(REFL_ARTICLE).expect("article should parse");
    let bridge = OtMathverseBridge::new(LeanName::from_string("Test.OT"), SourceSystem::HolLight);
    let (constants, stats) = bridge
        .import_article(&article)
        .expect("bridge import should succeed");

    assert_eq!(stats.theorem_count, 1);
    assert_eq!(stats.assumption_count, 0);
    assert_eq!(stats.support_count, 0);
    assert_eq!(constants.len(), 1);
}

#[test]
fn test_bridge_theorem_has_correct_kind() {
    let article = parse_article(REFL_ARTICLE).expect("article should parse");
    let bridge = OtMathverseBridge::new(LeanName::from_string("Test.OT"), SourceSystem::HolLight);
    let (constants, _) = bridge
        .import_article(&article)
        .expect("bridge import should succeed");

    assert_eq!(constants[0].kind, ImportedConstantKind::Theorem);
}

#[test]
fn test_bridge_theorem_has_hol_axiom_profile() {
    let article = parse_article(REFL_ARTICLE).expect("article should parse");
    let bridge = OtMathverseBridge::new(LeanName::from_string("Test.OT"), SourceSystem::HolLight);
    let (constants, _) = bridge
        .import_article(&article)
        .expect("bridge import should succeed");

    let c = &constants[0];
    assert!(c.axiom_profile.contains(AxiomProfile::CLASSICAL));
    assert!(c.axiom_profile.contains(AxiomProfile::EXTENSIONALITY));
    assert!(c.axiom_profile.contains(AxiomProfile::HOL_EMBEDDING));
    assert_eq!(c.axiom_profile, HOL_BASE_PROFILE);
}

#[test]
fn test_bridge_theorem_type_is_pi() {
    let article = parse_article(REFL_ARTICLE).expect("article should parse");
    let bridge = OtMathverseBridge::new(LeanName::from_string("Test.OT"), SourceSystem::HolLight);
    let (constants, _) = bridge
        .import_article(&article)
        .expect("bridge import should succeed");

    // The refl theorem should produce a Pi type (universally quantified).
    assert!(
        matches!(constants[0].type_expr.kind(), ExprKind::Pi(_, _, _)),
        "expected Pi type, got {:?}",
        constants[0].type_expr.kind()
    );
}

#[test]
fn test_bridge_theorem_trust_level_is_certificate_replayed() {
    let article = parse_article(REFL_ARTICLE).expect("article should parse");
    let bridge = OtMathverseBridge::new(LeanName::from_string("Test.OT"), SourceSystem::HolLight);
    let (constants, _) = bridge
        .import_article(&article)
        .expect("bridge import should succeed");

    assert_eq!(constants[0].trust_level, TrustLevel::CertificateReplayed);
}

#[test]
fn test_bridge_imports_assume_article_with_assumption() {
    let article = parse_article(ASSUME_ARTICLE).expect("article should parse");
    let bridge = OtMathverseBridge::new(LeanName::from_string("Test.OT"), SourceSystem::HolLight);
    let (constants, stats) = bridge
        .import_article(&article)
        .expect("bridge import should succeed");

    // Assumption `p` is in the exported hypothesis list (OpenTheory spec).
    assert_eq!(stats.theorem_count, 1);
    assert!(stats.total() >= 1);

    // All imported constants should have the HOL base profile.
    for c in &constants {
        assert_eq!(c.axiom_profile, HOL_BASE_PROFILE);
    }
}

// ============================================================================
// Provenance Tracking Tests
// ============================================================================

#[test]
fn test_bridge_provenance_source_hol_light() {
    let article = parse_article(REFL_ARTICLE).expect("article should parse");
    let bridge = OtMathverseBridge::new(LeanName::from_string("Test.OT"), SourceSystem::HolLight);
    let (constants, _) = bridge
        .import_article(&article)
        .expect("bridge import should succeed");

    assert_eq!(constants[0].provenance.source, SourceSystem::HolLight);
}

#[test]
fn test_bridge_provenance_source_hol4() {
    let article = parse_article(REFL_ARTICLE).expect("article should parse");
    let bridge = OtMathverseBridge::new(LeanName::from_string("Test.OT"), SourceSystem::Hol4);
    let (constants, _) = bridge
        .import_article(&article)
        .expect("bridge import should succeed");

    assert_eq!(constants[0].provenance.source, SourceSystem::Hol4);
}

#[test]
fn test_bridge_provenance_has_original_name() {
    let article = parse_article(REFL_ARTICLE).expect("article should parse");
    let bridge = OtMathverseBridge::new(LeanName::from_string("Test.OT"), SourceSystem::HolLight);
    let (constants, _) = bridge
        .import_article(&article)
        .expect("bridge import should succeed");

    // The kernel names it "Test.OT.theorem.0".
    assert!(
        !constants[0].provenance.original_name.is_empty(),
        "original_name should not be empty"
    );
}

#[test]
fn test_bridge_provenance_source_file_none_by_default() {
    let article = parse_article(REFL_ARTICLE).expect("article should parse");
    let bridge = OtMathverseBridge::new(LeanName::from_string("Test.OT"), SourceSystem::HolLight);
    let (constants, _) = bridge
        .import_article(&article)
        .expect("bridge import should succeed");

    assert_eq!(constants[0].provenance.source_file, None);
}

#[test]
fn test_bridge_provenance_source_file_when_set() {
    let article = parse_article(REFL_ARTICLE).expect("article should parse");
    let bridge = OtMathverseBridge::new(LeanName::from_string("Test.OT"), SourceSystem::HolLight)
        .with_source_file("/path/to/refl.art");
    let (constants, _) = bridge
        .import_article(&article)
        .expect("bridge import should succeed");

    assert_eq!(
        constants[0].provenance.source_file,
        Some("/path/to/refl.art".to_owned())
    );
}

#[test]
fn test_bridge_provenance_axiom_profile_matches_constant() {
    let article = parse_article(REFL_ARTICLE).expect("article should parse");
    let bridge = OtMathverseBridge::new(LeanName::from_string("Test.OT"), SourceSystem::HolLight);
    let (constants, _) = bridge
        .import_article(&article)
        .expect("bridge import should succeed");

    // The provenance axiom_profile should match the constant's own profile.
    assert_eq!(
        constants[0].provenance.axiom_profile,
        constants[0].axiom_profile
    );
}

// ============================================================================
// Statistics Tests
// ============================================================================

#[test]
fn test_statistics_refl_article() {
    let article = parse_article(REFL_ARTICLE).expect("article should parse");
    let bridge = OtMathverseBridge::new(LeanName::from_string("Test.OT"), SourceSystem::HolLight);
    let (_, stats) = bridge
        .import_article(&article)
        .expect("bridge import should succeed");

    assert_eq!(stats.theorem_count, 1);
    assert_eq!(stats.assumption_count, 0);
    assert_eq!(stats.total(), stats.support_count + 1);
}

#[test]
fn test_statistics_default_is_zeroed() {
    let stats = ImportStatistics::default();
    assert_eq!(stats.support_count, 0);
    assert_eq!(stats.assumption_count, 0);
    assert_eq!(stats.theorem_count, 0);
    assert_eq!(stats.total(), 0);
}

// ============================================================================
// HOL Light Importer Tests
// ============================================================================

#[test]
fn test_hol_light_import_text_produces_hol_light_provenance() {
    let importer = HolLightImporter::default();
    let (constants, stats) = importer
        .import_text(REFL_ARTICLE)
        .expect("HOL Light import should succeed");

    assert_eq!(stats.theorem_count, 1);
    for c in &constants {
        assert_eq!(c.provenance.source, SourceSystem::HolLight);
        assert_eq!(c.axiom_profile, HOL_BASE_PROFILE);
    }
}

#[test]
fn test_hol_light_import_text_namespace() {
    let importer = HolLightImporter::default();
    let (constants, _) = importer
        .import_text(REFL_ARTICLE)
        .expect("HOL Light import should succeed");

    // All names should be prefixed with "HolLight.Imported".
    for c in &constants {
        let name_str = c.name.to_string();
        assert!(
            name_str.starts_with("HolLight.Imported"),
            "expected HolLight.Imported prefix, got: {name_str}"
        );
    }
}

#[test]
fn test_hol_light_custom_namespace() {
    let importer = HolLightImporter::with_namespace("MyLib.HOL");
    let (constants, _) = importer
        .import_text(REFL_ARTICLE)
        .expect("HOL Light import should succeed");

    for c in &constants {
        let name_str = c.name.to_string();
        assert!(
            name_str.starts_with("MyLib.HOL"),
            "expected MyLib.HOL prefix, got: {name_str}"
        );
    }
}

#[test]
fn test_hol_light_directory_import_no_art_files() {
    let dir = tempfile::tempdir().expect("should create tempdir");
    let importer = HolLightImporter::default();
    let result = importer.import_directory(dir.path());
    assert!(result.is_err());
    match result.unwrap_err() {
        HolError::NoArticlesFound { path } => {
            assert!(path.contains(dir.path().to_str().unwrap()));
        }
        other => panic!("expected NoArticlesFound, got: {other:?}"),
    }
}

#[test]
fn test_hol_light_directory_import_with_art_file() {
    let dir = tempfile::tempdir().expect("should create tempdir");
    let art_path = dir.path().join("refl.art");
    std::fs::write(&art_path, REFL_ARTICLE).expect("should write .art file");

    let importer = HolLightImporter::default();
    let (constants, stats, errors) = importer
        .import_directory(dir.path())
        .expect("directory import should succeed");

    assert!(errors.is_empty(), "expected no errors, got: {errors:?}");
    assert_eq!(stats.theorem_count, 1);
    assert!(!constants.is_empty());
    for c in &constants {
        assert_eq!(c.provenance.source, SourceSystem::HolLight);
    }
}

// ============================================================================
// HOL4 Importer Tests
// ============================================================================

#[test]
fn test_hol4_import_text_produces_hol4_provenance() {
    let importer = Hol4Importer::default();
    let (constants, stats) = importer
        .import_text(REFL_ARTICLE)
        .expect("HOL4 import should succeed");

    assert_eq!(stats.theorem_count, 1);
    for c in &constants {
        assert_eq!(c.provenance.source, SourceSystem::Hol4);
        assert_eq!(c.axiom_profile, HOL_BASE_PROFILE);
    }
}

#[test]
fn test_hol4_import_text_namespace() {
    let importer = Hol4Importer::default();
    let (constants, _) = importer
        .import_text(REFL_ARTICLE)
        .expect("HOL4 import should succeed");

    for c in &constants {
        let name_str = c.name.to_string();
        assert!(
            name_str.starts_with("HOL4.Imported"),
            "expected HOL4.Imported prefix, got: {name_str}"
        );
    }
}

#[test]
fn test_hol4_custom_namespace() {
    let importer = Hol4Importer::with_namespace("MyLib.HOL4");
    let (constants, _) = importer
        .import_text(REFL_ARTICLE)
        .expect("HOL4 import should succeed");

    for c in &constants {
        let name_str = c.name.to_string();
        assert!(
            name_str.starts_with("MyLib.HOL4"),
            "expected MyLib.HOL4 prefix, got: {name_str}"
        );
    }
}

#[test]
fn test_hol4_axiom_profile_same_as_hol_light() {
    let hl_importer = HolLightImporter::default();
    let hol4_importer = Hol4Importer::default();

    let (hl_constants, _) = hl_importer
        .import_text(REFL_ARTICLE)
        .expect("HOL Light import should succeed");
    let (hol4_constants, _) = hol4_importer
        .import_text(REFL_ARTICLE)
        .expect("HOL4 import should succeed");

    // Both systems use the same axiom profile for the same article.
    assert_eq!(
        hl_constants[0].axiom_profile,
        hol4_constants[0].axiom_profile
    );
    assert_eq!(hl_constants[0].axiom_profile, HOL_BASE_PROFILE);
}

#[test]
fn test_hol4_directory_import_no_art_files() {
    let dir = tempfile::tempdir().expect("should create tempdir");
    let importer = Hol4Importer::default();
    let result = importer.import_directory(dir.path());
    assert!(result.is_err());
    match result.unwrap_err() {
        HolError::NoArticlesFound { .. } => {}
        other => panic!("expected NoArticlesFound, got: {other:?}"),
    }
}

#[test]
fn test_hol4_directory_import_with_art_file() {
    let dir = tempfile::tempdir().expect("should create tempdir");
    let art_path = dir.path().join("theorem.art");
    std::fs::write(&art_path, REFL_ARTICLE).expect("should write .art file");

    let importer = Hol4Importer::default();
    let (constants, stats, errors) = importer
        .import_directory(dir.path())
        .expect("directory import should succeed");

    assert!(errors.is_empty(), "expected no errors, got: {errors:?}");
    assert_eq!(stats.theorem_count, 1);
    assert!(!constants.is_empty());
    for c in &constants {
        assert_eq!(c.provenance.source, SourceSystem::Hol4);
    }
}

// ============================================================================
// Cross-System Consistency Tests
// ============================================================================

#[test]
fn test_both_systems_produce_same_type_expressions() {
    let hl_importer = HolLightImporter::with_namespace("Same.NS");
    let hol4_importer = Hol4Importer::with_namespace("Same.NS");

    let (hl_constants, _) = hl_importer
        .import_text(REFL_ARTICLE)
        .expect("HOL Light import");
    let (hol4_constants, _) = hol4_importer
        .import_text(REFL_ARTICLE)
        .expect("HOL4 import");

    // With the same namespace, the type expressions should be identical
    // because they go through the same OpenTheory pipeline.
    assert_eq!(hl_constants.len(), hol4_constants.len());
    for (hl, hol4) in hl_constants.iter().zip(hol4_constants.iter()) {
        assert_eq!(hl.type_expr, hol4.type_expr);
        assert_eq!(hl.name, hol4.name);
    }
}

#[test]
fn test_both_systems_differ_only_in_provenance_source() {
    let hl_importer = HolLightImporter::with_namespace("Same.NS");
    let hol4_importer = Hol4Importer::with_namespace("Same.NS");

    let (hl_constants, _) = hl_importer
        .import_text(REFL_ARTICLE)
        .expect("HOL Light import");
    let (hol4_constants, _) = hol4_importer
        .import_text(REFL_ARTICLE)
        .expect("HOL4 import");

    for (hl, hol4) in hl_constants.iter().zip(hol4_constants.iter()) {
        assert_eq!(hl.provenance.source, SourceSystem::HolLight);
        assert_eq!(hol4.provenance.source, SourceSystem::Hol4);
        // Everything else should match.
        assert_eq!(hl.axiom_profile, hol4.axiom_profile);
        assert_eq!(hl.trust_level, hol4.trust_level);
        assert_eq!(hl.kind, hol4.kind);
    }
}

// ============================================================================
// Bridge Text Import Tests
// ============================================================================

#[test]
fn test_bridge_import_article_text() {
    let bridge = OtMathverseBridge::new(LeanName::from_string("TextTest"), SourceSystem::HolLight);
    let (constants, stats) = bridge
        .import_article_text(REFL_ARTICLE)
        .expect("text import should succeed");

    assert_eq!(stats.theorem_count, 1);
    assert!(!constants.is_empty());
}

#[test]
fn test_bridge_import_invalid_article_text_returns_error() {
    let bridge = OtMathverseBridge::new(LeanName::from_string("TextTest"), SourceSystem::HolLight);
    let result = bridge.import_article_text("not a valid article\n");
    assert!(result.is_err());
}

// ============================================================================
// Directory Import Error Handling Tests
// ============================================================================

#[test]
fn test_directory_import_multiple_files() {
    let dir = tempfile::tempdir().expect("should create tempdir");

    // Write two valid articles.
    std::fs::write(dir.path().join("a.art"), REFL_ARTICLE).expect("write a.art");
    std::fs::write(dir.path().join("b.art"), REFL_ARTICLE).expect("write b.art");

    let importer = HolLightImporter::default();
    let (constants, stats, errors) = importer
        .import_directory(dir.path())
        .expect("directory import should succeed");

    assert!(errors.is_empty());
    assert_eq!(stats.theorem_count, 2);
    assert!(constants.len() >= 2);
}

#[test]
fn test_directory_import_skips_non_art_files() {
    let dir = tempfile::tempdir().expect("should create tempdir");

    std::fs::write(dir.path().join("notes.txt"), "not an article").expect("write notes.txt");
    std::fs::write(dir.path().join("thm.art"), REFL_ARTICLE).expect("write thm.art");

    let importer = HolLightImporter::default();
    let (constants, stats, errors) = importer
        .import_directory(dir.path())
        .expect("directory import should succeed");

    assert!(errors.is_empty());
    assert_eq!(stats.theorem_count, 1);
    assert!(!constants.is_empty());
}

#[test]
fn test_directory_import_collects_errors_for_bad_files() {
    let dir = tempfile::tempdir().expect("should create tempdir");

    std::fs::write(dir.path().join("good.art"), REFL_ARTICLE).expect("write good.art");
    std::fs::write(dir.path().join("bad.art"), "garbage content\n").expect("write bad.art");

    let importer = HolLightImporter::default();
    let (constants, stats, errors) = importer
        .import_directory(dir.path())
        .expect("directory import should succeed");

    // bad.art should produce an error, good.art should succeed.
    assert_eq!(errors.len(), 1);
    assert_eq!(stats.theorem_count, 1);
    assert!(!constants.is_empty());
}

// ============================================================================
// HolLightTheory Import Tests
// ============================================================================

#[test]
fn test_hol_light_theory_import_single_article() {
    let importer = HolLightImporter::default();
    let theory = importer
        .import_theory("refl_theory", &[REFL_ARTICLE])
        .expect("theory import should succeed");

    assert_eq!(theory.theory_name, "refl_theory");
    assert_eq!(theory.statistics.total_articles, 1);
    assert_eq!(theory.statistics.failed_articles, 0);
    assert!(theory.statistics.theorem_count >= 1);
    assert!(theory.total_constants() > 0);
}

#[test]
fn test_hol_light_theory_import_multiple_articles() {
    let importer = HolLightImporter::default();
    let theory = importer
        .import_theory("multi_theory", &[REFL_ARTICLE, REFL_ARTICLE, REFL_ARTICLE])
        .expect("theory import should succeed");

    assert_eq!(theory.statistics.total_articles, 3);
    assert_eq!(theory.statistics.failed_articles, 0);
    assert_eq!(theory.statistics.theorem_count, 3);
}

#[test]
fn test_hol_light_theory_import_with_failures() {
    let importer = HolLightImporter::default();
    let theory = importer
        .import_theory("mixed", &[REFL_ARTICLE, "bad article\n", REFL_ARTICLE])
        .expect("theory should succeed despite one bad article");

    assert_eq!(theory.statistics.total_articles, 3);
    assert_eq!(theory.statistics.failed_articles, 1);
    assert_eq!(theory.statistics.theorem_count, 2);
}

#[test]
fn test_hol_light_theory_combined_profile() {
    let importer = HolLightImporter::default();
    let theory = importer
        .import_theory("profile_test", &[REFL_ARTICLE])
        .expect("theory import");

    let profile = theory.combined_axiom_profile();
    assert!(profile.contains(AxiomProfile::CLASSICAL));
    assert!(profile.contains(AxiomProfile::EXTENSIONALITY));
    assert!(profile.contains(AxiomProfile::HOL_EMBEDDING));
    // CHOICE==CLASSICAL (same bit), so test with UNIVALENCE instead
    assert!(!profile.contains(AxiomProfile::UNIVALENCE));
}

#[test]
fn test_hol_light_theory_trust_level() {
    let importer = HolLightImporter::default();
    let theory = importer
        .import_theory("trust_test", &[REFL_ARTICLE])
        .expect("theory import");

    let trust = theory.min_trust_level();
    assert!(trust.is_some());
    // All constants from a single refl article should have CertificateReplayed or PartiallyAxiomatized
    let trust = trust.unwrap();
    assert!(
        trust == TrustLevel::CertificateReplayed || trust == TrustLevel::PartiallyAxiomatized,
        "unexpected trust level: {trust:?}"
    );
}

#[test]
fn test_hol_light_theory_empty_articles() {
    let importer = HolLightImporter::default();
    let theory = importer
        .import_theory("empty", &[])
        .expect("empty theory import should succeed");

    assert_eq!(theory.total_constants(), 0);
    assert!(theory.min_trust_level().is_none());
    assert!(theory.theorem_names().is_empty());
    assert!(theory.axiom_names().is_empty());
}

#[test]
fn test_hol_light_theory_theorem_names_populated() {
    let importer = HolLightImporter::default();
    let theory = importer
        .import_theory("name_test", &[REFL_ARTICLE])
        .expect("theory import");

    let names = theory.theorem_names();
    assert_eq!(names.len(), theory.theorems.len());
    for name in &names {
        assert!(
            name.contains("HolLight.Imported"),
            "theorem name should be namespaced: {name}"
        );
    }
}

#[test]
fn test_hol_light_statistics_success_rate() {
    let stats = HolLightStatistics {
        total_articles: 10,
        imported_constants: 25,
        failed_articles: 3,
        theorem_count: 15,
        axiom_count: 5,
        definition_count: 5,
    };
    assert!((stats.success_rate() - 0.7).abs() < f64::EPSILON);
}

#[test]
fn test_hol_light_statistics_success_rate_all_pass() {
    let stats = HolLightStatistics {
        total_articles: 5,
        imported_constants: 10,
        failed_articles: 0,
        theorem_count: 5,
        axiom_count: 2,
        definition_count: 3,
    };
    assert!((stats.success_rate() - 1.0).abs() < f64::EPSILON);
}

// ============================================================================
// Hol4Theory Import Tests
// ============================================================================

#[test]
fn test_hol4_theory_import_single_article() {
    let importer = Hol4Importer::default();
    let theory = importer
        .import_theory("boolTheory", &["min"], &[REFL_ARTICLE])
        .expect("theory import should succeed");

    assert_eq!(theory.theory_name, "boolTheory");
    assert_eq!(theory.parents, vec!["min"]);
    assert!(theory.has_parents());
    assert_eq!(theory.statistics.total_articles, 1);
    assert_eq!(theory.statistics.failed_articles, 0);
    assert!(theory.statistics.imported_constants > 0);
}

#[test]
fn test_hol4_theory_import_multiple_articles() {
    let importer = Hol4Importer::default();
    let theory = importer
        .import_theory("numTheory", &["bool"], &[REFL_ARTICLE, REFL_ARTICLE])
        .expect("theory import");

    assert_eq!(theory.statistics.total_articles, 2);
    assert_eq!(theory.statistics.theorem_count, 2);
}

#[test]
fn test_hol4_theory_import_with_failures() {
    let importer = Hol4Importer::default();
    let theory = importer
        .import_theory("mixed", &[], &[REFL_ARTICLE, "garbage\n"])
        .expect("theory should succeed despite bad article");

    assert_eq!(theory.statistics.failed_articles, 1);
    assert_eq!(theory.statistics.theorem_count, 1);
}

#[test]
fn test_hol4_theory_no_parents() {
    let importer = Hol4Importer::default();
    let theory = importer
        .import_theory("minTheory", &[], &[REFL_ARTICLE])
        .expect("theory import");

    assert!(!theory.has_parents());
    assert!(theory.parents.is_empty());
}

#[test]
fn test_hol4_theory_multiple_parents() {
    let importer = Hol4Importer::default();
    let theory = importer
        .import_theory("listTheory", &["bool", "num", "pair"], &[REFL_ARTICLE])
        .expect("theory import");

    assert_eq!(theory.parents, vec!["bool", "num", "pair"]);
    assert!(theory.has_parents());
}

#[test]
fn test_hol4_theory_combined_profile() {
    let importer = Hol4Importer::default();
    let theory = importer
        .import_theory("profile_test", &[], &[REFL_ARTICLE])
        .expect("theory import");

    let profile = theory.combined_axiom_profile();
    assert!(profile.contains(AxiomProfile::CLASSICAL));
    assert!(profile.contains(AxiomProfile::HOL_EMBEDDING));
}

#[test]
fn test_hol4_theory_empty_has_no_trust() {
    let importer = Hol4Importer::default();
    let theory = importer
        .import_theory("empty", &[], &[])
        .expect("empty theory");

    assert!(theory.min_trust_level().is_none());
    assert_eq!(theory.total_declarations(), 0);
}

#[test]
fn test_hol4_theory_total_declarations() {
    let importer = Hol4Importer::default();
    let theory = importer
        .import_theory("decl_test", &[], &[REFL_ARTICLE])
        .expect("theory import");

    let total = theory.types.len() + theory.constants.len() + theory.theorems.len();
    assert_eq!(theory.total_declarations(), total);
}

#[test]
fn test_hol4_statistics_success_rate() {
    let stats = Hol4Statistics {
        total_articles: 4,
        imported_constants: 8,
        failed_articles: 1,
        theorem_count: 4,
        type_count: 2,
        constant_count: 2,
    };
    assert!((stats.success_rate() - 0.75).abs() < f64::EPSILON);
}

// ============================================================================
// HolUnifier Cross-System Matching Tests
// ============================================================================

fn hol_profile() -> AxiomProfile {
    AxiomProfile::CLASSICAL | AxiomProfile::EXTENSIONALITY | AxiomProfile::HOL_EMBEDDING
}

#[test]
fn test_unifier_empty_state() {
    let u = HolUnifier::new();
    assert!(u.is_empty());
    assert_eq!(u.len(), 0);
    assert!(u.unified_constants().is_empty());
    assert!(u.find_equivalences().is_empty());
}

#[test]
fn test_unifier_add_constants_from_all_systems() {
    let mut u = HolUnifier::new();
    let id0 = u.add_hol_light_constant(
        "HOL.True",
        "Prop",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    let id1 = u.add_hol4_constant(
        "boolTheory.True",
        "Prop",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    let id2 = u.add_isabelle_constant(
        "HOL.True",
        "Prop",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );

    assert_eq!(id0, 0);
    assert_eq!(id1, 1);
    assert_eq!(id2, 2);
    assert_eq!(u.len(), 3);
}

#[test]
fn test_unifier_find_equivalences_cross_system() {
    let mut u = HolUnifier::new();
    u.add_hol_light_constant(
        "HOL.True",
        "Prop",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    u.add_hol4_constant(
        "boolTheory.True",
        "Prop",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    u.add_isabelle_constant(
        "HOL.True",
        "Prop",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );

    let pairs = u.find_equivalences();
    // 3 systems with base name "True" -> 3 cross-system pairs
    assert_eq!(pairs.len(), 3);
    for pair in &pairs {
        assert_eq!(pair.matched_name, "True");
    }
}

#[test]
fn test_unifier_no_equivalences_different_names() {
    let mut u = HolUnifier::new();
    u.add_hol_light_constant(
        "HOL.True",
        "Prop",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    u.add_hol4_constant(
        "boolTheory.False",
        "Prop",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    u.add_isabelle_constant(
        "Nat.zero",
        "Nat",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );

    let pairs = u.find_equivalences();
    assert!(pairs.is_empty());
}

#[test]
fn test_unifier_no_equivalences_same_system() {
    let mut u = HolUnifier::new();
    u.add_hol_light_constant(
        "A.True",
        "Prop",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    u.add_hol_light_constant(
        "B.True",
        "Prop",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );

    // Same source system -> no cross-system equivalence
    let pairs = u.find_equivalences();
    assert!(pairs.is_empty());
}

#[test]
fn test_unifier_get_constant_by_id() {
    let mut u = HolUnifier::new();
    let id = u.add_hol_light_constant(
        "Nat.add",
        "Nat->Nat->Nat",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );

    let record = u.get(id).expect("should find constant");
    assert_eq!(record.name, "Nat.add");
    assert_eq!(record.source_system, SourceSystem::HolLight);
    assert_eq!(record.type_repr, "Nat->Nat->Nat");
}

#[test]
fn test_unifier_get_nonexistent_returns_none() {
    let u = HolUnifier::new();
    assert!(u.get(999).is_none());
}

#[test]
fn test_unifier_constants_from_filter() {
    let mut u = HolUnifier::new();
    u.add_hol_light_constant("a", "T", hol_profile(), TrustLevel::CertificateReplayed);
    u.add_hol_light_constant("b", "T", hol_profile(), TrustLevel::CertificateReplayed);
    u.add_hol4_constant("c", "T", hol_profile(), TrustLevel::CertificateReplayed);
    u.add_isabelle_constant("d", "T", hol_profile(), TrustLevel::CertificateReplayed);

    assert_eq!(u.constants_from(&SourceSystem::HolLight).len(), 2);
    assert_eq!(u.constants_from(&SourceSystem::Hol4).len(), 1);
    assert_eq!(u.constants_from(&SourceSystem::Isabelle).len(), 1);
    assert!(u.constants_from(&SourceSystem::Coq).is_empty());
}

#[test]
fn test_unifier_search_by_name() {
    let mut u = HolUnifier::new();
    u.add_hol_light_constant(
        "Nat.add",
        "T",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    u.add_hol4_constant(
        "Nat.mul",
        "T",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    u.add_isabelle_constant(
        "Int.add",
        "T",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );

    let results = u.search_by_name("add");
    assert_eq!(results.len(), 2);
    let results = u.search_by_name("Nat");
    assert_eq!(results.len(), 2);
    let results = u.search_by_name("xyz");
    assert!(results.is_empty());
}

#[test]
fn test_unifier_merge() {
    let mut u1 = HolUnifier::new();
    u1.add_hol_light_constant("a.X", "T", hol_profile(), TrustLevel::CertificateReplayed);

    let mut u2 = HolUnifier::new();
    u2.add_hol4_constant("b.Y", "T", hol_profile(), TrustLevel::CertificateReplayed);
    u2.add_isabelle_constant("c.X", "T", hol_profile(), TrustLevel::CertificateReplayed);

    let id_map = u1.merge(&u2);
    assert_eq!(u1.len(), 3);
    assert_eq!(id_map.len(), 2);

    // After merge, cross-system equivalence for "X" should be detected
    let pairs = u1.find_equivalences();
    assert_eq!(pairs.len(), 1);
    assert_eq!(pairs[0].matched_name, "X");
}

// ============================================================================
// Statistics Aggregation Tests
// ============================================================================

#[test]
fn test_unifier_statistics_empty() {
    let u = HolUnifier::new();
    let stats = u.statistics();
    assert_eq!(stats.total_constants, 0);
    assert_eq!(stats.equivalence_count, 0);
    assert_eq!(stats.hol_light.constant_count, 0);
    assert_eq!(stats.hol4.constant_count, 0);
    assert_eq!(stats.isabelle.constant_count, 0);
}

#[test]
fn test_unifier_statistics_per_system_counts() {
    let mut u = HolUnifier::new();
    u.add_hol_light_constant("a", "T", hol_profile(), TrustLevel::CertificateReplayed);
    u.add_hol_light_constant("b", "T", hol_profile(), TrustLevel::PartiallyAxiomatized);
    u.add_hol4_constant("c", "T", hol_profile(), TrustLevel::CertificateReplayed);
    u.add_isabelle_constant("d", "T", hol_profile(), TrustLevel::TrustedOracle);

    let stats = u.statistics();
    assert_eq!(stats.total_constants, 4);
    assert_eq!(stats.hol_light.constant_count, 2);
    assert_eq!(stats.hol_light.proved_count, 1);
    assert_eq!(stats.hol_light.axiomatized_count, 1);
    assert_eq!(stats.hol4.constant_count, 1);
    assert_eq!(stats.hol4.proved_count, 1);
    assert_eq!(stats.hol4.axiomatized_count, 0);
    assert_eq!(stats.isabelle.constant_count, 1);
    assert_eq!(stats.isabelle.proved_count, 0);
    assert_eq!(stats.isabelle.axiomatized_count, 1);
}

#[test]
fn test_unifier_statistics_equivalence_count() {
    let mut u = HolUnifier::new();
    u.add_hol_light_constant(
        "HOL.True",
        "Prop",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    u.add_hol4_constant(
        "boolTheory.True",
        "Prop",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    u.add_hol_light_constant(
        "Nat.add",
        "Nat->Nat->Nat",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    u.add_isabelle_constant(
        "Groups.add",
        "Nat->Nat->Nat",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );

    let stats = u.statistics();
    assert_eq!(stats.total_constants, 4);
    // "True" matches HOL Light <-> HOL4, "add" matches HOL Light <-> Isabelle
    assert_eq!(stats.equivalence_count, 2);
}

#[test]
fn test_hol_light_theory_statistics_consistency() {
    let importer = HolLightImporter::default();
    let theory = importer
        .import_theory("consistency", &[REFL_ARTICLE, REFL_ARTICLE])
        .expect("theory import");

    // Statistics counts should match actual vector lengths
    assert_eq!(theory.statistics.theorem_count, theory.theorems.len());
    assert_eq!(theory.statistics.axiom_count, theory.axioms.len());
    assert_eq!(theory.statistics.definition_count, theory.definitions.len());
    assert_eq!(
        theory.statistics.imported_constants,
        theory.total_constants()
    );
}

#[test]
fn test_hol4_theory_statistics_consistency() {
    let importer = Hol4Importer::default();
    let theory = importer
        .import_theory("consistency", &[], &[REFL_ARTICLE, REFL_ARTICLE])
        .expect("theory import");

    assert_eq!(theory.statistics.theorem_count, theory.theorems.len());
    assert_eq!(
        theory.statistics.imported_constants,
        theory.total_declarations()
    );
}

// ============================================================================
// Cross-System Theory Integration Tests
// ============================================================================

#[test]
fn test_cross_system_theory_import_and_unify() {
    // Import the same article through both systems, then unify
    let hl_importer = HolLightImporter::default();
    let hol4_importer = Hol4Importer::default();

    let hl_theory = hl_importer
        .import_theory("refl", &[REFL_ARTICLE])
        .expect("HL theory import");
    let hol4_theory = hol4_importer
        .import_theory("refl", &[], &[REFL_ARTICLE])
        .expect("HOL4 theory import");

    let mut unifier = HolUnifier::new();

    // Add HOL Light theorems
    for thm in &hl_theory.theorems {
        unifier.add_hol_light_constant(
            &thm.name.to_string(),
            &format!("{:?}", thm.type_expr),
            thm.axiom_profile,
            thm.trust_level,
        );
    }

    // Add HOL4 theorems
    for thm in &hol4_theory.theorems {
        unifier.add_hol4_constant(
            &thm.name.to_string(),
            &format!("{:?}", thm.type_expr),
            thm.axiom_profile,
            thm.trust_level,
        );
    }

    // Both systems should produce at least one theorem each
    assert!(!unifier.constants_from(&SourceSystem::HolLight).is_empty());
    assert!(!unifier.constants_from(&SourceSystem::Hol4).is_empty());

    let stats = unifier.statistics();
    assert!(stats.total_constants >= 2);
}

#[test]
fn test_unifier_equivalence_pairs_are_deterministic() {
    let mut u = HolUnifier::new();
    u.add_isabelle_constant(
        "z.Comm",
        "T",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    u.add_hol4_constant(
        "y.Comm",
        "T",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    u.add_hol_light_constant(
        "x.Comm",
        "T",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );

    let pairs1 = u.find_equivalences();
    let pairs2 = u.find_equivalences();

    // Same call should produce same results
    assert_eq!(pairs1.len(), pairs2.len());
    for (a, b) in pairs1.iter().zip(pairs2.iter()) {
        assert_eq!(a.left, b.left);
        assert_eq!(a.right, b.right);
        assert_eq!(a.matched_name, b.matched_name);
    }

    // Pairs should be sorted by (left, right)
    for i in 1..pairs1.len() {
        let prev = (pairs1[i - 1].left, pairs1[i - 1].right);
        let curr = (pairs1[i].left, pairs1[i].right);
        assert!(prev <= curr);
    }
}

#[test]
fn test_unifier_multiple_equivalence_groups() {
    let mut u = HolUnifier::new();
    // Group 1: "True" across HL and HOL4
    u.add_hol_light_constant(
        "HOL.True",
        "Prop",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    u.add_hol4_constant(
        "boolTheory.True",
        "Prop",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    // Group 2: "Suc" across HL and Isabelle
    u.add_hol_light_constant(
        "Nat.Suc",
        "Nat->Nat",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    u.add_isabelle_constant(
        "Nat.Suc",
        "Nat->Nat",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    // Unmatched: unique base names
    u.add_hol4_constant(
        "listTheory.CONS",
        "a->list->list",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );

    let pairs = u.find_equivalences();
    assert_eq!(pairs.len(), 2); // True pair + Suc pair

    let matched_names: Vec<&str> = pairs.iter().map(|p| p.matched_name.as_str()).collect();
    assert!(matched_names.contains(&"True"));
    assert!(matched_names.contains(&"Suc"));
}

// ============================================================================
// Cross-System: HolTheoryAlignment Tests
// ============================================================================

use super::cross_system::{
    CrossSystemStatistics, HolConstantIndex, HolTheoryAlignment, UnificationResult,
};

#[test]
fn test_alignment_new_is_empty() {
    let a = HolTheoryAlignment::new("True");
    assert_eq!(a.base_name, "True");
    assert_eq!(a.system_count(), 0);
    assert!(!a.is_cross_system());
    assert!(!a.is_fully_aligned());
    assert!(a.all_ids().is_empty());
}

#[test]
fn test_alignment_single_system() {
    let mut a = HolTheoryAlignment::new("add");
    a.set_id(&SourceSystem::HolLight, 42);
    assert_eq!(a.system_count(), 1);
    assert!(!a.is_cross_system());
    assert!(!a.is_fully_aligned());
    assert_eq!(a.get_id(&SourceSystem::HolLight), Some(42));
    assert_eq!(a.get_id(&SourceSystem::Hol4), None);
    assert_eq!(a.all_ids(), vec![42]);
}

#[test]
fn test_alignment_two_systems() {
    let mut a = HolTheoryAlignment::new("True");
    a.set_id(&SourceSystem::HolLight, 1);
    a.set_id(&SourceSystem::Hol4, 2);
    assert_eq!(a.system_count(), 2);
    assert!(a.is_cross_system());
    assert!(!a.is_fully_aligned());
    assert_eq!(a.all_ids(), vec![1, 2]);
}

#[test]
fn test_alignment_fully_aligned() {
    let mut a = HolTheoryAlignment::new("Suc");
    a.set_id(&SourceSystem::HolLight, 10);
    a.set_id(&SourceSystem::Hol4, 20);
    a.set_id(&SourceSystem::Isabelle, 30);
    assert_eq!(a.system_count(), 3);
    assert!(a.is_cross_system());
    assert!(a.is_fully_aligned());
    assert_eq!(a.all_ids(), vec![10, 20, 30]);
}

#[test]
fn test_alignment_non_hol_system_ignored() {
    let mut a = HolTheoryAlignment::new("test");
    a.set_id(&SourceSystem::Coq, 99);
    assert_eq!(a.system_count(), 0);
    assert_eq!(a.get_id(&SourceSystem::Coq), None);
}

#[test]
fn test_alignment_overwrite_same_system() {
    let mut a = HolTheoryAlignment::new("add");
    a.set_id(&SourceSystem::HolLight, 1);
    a.set_id(&SourceSystem::HolLight, 2);
    // Last write wins
    assert_eq!(a.get_id(&SourceSystem::HolLight), Some(2));
    assert_eq!(a.system_count(), 1);
}

// ============================================================================
// Cross-System: HolConstantIndex Tests
// ============================================================================

#[test]
fn test_constant_index_empty() {
    let index = HolConstantIndex::new();
    assert_eq!(index.distinct_names(), 0);
    assert_eq!(index.distinct_types(), 0);
    assert_eq!(index.total_entries(), 0);
    assert!(index.all_base_names().is_empty());
}

#[test]
fn test_constant_index_from_unifier() {
    let mut u = HolUnifier::new();
    u.add_hol_light_constant(
        "Nat.add",
        "Nat->Nat->Nat",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    u.add_hol4_constant(
        "Nat.add",
        "Nat->Nat->Nat",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    u.add_isabelle_constant(
        "Int.mul",
        "Int->Int->Int",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );

    let index = u.build_index();
    assert_eq!(index.distinct_names(), 2); // "add" and "mul"
    assert_eq!(index.distinct_types(), 2);
    assert_eq!(index.total_entries(), 3);
}

#[test]
fn test_constant_index_lookup_by_name() {
    let mut u = HolUnifier::new();
    u.add_hol_light_constant(
        "Nat.add",
        "T",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    u.add_hol4_constant(
        "Int.add",
        "T",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    u.add_isabelle_constant(
        "Bool.neg",
        "T",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );

    let index = u.build_index();
    let add_ids = index.lookup_by_name("add");
    assert_eq!(add_ids.len(), 2);
    let neg_ids = index.lookup_by_name("neg");
    assert_eq!(neg_ids.len(), 1);
    let missing = index.lookup_by_name("nonexistent");
    assert!(missing.is_empty());
}

#[test]
fn test_constant_index_lookup_by_type() {
    let mut u = HolUnifier::new();
    u.add_hol_light_constant("a", "Prop", hol_profile(), TrustLevel::CertificateReplayed);
    u.add_hol4_constant("b", "Nat", hol_profile(), TrustLevel::CertificateReplayed);
    u.add_isabelle_constant("c", "Prop", hol_profile(), TrustLevel::CertificateReplayed);

    let index = u.build_index();
    let prop_ids = index.lookup_by_type("Prop");
    assert_eq!(prop_ids.len(), 2);
    let nat_ids = index.lookup_by_type("Nat");
    assert_eq!(nat_ids.len(), 1);
}

#[test]
fn test_constant_index_lookup_by_name_and_type() {
    let mut u = HolUnifier::new();
    u.add_hol_light_constant(
        "A.x",
        "Prop",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    u.add_hol4_constant("B.x", "Nat", hol_profile(), TrustLevel::CertificateReplayed);
    u.add_isabelle_constant(
        "C.x",
        "Prop",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );

    let index = u.build_index();
    let results = index.lookup_by_name_and_type("x", "Prop");
    assert_eq!(results.len(), 2);
    let results = index.lookup_by_name_and_type("x", "Nat");
    assert_eq!(results.len(), 1);
    let results = index.lookup_by_name_and_type("x", "Bool");
    assert!(results.is_empty());
}

#[test]
fn test_constant_index_lookup_by_name_and_system() {
    let mut u = HolUnifier::new();
    u.add_hol_light_constant(
        "A.True",
        "Prop",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    u.add_hol4_constant(
        "B.True",
        "Prop",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    u.add_isabelle_constant(
        "C.True",
        "Prop",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );

    let index = u.build_index();
    let hl = index.lookup_by_name_and_system("True", &SourceSystem::HolLight);
    assert_eq!(hl.len(), 1);
    let h4 = index.lookup_by_name_and_system("True", &SourceSystem::Hol4);
    assert_eq!(h4.len(), 1);
    let coq = index.lookup_by_name_and_system("True", &SourceSystem::Coq);
    assert!(coq.is_empty());
}

#[test]
fn test_constant_index_all_base_names_sorted() {
    let mut u = HolUnifier::new();
    u.add_hol_light_constant("Z.z", "T", hol_profile(), TrustLevel::CertificateReplayed);
    u.add_hol4_constant("A.a", "T", hol_profile(), TrustLevel::CertificateReplayed);
    u.add_isabelle_constant("M.m", "T", hol_profile(), TrustLevel::CertificateReplayed);

    let index = u.build_index();
    let names = index.all_base_names();
    assert_eq!(names, vec!["a", "m", "z"]);
}

// ============================================================================
// Cross-System: batch_unify and UnificationResult Tests
// ============================================================================

#[test]
fn test_batch_unify_empty() {
    let u = HolUnifier::new();
    let results = u.batch_unify();
    assert!(results.is_empty());
}

#[test]
fn test_batch_unify_single_system() {
    let mut u = HolUnifier::new();
    u.add_hol_light_constant(
        "A.True",
        "Prop",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    u.add_hol_light_constant(
        "B.False",
        "Prop",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );

    let results = u.batch_unify();
    assert_eq!(results.len(), 2);
    // With only one system, nothing should be cross-system.
    for r in &results {
        assert!(!r.alignment.is_cross_system());
    }
}

#[test]
fn test_batch_unify_cross_system_match() {
    let mut u = HolUnifier::new();
    u.add_hol_light_constant(
        "HOL.True",
        "Prop",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    u.add_hol4_constant(
        "bool.True",
        "Prop",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );

    let results = u.batch_unify();
    assert_eq!(results.len(), 1);
    let r = &results[0];
    assert_eq!(r.base_name, "True");
    assert!(r.is_confident());
    assert!(!r.has_conflicts());
    assert!(r.alignment.is_cross_system());
    assert_eq!(r.match_score, 1.0); // Name match + type match.
}

#[test]
fn test_batch_unify_type_mismatch_conflict() {
    let mut u = HolUnifier::new();
    u.add_hol_light_constant(
        "A.add",
        "Nat->Nat->Nat",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    u.add_hol4_constant(
        "B.add",
        "Int->Int->Int",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );

    let results = u.batch_unify();
    assert_eq!(results.len(), 1);
    let r = &results[0];
    assert_eq!(r.base_name, "add");
    assert!(r.has_conflicts());
    assert!(r.match_score <= 0.5); // Capped due to type mismatch.
}

#[test]
fn test_unification_result_no_constants() {
    let u = HolUnifier::new();
    let r = u.unify_constant("nonexistent");
    assert_eq!(r.match_score, 0.0);
    assert!(r.has_conflicts());
    assert_eq!(r.alignment.system_count(), 0);
}

#[test]
fn test_batch_unify_results_sorted_by_base_name() {
    let mut u = HolUnifier::new();
    u.add_hol_light_constant("Z.zzz", "T", hol_profile(), TrustLevel::CertificateReplayed);
    u.add_hol_light_constant("A.aaa", "T", hol_profile(), TrustLevel::CertificateReplayed);
    u.add_hol_light_constant("M.mmm", "T", hol_profile(), TrustLevel::CertificateReplayed);

    let results = u.batch_unify();
    for i in 1..results.len() {
        assert!(results[i - 1].base_name <= results[i].base_name);
    }
}

#[test]
fn test_batch_unify_ambiguous_same_system() {
    let mut u = HolUnifier::new();
    // Two constants from the same system with same base name.
    u.add_hol_light_constant(
        "A.add",
        "Nat->Nat->Nat",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    u.add_hol_light_constant(
        "B.add",
        "Int->Int->Int",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    u.add_hol4_constant(
        "C.add",
        "Nat->Nat->Nat",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );

    let results = u.batch_unify();
    assert_eq!(results.len(), 1);
    let r = &results[0];
    assert!(r.has_conflicts()); // Ambiguous due to two HL constants with same base.
}

// ============================================================================
// Cross-System: CrossSystemStatistics Tests
// ============================================================================

#[test]
fn test_cross_system_statistics_empty() {
    let u = HolUnifier::new();
    let stats = u.cross_system_statistics();
    assert_eq!(stats.matched, 0);
    assert_eq!(stats.unmatched, 0);
    assert_eq!(stats.conflicts, 0);
    assert_eq!(stats.ambiguous, 0);
}

#[test]
fn test_cross_system_statistics_all_matched() {
    let mut u = HolUnifier::new();
    u.add_hol_light_constant(
        "A.True",
        "Prop",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    u.add_hol4_constant(
        "B.True",
        "Prop",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );

    let stats = u.cross_system_statistics();
    assert_eq!(stats.matched, 1);
    assert_eq!(stats.unmatched, 0);
}

#[test]
fn test_cross_system_statistics_all_unmatched() {
    let mut u = HolUnifier::new();
    u.add_hol_light_constant(
        "A.True",
        "Prop",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    u.add_hol4_constant(
        "B.False",
        "Prop",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );

    let stats = u.cross_system_statistics();
    assert_eq!(stats.matched, 0);
    assert_eq!(stats.unmatched, 2);
}

#[test]
fn test_cross_system_statistics_with_conflicts() {
    let mut u = HolUnifier::new();
    u.add_hol_light_constant(
        "A.add",
        "Nat->Nat->Nat",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    u.add_hol4_constant(
        "B.add",
        "Int->Int->Int",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );

    let stats = u.cross_system_statistics();
    assert_eq!(stats.matched, 1);
    assert_eq!(stats.conflicts, 1);
}

// ============================================================================
// Cross-System: compute_alignments Tests
// ============================================================================

#[test]
fn test_compute_alignments_empty() {
    let u = HolUnifier::new();
    let alignments = u.compute_alignments();
    assert!(alignments.is_empty());
}

#[test]
fn test_compute_alignments_groups_by_base_name() {
    let mut u = HolUnifier::new();
    u.add_hol_light_constant(
        "HOL.True",
        "Prop",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    u.add_hol4_constant(
        "bool.True",
        "Prop",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    u.add_isabelle_constant(
        "Nat.zero",
        "Nat",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );

    let alignments = u.compute_alignments();
    assert_eq!(alignments.len(), 2); // "True" and "zero"

    let true_alignment = alignments.iter().find(|a| a.base_name == "True").unwrap();
    assert!(true_alignment.is_cross_system());
    assert!(true_alignment.hol_light_id.is_some());
    assert!(true_alignment.hol4_id.is_some());
    assert!(true_alignment.isabelle_id.is_none());
}

#[test]
fn test_compute_alignments_sorted_by_name() {
    let mut u = HolUnifier::new();
    u.add_hol_light_constant("Z.z", "T", hol_profile(), TrustLevel::CertificateReplayed);
    u.add_hol_light_constant("A.a", "T", hol_profile(), TrustLevel::CertificateReplayed);
    u.add_hol_light_constant("M.m", "T", hol_profile(), TrustLevel::CertificateReplayed);

    let alignments = u.compute_alignments();
    for i in 1..alignments.len() {
        assert!(alignments[i - 1].base_name <= alignments[i].base_name);
    }
}

// ============================================================================
// OpenTheory Bridge: OtImportConfig Tests
// ============================================================================

use super::opentheory_bridge::{OtAxiomPolicy, OtImportConfig, OtImportResult, OtStatistics};

#[test]
fn test_ot_import_config_default() {
    let config = OtImportConfig::default();
    assert_eq!(config.trust_level, TrustLevel::CertificateReplayed);
    assert_eq!(config.axiom_policy, OtAxiomPolicy::AcceptAll);
    assert!(config.name_mapping.is_empty());
    assert!(config.include_support);
    assert!(config.include_assumptions);
}

#[test]
fn test_ot_import_config_theorems_only() {
    let config = OtImportConfig::theorems_only();
    assert!(!config.include_support);
    assert!(!config.include_assumptions);
}

#[test]
fn test_ot_import_config_strict() {
    let config = OtImportConfig::strict();
    assert_eq!(config.axiom_policy, OtAxiomPolicy::RejectUnknown);
}

#[test]
fn test_ot_import_config_builder_pattern() {
    let config = OtImportConfig::default()
        .with_trust_level(TrustLevel::PartiallyAxiomatized)
        .with_axiom_policy(OtAxiomPolicy::MapToProfile)
        .with_name_mapping("old_name", "new_name");

    assert_eq!(config.trust_level, TrustLevel::PartiallyAxiomatized);
    assert_eq!(config.axiom_policy, OtAxiomPolicy::MapToProfile);
    assert_eq!(
        config.name_mapping.get("old_name"),
        Some(&"new_name".to_owned())
    );
}

#[test]
fn test_ot_axiom_policy_default_is_accept_all() {
    assert_eq!(OtAxiomPolicy::default(), OtAxiomPolicy::AcceptAll);
}

// ============================================================================
// OpenTheory Bridge: OtStatistics Tests
// ============================================================================

#[test]
fn test_ot_statistics_default_is_zero() {
    let stats = OtStatistics::default();
    assert_eq!(stats.articles_read, 0);
    assert_eq!(stats.theorems_imported, 0);
    assert_eq!(stats.axioms_tracked, 0);
    assert_eq!(stats.support_imported, 0);
    assert_eq!(stats.articles_failed, 0);
    assert_eq!(stats.total_imported(), 0);
    assert!((stats.success_rate() - 1.0).abs() < f64::EPSILON);
}

#[test]
fn test_ot_statistics_total() {
    let stats = OtStatistics {
        articles_read: 3,
        theorems_imported: 5,
        axioms_tracked: 2,
        support_imported: 3,
        articles_failed: 0,
    };
    assert_eq!(stats.total_imported(), 10);
    assert!((stats.success_rate() - 1.0).abs() < f64::EPSILON);
}

#[test]
fn test_ot_statistics_success_rate_with_failures() {
    let stats = OtStatistics {
        articles_read: 4,
        theorems_imported: 3,
        axioms_tracked: 0,
        support_imported: 0,
        articles_failed: 1,
    };
    assert!((stats.success_rate() - 0.75).abs() < f64::EPSILON);
}

#[test]
fn test_ot_statistics_merge() {
    let mut a = OtStatistics {
        articles_read: 2,
        theorems_imported: 5,
        axioms_tracked: 1,
        support_imported: 3,
        articles_failed: 0,
    };
    let b = OtStatistics {
        articles_read: 3,
        theorems_imported: 7,
        axioms_tracked: 2,
        support_imported: 4,
        articles_failed: 1,
    };
    a.merge(&b);
    assert_eq!(a.articles_read, 5);
    assert_eq!(a.theorems_imported, 12);
    assert_eq!(a.axioms_tracked, 3);
    assert_eq!(a.support_imported, 7);
    assert_eq!(a.articles_failed, 1);
}

// ============================================================================
// OpenTheory Bridge: batch_import Tests
// ============================================================================

#[test]
fn test_batch_import_single_article() {
    let bridge =
        OtMathverseBridge::new(LeanName::from_string("Test.Batch"), SourceSystem::HolLight);
    let result = bridge.batch_import(&[REFL_ARTICLE]);
    assert_eq!(result.statistics.articles_read, 1);
    assert_eq!(result.statistics.articles_failed, 0);
    assert_eq!(result.statistics.theorems_imported, 1);
    assert!(!result.has_warnings());
}

#[test]
fn test_batch_import_multiple_articles() {
    let bridge =
        OtMathverseBridge::new(LeanName::from_string("Test.Batch"), SourceSystem::HolLight);
    let result = bridge.batch_import(&[REFL_ARTICLE, REFL_ARTICLE, REFL_ARTICLE]);
    assert_eq!(result.statistics.articles_read, 3);
    assert_eq!(result.statistics.articles_failed, 0);
    assert_eq!(result.statistics.theorems_imported, 3);
    assert_eq!(result.constant_count(), 3);
}

#[test]
fn test_batch_import_with_failures() {
    let bridge =
        OtMathverseBridge::new(LeanName::from_string("Test.Batch"), SourceSystem::HolLight);
    let result = bridge.batch_import(&[REFL_ARTICLE, "bad\n", REFL_ARTICLE]);
    assert_eq!(result.statistics.articles_read, 3);
    assert_eq!(result.statistics.articles_failed, 1);
    assert_eq!(result.statistics.theorems_imported, 2);
    assert!(result.has_warnings());
    assert_eq!(result.warnings.len(), 1);
}

#[test]
fn test_batch_import_empty() {
    let bridge =
        OtMathverseBridge::new(LeanName::from_string("Test.Batch"), SourceSystem::HolLight);
    let result = bridge.batch_import(&[]);
    assert_eq!(result.statistics.articles_read, 0);
    assert_eq!(result.constant_count(), 0);
    assert!(!result.has_warnings());
}

#[test]
fn test_batch_import_all_failures() {
    let bridge =
        OtMathverseBridge::new(LeanName::from_string("Test.Batch"), SourceSystem::HolLight);
    let result = bridge.batch_import(&["bad1\n", "bad2\n"]);
    assert_eq!(result.statistics.articles_read, 2);
    assert_eq!(result.statistics.articles_failed, 2);
    assert_eq!(result.constant_count(), 0);
    assert_eq!(result.warnings.len(), 2);
}

// ============================================================================
// OpenTheory Bridge: import_with_config Tests
// ============================================================================

#[test]
fn test_import_with_config_default() {
    let bridge =
        OtMathverseBridge::new(LeanName::from_string("Test.Config"), SourceSystem::HolLight);
    let article = clean_kernel::open_theory::parse_article(REFL_ARTICLE).expect("should parse");
    let config = OtImportConfig::default();
    let result = bridge
        .import_with_config(&article, &config)
        .expect("import should succeed");

    assert!(result.constant_count() >= 1);
    assert_eq!(result.statistics.articles_read, 1);
}

#[test]
fn test_import_with_config_theorems_only() {
    let bridge =
        OtMathverseBridge::new(LeanName::from_string("Test.Config"), SourceSystem::HolLight);
    let article = clean_kernel::open_theory::parse_article(REFL_ARTICLE).expect("should parse");
    let config = OtImportConfig::theorems_only();
    let result = bridge
        .import_with_config(&article, &config)
        .expect("import should succeed");

    // Only theorems should be included.
    for c in &result.constants {
        assert_eq!(c.kind, ImportedConstantKind::Theorem);
    }
}

#[test]
fn test_import_statistics_merge() {
    let mut a = ImportStatistics {
        support_count: 2,
        assumption_count: 1,
        theorem_count: 5,
    };
    let b = ImportStatistics {
        support_count: 3,
        assumption_count: 2,
        theorem_count: 4,
    };
    a.merge(&b);
    assert_eq!(a.support_count, 5);
    assert_eq!(a.assumption_count, 3);
    assert_eq!(a.theorem_count, 9);
    assert_eq!(a.total(), 17);
}

// ============================================================================
// HOL Light: Proof Step Tests
// ============================================================================

use super::hol_light::{
    parse_proof_log, parse_proof_log_line, HolLightAxiomTracker, HolLightProofStep,
    HolLightProofTree,
};

#[test]
fn test_proof_step_refl() {
    let step = HolLightProofStep::Refl {
        term: "x".to_owned(),
    };
    assert_eq!(step.rule_name(), "REFL");
    assert!(step.is_leaf());
    assert!(step.premise_indices().is_empty());
}

#[test]
fn test_proof_step_trans() {
    let step = HolLightProofStep::Trans { left: 0, right: 1 };
    assert_eq!(step.rule_name(), "TRANS");
    assert!(!step.is_leaf());
    assert_eq!(step.premise_indices(), vec![0, 1]);
}

#[test]
fn test_proof_step_mk_comb() {
    let step = HolLightProofStep::MkComb { func: 0, arg: 1 };
    assert_eq!(step.rule_name(), "MK_COMB");
    assert!(!step.is_leaf());
    assert_eq!(step.premise_indices(), vec![0, 1]);
}

#[test]
fn test_proof_step_abs() {
    let step = HolLightProofStep::Abs {
        var: "x".to_owned(),
        body: 0,
    };
    assert_eq!(step.rule_name(), "ABS");
    assert!(!step.is_leaf());
    assert_eq!(step.premise_indices(), vec![0]);
}

#[test]
fn test_proof_step_beta() {
    let step = HolLightProofStep::Beta {
        lambda_term: "(\\x. x) y".to_owned(),
    };
    assert_eq!(step.rule_name(), "BETA");
    assert!(step.is_leaf());
    assert!(step.premise_indices().is_empty());
}

#[test]
fn test_proof_step_assume() {
    let step = HolLightProofStep::Assume {
        prop: "p".to_owned(),
    };
    assert_eq!(step.rule_name(), "ASSUME");
    assert!(step.is_leaf());
}

#[test]
fn test_proof_step_eq_mp() {
    let step = HolLightProofStep::EqMp { equiv: 0, proof: 1 };
    assert_eq!(step.rule_name(), "EQ_MP");
    assert!(!step.is_leaf());
    assert_eq!(step.premise_indices(), vec![0, 1]);
}

#[test]
fn test_proof_step_deduct() {
    let step = HolLightProofStep::Deduct { left: 0, right: 1 };
    assert_eq!(step.rule_name(), "DEDUCT_ANTISYM_RULE");
    assert!(!step.is_leaf());
}

#[test]
fn test_proof_step_inst() {
    let step = HolLightProofStep::Inst {
        theorem: 0,
        substitutions: vec![("t".to_owned(), "x".to_owned())],
    };
    assert_eq!(step.rule_name(), "INST");
    assert!(!step.is_leaf());
    assert_eq!(step.premise_indices(), vec![0]);
}

#[test]
fn test_proof_step_inst_type() {
    let step = HolLightProofStep::InstType {
        theorem: 0,
        type_substitutions: vec![("num".to_owned(), "A".to_owned())],
    };
    assert_eq!(step.rule_name(), "INST_TYPE");
    assert!(!step.is_leaf());
    assert_eq!(step.premise_indices(), vec![0]);
}

// ============================================================================
// HOL Light: Proof Tree Tests
// ============================================================================

#[test]
fn test_proof_tree_empty() {
    let tree = HolLightProofTree::new();
    assert!(tree.is_empty());
    assert_eq!(tree.step_count(), 0);
    assert_eq!(tree.leaf_count(), 0);
    assert_eq!(tree.depth(), 0);
    assert!(tree.is_valid());
    assert!(tree.conclusion.is_none());
    assert!(tree.theorem_name.is_none());
}

#[test]
fn test_proof_tree_with_name() {
    let tree = HolLightProofTree::with_name("TRUTH");
    assert_eq!(tree.theorem_name, Some("TRUTH".to_owned()));
    assert!(tree.is_empty());
}

#[test]
fn test_proof_tree_single_step() {
    let mut tree = HolLightProofTree::new();
    let idx = tree.add_step(HolLightProofStep::Refl {
        term: "x".to_owned(),
    });
    tree.set_conclusion(idx);
    assert_eq!(tree.step_count(), 1);
    assert_eq!(tree.leaf_count(), 1);
    assert_eq!(tree.depth(), 1);
    assert!(tree.is_valid());
    assert_eq!(tree.conclusion, Some(0));
}

#[test]
fn test_proof_tree_multi_step() {
    let mut tree = HolLightProofTree::new();
    tree.add_step(HolLightProofStep::Refl {
        term: "x".to_owned(),
    });
    tree.add_step(HolLightProofStep::Refl {
        term: "y".to_owned(),
    });
    let conclusion = tree.add_step(HolLightProofStep::Trans { left: 0, right: 1 });
    tree.set_conclusion(conclusion);

    assert_eq!(tree.step_count(), 3);
    assert_eq!(tree.leaf_count(), 2);
    assert_eq!(tree.depth(), 2);
    assert!(tree.is_valid());
}

#[test]
fn test_proof_tree_invalid_forward_reference() {
    let mut tree = HolLightProofTree::new();
    // This step references index 1, but only index 0 exists so far.
    tree.add_step(HolLightProofStep::Trans { left: 1, right: 2 });
    assert!(!tree.is_valid());
}

#[test]
fn test_proof_tree_invalid_conclusion_index() {
    let mut tree = HolLightProofTree::new();
    tree.add_step(HolLightProofStep::Refl {
        term: "x".to_owned(),
    });
    tree.set_conclusion(99);
    assert!(!tree.is_valid());
}

#[test]
fn test_proof_tree_rule_histogram() {
    let mut tree = HolLightProofTree::new();
    tree.add_step(HolLightProofStep::Refl {
        term: "x".to_owned(),
    });
    tree.add_step(HolLightProofStep::Refl {
        term: "y".to_owned(),
    });
    tree.add_step(HolLightProofStep::Trans { left: 0, right: 1 });

    let hist = tree.rule_histogram();
    assert_eq!(hist.get("REFL"), Some(&2));
    assert_eq!(hist.get("TRANS"), Some(&1));
    assert_eq!(hist.get("MK_COMB"), None);
}

#[test]
fn test_proof_tree_get_step() {
    let mut tree = HolLightProofTree::new();
    tree.add_step(HolLightProofStep::Assume {
        prop: "p".to_owned(),
    });
    let step = tree.get_step(0).expect("step should exist");
    assert_eq!(step.rule_name(), "ASSUME");
    assert!(tree.get_step(1).is_none());
}

#[test]
fn test_proof_tree_deeper_nesting() {
    let mut tree = HolLightProofTree::new();
    // Build a chain: refl -> abs -> trans
    tree.add_step(HolLightProofStep::Refl {
        term: "x".to_owned(),
    });
    tree.add_step(HolLightProofStep::Abs {
        var: "x".to_owned(),
        body: 0,
    });
    tree.add_step(HolLightProofStep::Refl {
        term: "y".to_owned(),
    });
    let conclusion = tree.add_step(HolLightProofStep::Trans { left: 1, right: 2 });
    tree.set_conclusion(conclusion);

    assert_eq!(tree.step_count(), 4);
    assert_eq!(tree.depth(), 3); // refl(1) -> abs(2) -> trans(3)
    assert!(tree.is_valid());
}

// ============================================================================
// HOL Light: parse_proof_log Tests
// ============================================================================

#[test]
fn test_parse_proof_log_line_refl() {
    let step = parse_proof_log_line("REFL x").unwrap();
    assert_eq!(step.rule_name(), "REFL");
    if let HolLightProofStep::Refl { term } = step {
        assert_eq!(term, "x");
    } else {
        panic!("expected Refl");
    }
}

#[test]
fn test_parse_proof_log_line_trans() {
    let step = parse_proof_log_line("TRANS 0 1").unwrap();
    assert_eq!(step.rule_name(), "TRANS");
    if let HolLightProofStep::Trans { left, right } = step {
        assert_eq!(left, 0);
        assert_eq!(right, 1);
    } else {
        panic!("expected Trans");
    }
}

#[test]
fn test_parse_proof_log_line_mk_comb() {
    let step = parse_proof_log_line("MK_COMB 2 3").unwrap();
    if let HolLightProofStep::MkComb { func, arg } = step {
        assert_eq!(func, 2);
        assert_eq!(arg, 3);
    } else {
        panic!("expected MkComb");
    }
}

#[test]
fn test_parse_proof_log_line_abs() {
    let step = parse_proof_log_line("ABS x 0").unwrap();
    if let HolLightProofStep::Abs { var, body } = step {
        assert_eq!(var, "x");
        assert_eq!(body, 0);
    } else {
        panic!("expected Abs");
    }
}

#[test]
fn test_parse_proof_log_line_beta() {
    let step = parse_proof_log_line("BETA (\\x. x) y").unwrap();
    if let HolLightProofStep::Beta { lambda_term } = step {
        assert_eq!(lambda_term, "(\\x. x) y");
    } else {
        panic!("expected Beta");
    }
}

#[test]
fn test_parse_proof_log_line_assume() {
    let step = parse_proof_log_line("ASSUME p /\\ q").unwrap();
    if let HolLightProofStep::Assume { prop } = step {
        assert_eq!(prop, "p /\\ q");
    } else {
        panic!("expected Assume");
    }
}

#[test]
fn test_parse_proof_log_line_eq_mp() {
    let step = parse_proof_log_line("EQ_MP 4 5").unwrap();
    if let HolLightProofStep::EqMp { equiv, proof } = step {
        assert_eq!(equiv, 4);
        assert_eq!(proof, 5);
    } else {
        panic!("expected EqMp");
    }
}

#[test]
fn test_parse_proof_log_line_deduct() {
    let step = parse_proof_log_line("DEDUCT 6 7").unwrap();
    if let HolLightProofStep::Deduct { left, right } = step {
        assert_eq!(left, 6);
        assert_eq!(right, 7);
    } else {
        panic!("expected Deduct");
    }
}

#[test]
fn test_parse_proof_log_line_inst_with_substitutions() {
    let step = parse_proof_log_line("INST 0 t/x,u/y").unwrap();
    if let HolLightProofStep::Inst {
        theorem,
        substitutions,
    } = step
    {
        assert_eq!(theorem, 0);
        assert_eq!(substitutions.len(), 2);
        assert_eq!(substitutions[0], ("t".to_owned(), "x".to_owned()));
        assert_eq!(substitutions[1], ("u".to_owned(), "y".to_owned()));
    } else {
        panic!("expected Inst");
    }
}

#[test]
fn test_parse_proof_log_line_inst_type() {
    let step = parse_proof_log_line("INST_TYPE 0 num/A").unwrap();
    if let HolLightProofStep::InstType {
        theorem,
        type_substitutions,
    } = step
    {
        assert_eq!(theorem, 0);
        assert_eq!(type_substitutions.len(), 1);
        assert_eq!(type_substitutions[0], ("num".to_owned(), "A".to_owned()));
    } else {
        panic!("expected InstType");
    }
}

#[test]
fn test_parse_proof_log_line_empty() {
    assert!(parse_proof_log_line("").is_none());
    assert!(parse_proof_log_line("  ").is_none());
}

#[test]
fn test_parse_proof_log_line_unknown_rule() {
    assert!(parse_proof_log_line("UNKNOWN 0 1").is_none());
}

#[test]
fn test_parse_proof_log_line_invalid_indices() {
    assert!(parse_proof_log_line("TRANS abc def").is_none());
}

#[test]
fn test_parse_proof_log_full() {
    let log = "REFL x\nREFL y\nTRANS 0 1\n";
    let tree = parse_proof_log(log);
    assert_eq!(tree.step_count(), 3);
    assert_eq!(tree.conclusion, Some(2));
    assert!(tree.is_valid());
}

#[test]
fn test_parse_proof_log_with_blank_lines() {
    let log = "REFL x\n\nBETA (\\x. x) y\n\n";
    let tree = parse_proof_log(log);
    assert_eq!(tree.step_count(), 2);
}

#[test]
fn test_parse_proof_log_empty_string() {
    let tree = parse_proof_log("");
    assert!(tree.is_empty());
    assert!(tree.conclusion.is_none());
}

// ============================================================================
// HOL Light: Axiom Tracker Tests
// ============================================================================

#[test]
fn test_axiom_tracker_empty() {
    let tracker = HolLightAxiomTracker::new();
    assert_eq!(tracker.theorem_count(), 0);
    assert!(tracker.theorem_names().is_empty());
}

#[test]
fn test_axiom_tracker_add_dependency() {
    let mut tracker = HolLightAxiomTracker::new();
    tracker.add_dependency("TRUTH", "ETA_AX");

    assert!(tracker.has_dependencies("TRUTH"));
    assert_eq!(tracker.get_dependencies("TRUTH"), vec!["ETA_AX"]);
    assert_eq!(tracker.theorem_count(), 1);
}

#[test]
fn test_axiom_tracker_multiple_dependencies() {
    let mut tracker = HolLightAxiomTracker::new();
    tracker.add_dependencies("SELECT_ELIM", &["SELECT_AX", "ETA_AX"]);

    let deps = tracker.get_dependencies("SELECT_ELIM");
    assert_eq!(deps.len(), 2);
    assert!(deps.contains(&"SELECT_AX"));
    assert!(deps.contains(&"ETA_AX"));
}

#[test]
fn test_axiom_tracker_no_dependencies() {
    let tracker = HolLightAxiomTracker::new();
    assert!(!tracker.has_dependencies("UNKNOWN"));
    assert!(tracker.get_dependencies("UNKNOWN").is_empty());
}

#[test]
fn test_axiom_tracker_standard_axioms_only() {
    let mut tracker = HolLightAxiomTracker::new();
    tracker.add_dependencies("STANDARD_THM", &["INFINITY_AX", "ETA_AX"]);
    tracker.add_dependency("CHOICE_THM", "SELECT_AX");

    assert!(tracker.uses_only_standard_axioms("STANDARD_THM"));
    assert!(tracker.uses_only_standard_axioms("CHOICE_THM"));
}

#[test]
fn test_axiom_tracker_nonstandard_axioms() {
    let mut tracker = HolLightAxiomTracker::new();
    tracker.add_dependency("CUSTOM_THM", "MY_CUSTOM_AXIOM");

    assert!(!tracker.uses_only_standard_axioms("CUSTOM_THM"));
}

#[test]
fn test_axiom_tracker_no_axiom_deps_is_standard() {
    let tracker = HolLightAxiomTracker::new();
    // A theorem with no recorded axiom dependencies is considered standard.
    assert!(tracker.uses_only_standard_axioms("PURE_THM"));
}

#[test]
fn test_axiom_tracker_counts() {
    let mut tracker = HolLightAxiomTracker::new();
    tracker.add_dependency("A", "INFINITY_AX");
    tracker.add_dependency("B", "ETA_AX");
    tracker.add_dependency("C", "USER_AXIOM");

    assert_eq!(tracker.theorem_count(), 3);
    assert_eq!(tracker.standard_axiom_count(), 2);
    assert_eq!(tracker.nonstandard_axiom_count(), 1);
}

#[test]
fn test_axiom_tracker_theorem_names_sorted() {
    let mut tracker = HolLightAxiomTracker::new();
    tracker.add_dependency("Z_THM", "ETA_AX");
    tracker.add_dependency("A_THM", "ETA_AX");
    tracker.add_dependency("M_THM", "ETA_AX");

    let names = tracker.theorem_names();
    assert_eq!(names, vec!["A_THM", "M_THM", "Z_THM"]);
}

// ============================================================================
// HOL4: Theory Graph Tests
// ============================================================================

use super::hol4::{
    parse_theory_graph, Hol4ExportFormat, Hol4TheoryGraph, Hol4TheoryNode, Hol4TypeOp,
};

#[test]
fn test_theory_graph_empty() {
    let graph = Hol4TheoryGraph::new();
    assert!(graph.is_empty());
    assert_eq!(graph.theory_count(), 0);
    assert!(graph.theory_names().is_empty());
    assert!(!graph.has_cycle());
}

#[test]
fn test_theory_graph_add_single() {
    let mut graph = Hol4TheoryGraph::new();
    graph.add_theory_with_parents("min", &[]);
    assert_eq!(graph.theory_count(), 1);
    assert!(!graph.is_empty());
    assert_eq!(graph.theory_names(), vec!["min"]);
}

#[test]
fn test_theory_graph_parent_child() {
    let mut graph = Hol4TheoryGraph::new();
    graph.add_theory_with_parents("min", &[]);
    graph.add_theory_with_parents("bool", &["min"]);
    graph.add_theory_with_parents("num", &["min", "bool"]);

    assert_eq!(graph.parents_of("bool"), vec!["min"]);
    assert_eq!(graph.parents_of("min"), Vec::<&str>::new());

    let children = graph.children_of("min");
    assert!(children.contains(&"bool"));
    assert!(children.contains(&"num"));
}

#[test]
fn test_theory_graph_roots() {
    let mut graph = Hol4TheoryGraph::new();
    graph.add_theory_with_parents("min", &[]);
    graph.add_theory_with_parents("bool", &["min"]);
    graph.add_theory_with_parents("num", &["bool"]);

    let roots = graph.roots();
    assert_eq!(roots, vec!["min"]);
}

#[test]
fn test_theory_graph_leaves() {
    let mut graph = Hol4TheoryGraph::new();
    graph.add_theory_with_parents("min", &[]);
    graph.add_theory_with_parents("bool", &["min"]);
    graph.add_theory_with_parents("num", &["bool"]);

    let mut leaves = graph.leaves();
    leaves.sort();
    assert!(leaves.contains(&"num"));
}

#[test]
fn test_theory_graph_transitive_dependencies() {
    let mut graph = Hol4TheoryGraph::new();
    graph.add_theory_with_parents("min", &[]);
    graph.add_theory_with_parents("bool", &["min"]);
    graph.add_theory_with_parents("num", &["bool"]);
    graph.add_theory_with_parents("list", &["bool", "num"]);

    let deps = graph.transitive_dependencies("list");
    assert!(deps.contains(&"bool".to_owned()));
    assert!(deps.contains(&"num".to_owned()));
    assert!(deps.contains(&"min".to_owned()));
    assert!(!deps.contains(&"list".to_owned()));
}

#[test]
fn test_theory_graph_no_cycle() {
    let mut graph = Hol4TheoryGraph::new();
    graph.add_theory_with_parents("min", &[]);
    graph.add_theory_with_parents("bool", &["min"]);
    graph.add_theory_with_parents("num", &["bool"]);
    assert!(!graph.has_cycle());
}

#[test]
fn test_theory_graph_with_cycle() {
    let mut graph = Hol4TheoryGraph::new();
    graph.add_theory_with_parents("a", &["b"]);
    graph.add_theory_with_parents("b", &["a"]);
    assert!(graph.has_cycle());
}

#[test]
fn test_theory_graph_get_theory() {
    let mut graph = Hol4TheoryGraph::new();
    graph.add_theory(Hol4TheoryNode {
        name: "bool".to_owned(),
        parents: vec!["min".to_owned()],
        theorem_count: Some(42),
        type_count: Some(1),
        constant_count: Some(5),
    });

    let node = graph.get_theory("bool").expect("should find theory");
    assert_eq!(node.name, "bool");
    assert_eq!(node.theorem_count, Some(42));
    assert_eq!(node.type_count, Some(1));
    assert_eq!(node.constant_count, Some(5));
    assert!(graph.get_theory("nonexistent").is_none());
}

// ============================================================================
// HOL4: parse_theory_graph Tests
// ============================================================================

#[test]
fn test_parse_theory_graph_basic() {
    let text = "min:\nbool: min\nnum: min, bool\n";
    let graph = parse_theory_graph(text);
    assert_eq!(graph.theory_count(), 3);
    assert_eq!(graph.parents_of("bool"), vec!["min"]);
    let num_parents = graph.parents_of("num");
    assert!(num_parents.contains(&"min"));
    assert!(num_parents.contains(&"bool"));
}

#[test]
fn test_parse_theory_graph_with_comments() {
    let text = "# HOL4 theory hierarchy\nmin:\n# bool depends on min\nbool: min\n";
    let graph = parse_theory_graph(text);
    assert_eq!(graph.theory_count(), 2);
}

#[test]
fn test_parse_theory_graph_empty() {
    let graph = parse_theory_graph("");
    assert!(graph.is_empty());
}

#[test]
fn test_parse_theory_graph_blank_lines() {
    let text = "\nmin:\n\nbool: min\n\n";
    let graph = parse_theory_graph(text);
    assert_eq!(graph.theory_count(), 2);
}

#[test]
fn test_parse_theory_graph_no_parents() {
    let text = "min:\nbasic:\n";
    let graph = parse_theory_graph(text);
    assert_eq!(graph.roots().len(), 2);
}

// ============================================================================
// HOL4: Hol4ExportFormat Tests
// ============================================================================

#[test]
fn test_export_format_extensions() {
    assert_eq!(Hol4ExportFormat::ArticleFormat.extension(), "art");
    assert_eq!(Hol4ExportFormat::SExpFormat.extension(), "sexp");
    assert_eq!(Hol4ExportFormat::JsonFormat.extension(), "json");
}

#[test]
fn test_export_format_descriptions() {
    assert!(!Hol4ExportFormat::ArticleFormat.description().is_empty());
    assert!(!Hol4ExportFormat::SExpFormat.description().is_empty());
    assert!(!Hol4ExportFormat::JsonFormat.description().is_empty());
}

#[test]
fn test_export_format_import_support() {
    assert!(Hol4ExportFormat::ArticleFormat.is_import_supported());
    assert!(!Hol4ExportFormat::SExpFormat.is_import_supported());
    assert!(!Hol4ExportFormat::JsonFormat.is_import_supported());
}

// ============================================================================
// HOL4: Hol4TypeOp Tests
// ============================================================================

#[test]
fn test_type_op_builtin_names() {
    assert_eq!(Hol4TypeOp::Bool.name(), "bool");
    assert_eq!(Hol4TypeOp::Fun.name(), "fun");
    assert_eq!(Hol4TypeOp::Ind.name(), "ind");
    assert_eq!(Hol4TypeOp::Num.name(), "num");
    assert_eq!(Hol4TypeOp::List.name(), "list");
    assert_eq!(Hol4TypeOp::Option.name(), "option");
    assert_eq!(Hol4TypeOp::Prod.name(), "prod");
    assert_eq!(Hol4TypeOp::Sum.name(), "sum");
}

#[test]
fn test_type_op_arities() {
    assert_eq!(Hol4TypeOp::Bool.arity(), 0);
    assert_eq!(Hol4TypeOp::Ind.arity(), 0);
    assert_eq!(Hol4TypeOp::Num.arity(), 0);
    assert_eq!(Hol4TypeOp::Fun.arity(), 2);
    assert_eq!(Hol4TypeOp::Prod.arity(), 2);
    assert_eq!(Hol4TypeOp::Sum.arity(), 2);
    assert_eq!(Hol4TypeOp::List.arity(), 1);
    assert_eq!(Hol4TypeOp::Option.arity(), 1);
}

#[test]
fn test_type_op_builtin_check() {
    assert!(Hol4TypeOp::Bool.is_builtin());
    assert!(Hol4TypeOp::Fun.is_builtin());
    assert!(Hol4TypeOp::Num.is_builtin());
    assert!(!Hol4TypeOp::UserDefined {
        name: "tree".to_owned(),
        arity: 1,
    }
    .is_builtin());
}

#[test]
fn test_type_op_from_name_builtin() {
    assert_eq!(Hol4TypeOp::from_name("bool"), Hol4TypeOp::Bool);
    assert_eq!(Hol4TypeOp::from_name("fun"), Hol4TypeOp::Fun);
    assert_eq!(Hol4TypeOp::from_name("->"), Hol4TypeOp::Fun);
    assert_eq!(Hol4TypeOp::from_name("num"), Hol4TypeOp::Num);
    assert_eq!(Hol4TypeOp::from_name("list"), Hol4TypeOp::List);
}

#[test]
fn test_type_op_from_name_user_defined() {
    let op = Hol4TypeOp::from_name("tree");
    assert!(!op.is_builtin());
    assert_eq!(op.name(), "tree");
    assert_eq!(op.arity(), 0); // Default arity for unknown.
}

#[test]
fn test_type_op_from_name_with_arity() {
    let op = Hol4TypeOp::from_name_with_arity("tree", 2);
    assert!(!op.is_builtin());
    assert_eq!(op.name(), "tree");
    assert_eq!(op.arity(), 2);

    // Builtin types ignore the explicit arity.
    let op = Hol4TypeOp::from_name_with_arity("bool", 5);
    assert!(op.is_builtin());
    assert_eq!(op.arity(), 0); // Bool arity is always 0.
}

// ============================================================================
// Edge Case Tests: Empty Theories
// ============================================================================

#[test]
fn test_empty_hol_light_theory_all_methods() {
    let importer = HolLightImporter::default();
    let theory = importer.import_theory("empty", &[]).expect("empty theory");

    assert_eq!(theory.theory_name, "empty");
    assert_eq!(theory.total_constants(), 0);
    assert!(theory.min_trust_level().is_none());
    assert!(theory.theorem_names().is_empty());
    assert!(theory.axiom_names().is_empty());
    assert_eq!(theory.combined_axiom_profile(), AxiomProfile::NONE);
    assert_eq!(theory.statistics.success_rate(), 1.0);
}

#[test]
fn test_empty_hol4_theory_all_methods() {
    let importer = Hol4Importer::default();
    let theory = importer
        .import_theory("empty", &[], &[])
        .expect("empty theory");

    assert_eq!(theory.total_declarations(), 0);
    assert!(theory.min_trust_level().is_none());
    assert!(theory.theorem_names().is_empty());
    assert!(!theory.has_parents());
    assert_eq!(theory.combined_axiom_profile(), AxiomProfile::NONE);
}

// ============================================================================
// Edge Case Tests: Duplicate Constants
// ============================================================================

#[test]
fn test_duplicate_constants_same_name_same_system() {
    let mut u = HolUnifier::new();
    let id1 = u.add_hol_light_constant(
        "A.True",
        "Prop",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    let id2 = u.add_hol_light_constant(
        "B.True",
        "Prop",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );

    // Both get different IDs.
    assert_ne!(id1, id2);
    assert_eq!(u.len(), 2);

    // No cross-system equivalences.
    let pairs = u.find_equivalences();
    assert!(pairs.is_empty());

    // But batch_unify should detect the ambiguity.
    let results = u.batch_unify();
    assert_eq!(results.len(), 1); // One base name "True"
    assert!(results[0].has_conflicts()); // Ambiguous
}

#[test]
fn test_duplicate_constants_different_types() {
    let mut u = HolUnifier::new();
    u.add_hol_light_constant(
        "A.f",
        "Nat->Nat",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    u.add_hol4_constant(
        "B.f",
        "Int->Int",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );

    let results = u.batch_unify();
    assert_eq!(results.len(), 1);
    let r = &results[0];
    assert!(r.has_conflicts()); // Type mismatch
    assert!(r.match_score <= 0.5);
}

// ============================================================================
// Edge Case Tests: Type Mismatches
// ============================================================================

#[test]
fn test_unify_constant_type_mismatch_details() {
    let mut u = HolUnifier::new();
    u.add_hol_light_constant(
        "X.add",
        "Nat->Nat->Nat",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    u.add_hol4_constant(
        "Y.add",
        "Int->Int->Int",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    u.add_isabelle_constant(
        "Z.add",
        "Real->Real->Real",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );

    let r = u.unify_constant("add");
    assert!(r.has_conflicts());
    assert!(r.alignment.is_fully_aligned());
    // 3 different type reprs -> conflict
    assert!(r
        .conflict_reasons
        .iter()
        .any(|c| c.contains("type mismatch")));
}

#[test]
fn test_cross_system_statistics_mixed() {
    let mut u = HolUnifier::new();
    // Matched: True across HL and H4
    u.add_hol_light_constant(
        "A.True",
        "Prop",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    u.add_hol4_constant(
        "B.True",
        "Prop",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    // Unmatched: unique names
    u.add_isabelle_constant(
        "C.unique",
        "T",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    // Conflict: type mismatch
    u.add_hol_light_constant(
        "D.add",
        "Nat",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );
    u.add_hol4_constant(
        "E.add",
        "Int",
        hol_profile(),
        TrustLevel::CertificateReplayed,
    );

    let stats = u.cross_system_statistics();
    assert_eq!(stats.matched, 2); // True and add are both cross-system
    assert_eq!(stats.unmatched, 1); // "unique"
    assert_eq!(stats.conflicts, 1); // "add" has type conflict
}
