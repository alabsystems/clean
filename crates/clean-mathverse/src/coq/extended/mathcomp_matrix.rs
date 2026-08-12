// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! MathComp matrix theory import for gamma-crown axiom elimination.
//!
//! Extracts matrix algebra lemmas from Coq's MathComp library (`matrix.v`,
//! `mxalgebra.v`, `mxpoly.v`) and classifies them by which gamma-crown
//! conjectures (C004, C006, C010) they can help discharge.
//!
//! MathComp's ssreflect-based formalization provides:
//! - Matrix multiplication associativity and distributivity (targets C010)
//! - Block matrix decomposition and composition (targets C006)
//! - Matrix rank theory via `\rank` notation (targets C004)
//!
//! ## Pipeline
//!
//! ```text
//! CicDeclaration (from coq_extended pipeline)
//!     |
//!     v
//! extract_matrix_lemmas() -- filter mathcomp.algebra.matrix/mxalgebra
//!     |
//!     v
//! classify_gamma_crown_target() -- map to C004/C006/C010
//!     |
//!     v
//! MathCompMatrixImportResult -- statistics for trust accounting
//! ```

use std::path::PathBuf;

use super::cic_extract::{CicDeclKind, CicDeclaration};
use super::library_config::{CoqLibraryConfig, ImportPhase, PhaseModuleSet};
use super::sexp_parser::SexpValue;
use crate::types::AxiomProfile;

// ---------------------------------------------------------------------------
// MathCompMatrixOp
// ---------------------------------------------------------------------------

/// Matrix operation kind detected from MathComp declaration names.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum MathCompMatrixOp {
    /// Matrix multiplication (`mulmx`, `*m`).
    MatMul,
    /// Matrix addition (`addmx`, `+m`).
    MatAdd,
    /// Matrix transpose (`trmx`, `^T`).
    Transpose,
    /// Scalar-matrix multiplication (`scalemx`, `*:`).
    ScalarMul,
    /// Matrix rank (`\rank`, `mxrank`).
    MatRank,
    /// Matrix determinant (`\det`, `determinant`).
    Determinant,
    /// Matrix inverse (`invmx`).
    MatInverse,
    /// Block diagonal construction (`block_mx`, `diag_mx`).
    BlockDiag,
    /// Matrix trace (`\tr`, `mxtrace`).
    Trace,
    /// Zero matrix (`0`, `const_mx 0`).
    ZeroMat,
    /// Identity matrix (`1%:M`, `scalar_mx 1`).
    IdentityMat,
    /// Block matrix decomposition (`ulsubmx`, `ursubmx`, `dlsubmx`, `drsubmx`).
    BlockDecomposition,
}

// ---------------------------------------------------------------------------
// GammaCrownTarget
// ---------------------------------------------------------------------------

/// Which gamma-crown conjecture a MathComp matrix lemma targets.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum GammaCrownTarget {
    /// C004: Matrix rank properties (rank-nullity, sub-additivity).
    C004MatrixRank,
    /// C006: Block matrix decomposition (blockwise CROWN equivalence).
    C006BlockDecomposition,
    /// C010: Matrix multiplication associativity (affine transform composition).
    C010MatMulAssoc,
    /// No specific gamma-crown target identified.
    None,
}

// ---------------------------------------------------------------------------
// MathCompMatrixLemma
// ---------------------------------------------------------------------------

/// A matrix theory lemma extracted from MathComp with gamma-crown targeting.
#[derive(Clone, Debug)]
pub struct MathCompMatrixLemma {
    /// Fully qualified Coq name (e.g., `mathcomp.algebra.matrix.mulmxA`).
    pub name: String,
    /// Detected matrix operation.
    pub op: MathCompMatrixOp,
    /// Raw s-expression of the type (statement).
    pub statement_sexp: Option<SexpValue>,
    /// Raw s-expression of the body (proof term).
    pub proof_sexp: Option<SexpValue>,
    /// Which gamma-crown axiom this lemma might discharge.
    pub target_axiom: Option<String>,
    /// Source module path.
    pub module_path: String,
    /// Axiom profile bits.
    pub axiom_profile: AxiomProfile,
}

// ---------------------------------------------------------------------------
// MathCompMatrixImportResult
// ---------------------------------------------------------------------------

/// Statistics from a MathComp matrix theory import run.
#[derive(Clone, Debug, Default)]
pub struct MathCompMatrixImportResult {
    /// Total declarations scanned.
    pub declarations_scanned: usize,
    /// Declarations identified as matrix-related.
    pub matrix_lemmas_extracted: usize,
    /// Lemmas classified with a gamma-crown target.
    pub target_classified: usize,
    /// Lemmas targeting C004 (matrix rank).
    pub c004_matches: usize,
    /// Lemmas targeting C006 (block decomposition).
    pub c006_matches: usize,
    /// Lemmas targeting C010 (matrix mul associativity).
    pub c010_matches: usize,
    /// Per-operation counts.
    pub op_counts: OpCounts,
}

/// Per-operation count tracking.
#[derive(Clone, Debug, Default)]
pub struct OpCounts {
    pub mat_mul: usize,
    pub mat_add: usize,
    pub transpose: usize,
    pub scalar_mul: usize,
    pub mat_rank: usize,
    pub determinant: usize,
    pub mat_inverse: usize,
    pub block_diag: usize,
    pub trace: usize,
    pub zero_mat: usize,
    pub identity_mat: usize,
    pub block_decomposition: usize,
}

impl MathCompMatrixImportResult {
    /// Summary line for progress reporting.
    #[must_use]
    pub fn summary(&self) -> String {
        format!(
            "scanned={}, matrix_extracted={}, classified={}, \
             C004={}, C006={}, C010={}",
            self.declarations_scanned,
            self.matrix_lemmas_extracted,
            self.target_classified,
            self.c004_matches,
            self.c006_matches,
            self.c010_matches,
        )
    }
}

// ---------------------------------------------------------------------------
// Matrix module prefixes
// ---------------------------------------------------------------------------

/// Module prefixes that contain matrix theory in MathComp.
const MATRIX_MODULE_PREFIXES: &[&str] = &[
    "mathcomp.algebra.matrix",
    "mathcomp.algebra.mxalgebra",
    "mathcomp.algebra.mxpoly",
    "mathcomp.algebra.mxrepresentation",
    "mathcomp.algebra.vector",
    "mathcomp.algebra.mxlinalg",
];

/// Name fragments that indicate matrix operations.
const MATRIX_NAME_PATTERNS: &[(&str, MathCompMatrixOp)] = &[
    // Multiplication
    ("mulmx", MathCompMatrixOp::MatMul),
    ("mulmxA", MathCompMatrixOp::MatMul),
    ("mul_mx", MathCompMatrixOp::MatMul),
    ("mxmul", MathCompMatrixOp::MatMul),
    // Addition
    ("addmx", MathCompMatrixOp::MatAdd),
    ("add_mx", MathCompMatrixOp::MatAdd),
    // Transpose
    ("trmx", MathCompMatrixOp::Transpose),
    ("tr_mx", MathCompMatrixOp::Transpose),
    ("transpose", MathCompMatrixOp::Transpose),
    // Scalar multiplication
    ("scalemx", MathCompMatrixOp::ScalarMul),
    ("scale_mx", MathCompMatrixOp::ScalarMul),
    ("scalar_mx", MathCompMatrixOp::ScalarMul),
    // Rank
    ("mxrank", MathCompMatrixOp::MatRank),
    ("rank", MathCompMatrixOp::MatRank),
    // Determinant
    ("det", MathCompMatrixOp::Determinant),
    ("determinant", MathCompMatrixOp::Determinant),
    ("cofactor", MathCompMatrixOp::Determinant),
    // Inverse
    ("invmx", MathCompMatrixOp::MatInverse),
    ("inv_mx", MathCompMatrixOp::MatInverse),
    // Block diagonal / decomposition
    ("block_mx", MathCompMatrixOp::BlockDiag),
    ("diag_mx", MathCompMatrixOp::BlockDiag),
    ("diag_block", MathCompMatrixOp::BlockDiag),
    // Block sub-matrices
    ("ulsubmx", MathCompMatrixOp::BlockDecomposition),
    ("ursubmx", MathCompMatrixOp::BlockDecomposition),
    ("dlsubmx", MathCompMatrixOp::BlockDecomposition),
    ("drsubmx", MathCompMatrixOp::BlockDecomposition),
    ("submx", MathCompMatrixOp::BlockDecomposition),
    // Row/column space (rank-related)
    ("row_free", MathCompMatrixOp::MatRank),
    ("col_free", MathCompMatrixOp::MatRank),
    ("kermx", MathCompMatrixOp::MatRank),
    ("cokermx", MathCompMatrixOp::MatRank),
    ("row_full", MathCompMatrixOp::MatRank),
    ("col_full", MathCompMatrixOp::MatRank),
    // Trace
    ("mxtrace", MathCompMatrixOp::Trace),
    ("tr_diag", MathCompMatrixOp::Trace),
    // Zero / Identity
    ("const_mx", MathCompMatrixOp::ZeroMat),
    ("scalar_mx_1", MathCompMatrixOp::IdentityMat),
    ("pid_mx", MathCompMatrixOp::IdentityMat),
];

// ---------------------------------------------------------------------------
// Core extraction logic
// ---------------------------------------------------------------------------

/// Check whether a declaration is from a MathComp matrix module.
fn is_matrix_module(decl: &CicDeclaration) -> bool {
    let path = &decl.module_path;
    let name = &decl.name;
    MATRIX_MODULE_PREFIXES
        .iter()
        .any(|prefix| path.starts_with(prefix) || name.starts_with(prefix))
}

/// Detect which matrix operation a declaration relates to, based on name patterns.
fn detect_matrix_op(name: &str) -> Option<MathCompMatrixOp> {
    // Extract the short name (last component after the last dot).
    let short_name = name.rsplit('.').next().unwrap_or(name);

    // Check exact matches and substring matches against known patterns.
    for &(pattern, op) in MATRIX_NAME_PATTERNS {
        if short_name.contains(pattern) {
            return Some(op);
        }
    }

    // Fallback: if the declaration is in a matrix module but does not match
    // a specific pattern, check for common suffix patterns.
    if short_name.ends_with("mx") || short_name.starts_with("mx") {
        return Some(MathCompMatrixOp::MatMul); // generic matrix lemma
    }

    None
}

/// Extract matrix-related lemmas from a slice of CIC declarations.
///
/// Filters declarations from MathComp matrix modules, detects the matrix
/// operation they concern, and wraps them as [`MathCompMatrixLemma`] values.
#[must_use]
pub fn extract_matrix_lemmas(decls: &[CicDeclaration]) -> Vec<MathCompMatrixLemma> {
    let mut out = Vec::new();

    for decl in decls {
        if !is_matrix_module(decl) {
            continue;
        }

        // Only extract theorems, lemmas, and definitions (not modules/classes).
        match decl.kind {
            CicDeclKind::Theorem
            | CicDeclKind::Lemma
            | CicDeclKind::Definition
            | CicDeclKind::CanonicalStructure => {}
            _ => continue,
        }

        let op = match detect_matrix_op(&decl.name) {
            Some(op) => op,
            None => continue,
        };

        let lemma = MathCompMatrixLemma {
            name: decl.name.clone(),
            op,
            statement_sexp: decl.type_sexp.clone(),
            proof_sexp: decl.body_sexp.clone(),
            target_axiom: None, // filled in by classify_gamma_crown_target
            module_path: decl.module_path.clone(),
            axiom_profile: decl.axiom_profile,
        };

        out.push(lemma);
    }

    out
}

/// Classify which gamma-crown conjecture a matrix lemma targets.
///
/// Mapping rules:
/// - `MatRank` operations -> C004 (matrix rank properties)
/// - `BlockDiag` / `BlockDecomposition` -> C006 (block matrix decomposition)
/// - `MatMul` associativity/composition -> C010 (affine transform composition)
/// - Other operations -> `GammaCrownTarget::None`
#[must_use]
pub fn classify_gamma_crown_target(lemma: &MathCompMatrixLemma) -> GammaCrownTarget {
    // First check name-based heuristics for more precise classification.
    let short_name = lemma.name.rsplit('.').next().unwrap_or(&lemma.name);

    // C010: matrix multiplication associativity
    if short_name.contains("mulmxA")
        || short_name.contains("mul_mx_assoc")
        || short_name.contains("mulmx_assoc")
        || (lemma.op == MathCompMatrixOp::MatMul && short_name.contains("assoc"))
    {
        return GammaCrownTarget::C010MatMulAssoc;
    }

    // C010: affine transform / composition lemmas
    if short_name.contains("mulmxDl")
        || short_name.contains("mulmxDr")
        || short_name.contains("mul0mx")
        || short_name.contains("mulmx0")
        || short_name.contains("mul1mx")
        || short_name.contains("mulmx1")
    {
        return GammaCrownTarget::C010MatMulAssoc;
    }

    // C004: rank-related lemmas
    if short_name.contains("rank")
        || short_name.contains("mxrank")
        || short_name.contains("row_free")
        || short_name.contains("col_free")
        || short_name.contains("kermx")
        || short_name.contains("cokermx")
    {
        return GammaCrownTarget::C004MatrixRank;
    }

    // C006: block matrix decomposition
    if short_name.contains("block_mx")
        || short_name.contains("ulsubmx")
        || short_name.contains("ursubmx")
        || short_name.contains("dlsubmx")
        || short_name.contains("drsubmx")
        || short_name.contains("submx")
        || short_name.contains("diag_block")
    {
        return GammaCrownTarget::C006BlockDecomposition;
    }

    // Operation-based fallback classification.
    match lemma.op {
        MathCompMatrixOp::MatRank => GammaCrownTarget::C004MatrixRank,
        MathCompMatrixOp::BlockDiag | MathCompMatrixOp::BlockDecomposition => {
            GammaCrownTarget::C006BlockDecomposition
        }
        MathCompMatrixOp::MatMul => GammaCrownTarget::C010MatMulAssoc,
        _ => GammaCrownTarget::None,
    }
}

/// Annotate a lemma with its gamma-crown target axiom string.
///
/// Mutates the `target_axiom` field based on classification.
pub(crate) fn annotate_target(lemma: &mut MathCompMatrixLemma) {
    let target = classify_gamma_crown_target(lemma);
    lemma.target_axiom = match target {
        GammaCrownTarget::C004MatrixRank => Some("C004".to_owned()),
        GammaCrownTarget::C006BlockDecomposition => Some("C006".to_owned()),
        GammaCrownTarget::C010MatMulAssoc => Some("C010".to_owned()),
        GammaCrownTarget::None => None,
    };
}

// ---------------------------------------------------------------------------
// Import pipeline
// ---------------------------------------------------------------------------

/// Run the MathComp matrix theory import on a set of CIC declarations.
///
/// Extracts matrix lemmas, classifies gamma-crown targets, and returns
/// aggregate statistics.
#[must_use]
pub fn run_matrix_import(
    _config: &CoqLibraryConfig,
    decls: &[CicDeclaration],
) -> MathCompMatrixImportResult {
    let mut result = MathCompMatrixImportResult {
        declarations_scanned: decls.len(),
        ..Default::default()
    };

    let mut lemmas = extract_matrix_lemmas(decls);
    result.matrix_lemmas_extracted = lemmas.len();

    for lemma in &mut lemmas {
        annotate_target(lemma);
        count_op(lemma.op, &mut result.op_counts);

        let target = classify_gamma_crown_target(lemma);
        if target != GammaCrownTarget::None {
            result.target_classified += 1;
        }
        match target {
            GammaCrownTarget::C004MatrixRank => result.c004_matches += 1,
            GammaCrownTarget::C006BlockDecomposition => result.c006_matches += 1,
            GammaCrownTarget::C010MatMulAssoc => result.c010_matches += 1,
            GammaCrownTarget::None => {}
        }
    }

    result
}

fn count_op(op: MathCompMatrixOp, counts: &mut OpCounts) {
    match op {
        MathCompMatrixOp::MatMul => counts.mat_mul += 1,
        MathCompMatrixOp::MatAdd => counts.mat_add += 1,
        MathCompMatrixOp::Transpose => counts.transpose += 1,
        MathCompMatrixOp::ScalarMul => counts.scalar_mul += 1,
        MathCompMatrixOp::MatRank => counts.mat_rank += 1,
        MathCompMatrixOp::Determinant => counts.determinant += 1,
        MathCompMatrixOp::MatInverse => counts.mat_inverse += 1,
        MathCompMatrixOp::BlockDiag => counts.block_diag += 1,
        MathCompMatrixOp::Trace => counts.trace += 1,
        MathCompMatrixOp::ZeroMat => counts.zero_mat += 1,
        MathCompMatrixOp::IdentityMat => counts.identity_mat += 1,
        MathCompMatrixOp::BlockDecomposition => counts.block_decomposition += 1,
    }
}

// ---------------------------------------------------------------------------
// Library configuration
// ---------------------------------------------------------------------------

/// Create a [`CoqLibraryConfig`] focused on MathComp matrix theory.
///
/// Includes only the `mathcomp.algebra.matrix`, `mathcomp.algebra.mxalgebra`,
/// and related modules. Uses `CLASSICAL` axiom profile since MathComp
/// relies on decidable equality and classical reasoning.
#[must_use]
pub fn mathcomp_matrix_config(sexp_dir: PathBuf) -> CoqLibraryConfig {
    CoqLibraryConfig {
        name: "mathcomp-matrix".to_owned(),
        sexp_dir,
        default_axiom_profile: AxiomProfile::CLASSICAL,
        expected_theorems: 5_000,
        phase_modules: vec![
            PhaseModuleSet {
                phase: ImportPhase::Core,
                include_prefixes: vec![
                    // ssreflect foundations needed by matrix theory
                    "mathcomp.ssreflect.".into(),
                    "mathcomp.ssrbool".into(),
                    "mathcomp.ssrnat".into(),
                    "mathcomp.ssrfun".into(),
                    "mathcomp.eqtype".into(),
                    "mathcomp.choice".into(),
                    "mathcomp.seq".into(),
                    "mathcomp.fintype".into(),
                    "mathcomp.bigop".into(),
                ],
            },
            PhaseModuleSet {
                phase: ImportPhase::Algebra,
                include_prefixes: vec![
                    // Core algebra needed by matrix
                    "mathcomp.algebra.ssralg".into(),
                    "mathcomp.algebra.ssrnum".into(),
                    "mathcomp.algebra.ring_quotient".into(),
                    // Matrix modules
                    "mathcomp.algebra.matrix".into(),
                    "mathcomp.algebra.mxalgebra".into(),
                    "mathcomp.algebra.mxpoly".into(),
                    "mathcomp.algebra.mxrepresentation".into(),
                    "mathcomp.algebra.vector".into(),
                    "mathcomp.algebra.mxlinalg".into(),
                ],
            },
            PhaseModuleSet {
                phase: ImportPhase::Full,
                include_prefixes: vec![], // everything
            },
        ],
        exclude_prefixes: vec!["mathcomp.test.".into(), "mathcomp.examples.".into()],
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: create a CicDeclaration with the given name and module path.
    fn make_decl(name: &str, module_path: &str, kind: CicDeclKind) -> CicDeclaration {
        CicDeclaration {
            name: name.to_owned(),
            kind,
            type_sexp: Some(SexpValue::Atom("Prop".to_owned())),
            body_sexp: Some(SexpValue::Atom("proof".to_owned())),
            axiom_profile: AxiomProfile::CLASSICAL,
            module_path: module_path.to_owned(),
        }
    }

    #[test]
    fn test_extract_matrix_lemmas_from_matrix_module() {
        let decls = vec![
            make_decl(
                "mathcomp.algebra.matrix.mulmxA",
                "mathcomp.algebra.matrix",
                CicDeclKind::Lemma,
            ),
            make_decl(
                "mathcomp.algebra.matrix.addmx_comm",
                "mathcomp.algebra.matrix",
                CicDeclKind::Theorem,
            ),
            make_decl(
                "mathcomp.algebra.matrix.trmx_mul",
                "mathcomp.algebra.matrix",
                CicDeclKind::Lemma,
            ),
            // Not from matrix module — should be filtered out.
            make_decl(
                "mathcomp.ssreflect.ssrnat.addn0",
                "mathcomp.ssreflect",
                CicDeclKind::Lemma,
            ),
        ];

        let lemmas = extract_matrix_lemmas(&decls);
        assert_eq!(lemmas.len(), 3, "should extract 3 matrix lemmas");
        assert_eq!(lemmas[0].name, "mathcomp.algebra.matrix.mulmxA");
        assert_eq!(lemmas[0].op, MathCompMatrixOp::MatMul);
        assert_eq!(lemmas[1].op, MathCompMatrixOp::MatAdd);
        assert_eq!(lemmas[2].op, MathCompMatrixOp::Transpose);
    }

    #[test]
    fn test_extract_skips_non_theorem_kinds() {
        let decls = vec![
            make_decl(
                "mathcomp.algebra.matrix.mulmxA",
                "mathcomp.algebra.matrix",
                CicDeclKind::Module,
            ),
            make_decl(
                "mathcomp.algebra.matrix.MatrixRing",
                "mathcomp.algebra.matrix",
                CicDeclKind::Class,
            ),
            make_decl(
                "mathcomp.algebra.matrix.nat_ind",
                "mathcomp.algebra.matrix",
                CicDeclKind::Inductive,
            ),
        ];

        let lemmas = extract_matrix_lemmas(&decls);
        assert!(
            lemmas.is_empty(),
            "should skip non-theorem/lemma/definition kinds"
        );
    }

    #[test]
    fn test_detect_matrix_op_mulmx() {
        assert_eq!(
            detect_matrix_op("mathcomp.algebra.matrix.mulmxA"),
            Some(MathCompMatrixOp::MatMul)
        );
    }

    #[test]
    fn test_detect_matrix_op_rank() {
        assert_eq!(
            detect_matrix_op("mathcomp.algebra.mxalgebra.mxrank_mul"),
            Some(MathCompMatrixOp::MatRank)
        );
    }

    #[test]
    fn test_detect_matrix_op_block() {
        assert_eq!(
            detect_matrix_op("mathcomp.algebra.matrix.block_mx_col"),
            Some(MathCompMatrixOp::BlockDiag)
        );
        assert_eq!(
            detect_matrix_op("mathcomp.algebra.matrix.ulsubmx_block"),
            Some(MathCompMatrixOp::BlockDecomposition)
        );
    }

    #[test]
    fn test_detect_matrix_op_det() {
        assert_eq!(
            detect_matrix_op("mathcomp.algebra.matrix.determinant_mul"),
            Some(MathCompMatrixOp::Determinant)
        );
    }

    #[test]
    fn test_detect_matrix_op_none_for_unrelated() {
        assert_eq!(detect_matrix_op("mathcomp.ssreflect.ssrnat.addn0"), None);
    }

    #[test]
    fn test_classify_gamma_crown_target_c010_assoc() {
        let lemma = MathCompMatrixLemma {
            name: "mathcomp.algebra.matrix.mulmxA".to_owned(),
            op: MathCompMatrixOp::MatMul,
            statement_sexp: None,
            proof_sexp: None,
            target_axiom: None,
            module_path: "mathcomp.algebra.matrix".to_owned(),
            axiom_profile: AxiomProfile::CLASSICAL,
        };
        assert_eq!(
            classify_gamma_crown_target(&lemma),
            GammaCrownTarget::C010MatMulAssoc
        );
    }

    #[test]
    fn test_classify_gamma_crown_target_c010_distributivity() {
        let lemma = MathCompMatrixLemma {
            name: "mathcomp.algebra.matrix.mulmxDl".to_owned(),
            op: MathCompMatrixOp::MatMul,
            statement_sexp: None,
            proof_sexp: None,
            target_axiom: None,
            module_path: "mathcomp.algebra.matrix".to_owned(),
            axiom_profile: AxiomProfile::CLASSICAL,
        };
        assert_eq!(
            classify_gamma_crown_target(&lemma),
            GammaCrownTarget::C010MatMulAssoc
        );
    }

    #[test]
    fn test_classify_gamma_crown_target_c004_rank() {
        let lemma = MathCompMatrixLemma {
            name: "mathcomp.algebra.mxalgebra.mxrank_mul_le".to_owned(),
            op: MathCompMatrixOp::MatRank,
            statement_sexp: None,
            proof_sexp: None,
            target_axiom: None,
            module_path: "mathcomp.algebra.mxalgebra".to_owned(),
            axiom_profile: AxiomProfile::CLASSICAL,
        };
        assert_eq!(
            classify_gamma_crown_target(&lemma),
            GammaCrownTarget::C004MatrixRank
        );
    }

    #[test]
    fn test_classify_gamma_crown_target_c006_block() {
        let lemma = MathCompMatrixLemma {
            name: "mathcomp.algebra.matrix.block_mx_row".to_owned(),
            op: MathCompMatrixOp::BlockDiag,
            statement_sexp: None,
            proof_sexp: None,
            target_axiom: None,
            module_path: "mathcomp.algebra.matrix".to_owned(),
            axiom_profile: AxiomProfile::CLASSICAL,
        };
        assert_eq!(
            classify_gamma_crown_target(&lemma),
            GammaCrownTarget::C006BlockDecomposition
        );
    }

    #[test]
    fn test_classify_gamma_crown_target_none_for_add() {
        let lemma = MathCompMatrixLemma {
            name: "mathcomp.algebra.matrix.addmx_comm".to_owned(),
            op: MathCompMatrixOp::MatAdd,
            statement_sexp: None,
            proof_sexp: None,
            target_axiom: None,
            module_path: "mathcomp.algebra.matrix".to_owned(),
            axiom_profile: AxiomProfile::CLASSICAL,
        };
        assert_eq!(classify_gamma_crown_target(&lemma), GammaCrownTarget::None);
    }

    #[test]
    fn test_annotate_target_sets_field() {
        let mut lemma = MathCompMatrixLemma {
            name: "mathcomp.algebra.matrix.mulmxA".to_owned(),
            op: MathCompMatrixOp::MatMul,
            statement_sexp: None,
            proof_sexp: None,
            target_axiom: None,
            module_path: "mathcomp.algebra.matrix".to_owned(),
            axiom_profile: AxiomProfile::CLASSICAL,
        };
        annotate_target(&mut lemma);
        assert_eq!(lemma.target_axiom, Some("C010".to_owned()));
    }

    #[test]
    fn test_run_matrix_import_counts() {
        let decls = vec![
            make_decl(
                "mathcomp.algebra.matrix.mulmxA",
                "mathcomp.algebra.matrix",
                CicDeclKind::Lemma,
            ),
            make_decl(
                "mathcomp.algebra.mxalgebra.mxrank_mul_le",
                "mathcomp.algebra.mxalgebra",
                CicDeclKind::Theorem,
            ),
            make_decl(
                "mathcomp.algebra.matrix.block_mx_row",
                "mathcomp.algebra.matrix",
                CicDeclKind::Lemma,
            ),
            make_decl(
                "mathcomp.algebra.matrix.addmx_comm",
                "mathcomp.algebra.matrix",
                CicDeclKind::Theorem,
            ),
            // Non-matrix declaration
            make_decl(
                "Coq.Init.Logic.eq_refl",
                "Coq.Init.Logic",
                CicDeclKind::Theorem,
            ),
        ];

        let config = mathcomp_matrix_config(PathBuf::from("/tmp/mathcomp"));
        let result = run_matrix_import(&config, &decls);

        assert_eq!(result.declarations_scanned, 5);
        assert_eq!(result.matrix_lemmas_extracted, 4);
        assert_eq!(result.c010_matches, 1, "mulmxA -> C010");
        assert_eq!(result.c004_matches, 1, "mxrank_mul_le -> C004");
        assert_eq!(result.c006_matches, 1, "block_mx_row -> C006");
        assert_eq!(result.target_classified, 3, "3 of 4 have targets");
        assert_eq!(result.op_counts.mat_mul, 1);
        assert_eq!(result.op_counts.mat_rank, 1);
        assert_eq!(result.op_counts.block_diag, 1);
        assert_eq!(result.op_counts.mat_add, 1);
    }

    #[test]
    fn test_run_matrix_import_empty() {
        let config = mathcomp_matrix_config(PathBuf::from("/tmp/empty"));
        let result = run_matrix_import(&config, &[]);
        assert_eq!(result.declarations_scanned, 0);
        assert_eq!(result.matrix_lemmas_extracted, 0);
        assert_eq!(result.target_classified, 0);
    }

    #[test]
    fn test_mathcomp_matrix_config_properties() {
        let config = mathcomp_matrix_config(PathBuf::from("/tmp/mc"));
        assert_eq!(config.name, "mathcomp-matrix");
        assert!(config.default_axiom_profile.has(AxiomProfile::CLASSICAL));
        assert_eq!(config.expected_theorems, 5_000);

        // Should include matrix modules in Algebra phase
        assert!(config.is_included("mathcomp.algebra.matrix", ImportPhase::Algebra));
        assert!(config.is_included("mathcomp.algebra.mxalgebra", ImportPhase::Algebra));

        // Should include ssreflect in Core phase
        assert!(config.is_included("mathcomp.ssreflect.ssrbool", ImportPhase::Core));

        // Should exclude test modules
        assert!(!config.is_included("mathcomp.test.foo", ImportPhase::Full));
    }

    #[test]
    fn test_result_summary_format() {
        let result = MathCompMatrixImportResult {
            declarations_scanned: 100,
            matrix_lemmas_extracted: 42,
            target_classified: 15,
            c004_matches: 3,
            c006_matches: 5,
            c010_matches: 7,
            ..Default::default()
        };
        let s = result.summary();
        assert!(s.contains("scanned=100"));
        assert!(s.contains("matrix_extracted=42"));
        assert!(s.contains("C004=3"));
        assert!(s.contains("C006=5"));
        assert!(s.contains("C010=7"));
    }

    #[test]
    fn test_is_matrix_module_name_based() {
        // Declaration where module_path doesn't match but name does.
        let decl = make_decl("mathcomp.algebra.matrix.mulmx0", "", CicDeclKind::Lemma);
        assert!(is_matrix_module(&decl));
    }

    #[test]
    fn test_mxalgebra_module_lemmas_extracted() {
        let decls = vec![
            make_decl(
                "mathcomp.algebra.mxalgebra.rank_leq_row",
                "mathcomp.algebra.mxalgebra",
                CicDeclKind::Lemma,
            ),
            make_decl(
                "mathcomp.algebra.mxalgebra.row_free_inj",
                "mathcomp.algebra.mxalgebra",
                CicDeclKind::Lemma,
            ),
        ];

        let lemmas = extract_matrix_lemmas(&decls);
        assert_eq!(lemmas.len(), 2);
        // rank_leq_row contains "rank" -> MatRank
        assert_eq!(lemmas[0].op, MathCompMatrixOp::MatRank);
    }

    #[test]
    fn test_classify_kernel_and_cokernel_as_c004() {
        let lemma = MathCompMatrixLemma {
            name: "mathcomp.algebra.mxalgebra.kermx_eq0".to_owned(),
            op: MathCompMatrixOp::MatRank,
            statement_sexp: None,
            proof_sexp: None,
            target_axiom: None,
            module_path: "mathcomp.algebra.mxalgebra".to_owned(),
            axiom_profile: AxiomProfile::CLASSICAL,
        };
        assert_eq!(
            classify_gamma_crown_target(&lemma),
            GammaCrownTarget::C004MatrixRank
        );
    }

    #[test]
    fn test_c010_identity_lemmas() {
        // mul1mx and mulmx1 should target C010
        for name in &["mul1mx", "mulmx1", "mul0mx", "mulmx0"] {
            let lemma = MathCompMatrixLemma {
                name: format!("mathcomp.algebra.matrix.{name}"),
                op: MathCompMatrixOp::MatMul,
                statement_sexp: None,
                proof_sexp: None,
                target_axiom: None,
                module_path: "mathcomp.algebra.matrix".to_owned(),
                axiom_profile: AxiomProfile::CLASSICAL,
            };
            assert_eq!(
                classify_gamma_crown_target(&lemma),
                GammaCrownTarget::C010MatMulAssoc,
                "expected {name} to target C010"
            );
        }
    }

    #[test]
    fn test_submx_block_decomposition_targets_c006() {
        let lemma = MathCompMatrixLemma {
            name: "mathcomp.algebra.matrix.submx_block".to_owned(),
            op: MathCompMatrixOp::BlockDecomposition,
            statement_sexp: None,
            proof_sexp: None,
            target_axiom: None,
            module_path: "mathcomp.algebra.matrix".to_owned(),
            axiom_profile: AxiomProfile::CLASSICAL,
        };
        assert_eq!(
            classify_gamma_crown_target(&lemma),
            GammaCrownTarget::C006BlockDecomposition
        );
    }

    #[test]
    fn test_canonical_structure_included() {
        let decls = vec![make_decl(
            "mathcomp.algebra.matrix.scalar_mx_is_linear",
            "mathcomp.algebra.matrix",
            CicDeclKind::CanonicalStructure,
        )];

        let lemmas = extract_matrix_lemmas(&decls);
        assert_eq!(lemmas.len(), 1);
        assert_eq!(lemmas[0].op, MathCompMatrixOp::ScalarMul);
    }

    #[test]
    fn test_det_cofactor_targets_none() {
        // Determinant operations don't directly map to C004/C006/C010.
        let lemma = MathCompMatrixLemma {
            name: "mathcomp.algebra.matrix.cofactor_tr".to_owned(),
            op: MathCompMatrixOp::Determinant,
            statement_sexp: None,
            proof_sexp: None,
            target_axiom: None,
            module_path: "mathcomp.algebra.matrix".to_owned(),
            axiom_profile: AxiomProfile::CLASSICAL,
        };
        assert_eq!(classify_gamma_crown_target(&lemma), GammaCrownTarget::None);
    }
}
