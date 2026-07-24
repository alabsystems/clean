// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! HOL family importer (HOL Light, HOL4, HOL Zero, Isabelle/HOL).
//!
//! The HOL family shares a common simple type theory with three axioms
//! (extensionality, choice, infinity). The OpenTheory format provides a
//! standard exchange mechanism across all HOL systems.
//!
//! # Trust model
//!
//! HOL proofs are verified by LCF-style kernels in the source system. Since
//! we do not replay the full proof in clean's kernel, imported theorems carry
//! the `HOL_AXIOMS` axiom profile and `PartiallyAxiomatized` trust level.
//! The three HOL axioms (extensionality, choice, infinity) are tracked in
//! the `AxiomProfile` bitvector for downstream trust gating.
//!
//! # Supported import paths
//!
//! 1. **OpenTheory `.art` articles** — standard exchange format, works with
//!    all HOL family systems. This is the primary import path.
//! 2. Future: direct HOL Light proof objects, HOL4 theory files.

use thiserror::Error;

use crate::types::{AxiomProfile, Provenance, SourceSystem, TrustLevel};

pub mod opentheory;
pub(crate) mod ot_vm;
pub mod translate;
pub mod types;

pub use types::{HolAxiom, HolImportResult, HolTerm, HolThm, HolType};

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Errors during HOL family import.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum HolError {
    /// Failed to parse an OpenTheory article.
    #[error("OpenTheory error: {message}")]
    OpenTheoryError { message: String },

    /// Type or term translation error.
    #[error("HOL translation error: {message}")]
    TranslationError { message: String },

    /// Unsupported HOL feature encountered.
    #[error("unsupported HOL feature: {feature}")]
    UnsupportedFeature { feature: String },
}

// ---------------------------------------------------------------------------
// Importer
// ---------------------------------------------------------------------------

/// HOL family importer using OpenTheory as the exchange format.
///
/// Imports theorems from HOL Light, HOL4, HOL Zero, or Isabelle/HOL via
/// their OpenTheory article exports.
pub struct HolImporter {
    source: SourceSystem,
}

impl Default for HolImporter {
    fn default() -> Self {
        Self::new(SourceSystem::HolLight)
    }
}

impl HolImporter {
    /// Create a new HOL importer for the given source system.
    ///
    /// Use `SourceSystem::HolLight`, `SourceSystem::Hol4`, or
    /// `SourceSystem::Isabelle` to specify the origin.
    #[must_use]
    pub fn new(source: SourceSystem) -> Self {
        Self { source }
    }

    /// Import an OpenTheory article and produce an import result.
    pub fn import_article(&self, article_text: &str) -> Result<HolImportResult, HolError> {
        let article = opentheory::parse_article(article_text)?;

        let theorem_count = article.theorems.len();

        // Attempt translation of each theorem.
        let mut translated_count = 0;
        let mut diagnostics = Vec::new();

        for (i, thm) in article.theorems.iter().enumerate() {
            match translate::translate_theorem(thm) {
                Ok(_) => translated_count += 1,
                Err(e) => {
                    diagnostics.push(format!("theorem {i}: translation failed: {e}"));
                }
            }
        }

        // Compute axiom profile from declared axioms.
        let mut axiom_profile = AxiomProfile::HOL_AXIOMS;
        for ax in &article.axioms_assumed {
            match ax {
                HolAxiom::Extensionality => axiom_profile |= AxiomProfile::FUNC_EXT,
                HolAxiom::Choice => axiom_profile |= AxiomProfile::CHOICE,
                HolAxiom::Infinity => {} // No separate bit for infinity.
            }
        }

        // Any partial-or-full translation is currently labelled the same
        // (PartiallyAxiomatized); only zero-translated falls back to oracle.
        let trust_level = if translated_count > 0 {
            TrustLevel::PartiallyAxiomatized
        } else {
            TrustLevel::TrustedOracle
        };

        let source_name = match self.source {
            SourceSystem::HolLight => "HOL Light",
            SourceSystem::Hol4 => "HOL4",
            SourceSystem::Isabelle => "Isabelle/HOL",
            _ => "HOL",
        };

        if !article.constants.is_empty() {
            diagnostics.push(format!(
                "defined constants: {}",
                article.constants.join(", ")
            ));
        }
        if !article.type_ops.is_empty() {
            diagnostics.push(format!("defined type ops: {}", article.type_ops.join(", ")));
        }
        if !article.axioms_assumed.is_empty() {
            diagnostics.push(format!("axioms assumed: {:?}", article.axioms_assumed));
        }

        let provenance = Provenance {
            source: self.source,
            original_name: source_name.to_owned(),
            source_file: None,
            axiom_profile,
        };

        Ok(HolImportResult {
            source_name: source_name.to_owned(),
            theorem_count,
            translated_count,
            axioms_used: article.axioms_assumed,
            axiom_profile,
            trust_level,
            provenance,
            diagnostics,
        })
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// Minimal article: builds Const("=", bool), refl, then exports via thm.
    const TRUTH_ARTICLE: &str = "\
\"bool\"
nil
opType
0
def
\"=\"
0
ref
constTerm
refl
nil
\"T\"
0
ref
constTerm
thm
";

    #[test]
    fn test_hol_importer_default() {
        let importer = HolImporter::default();
        assert_eq!(importer.source, SourceSystem::HolLight);
    }

    #[test]
    fn test_hol_importer_hol4() {
        let importer = HolImporter::new(SourceSystem::Hol4);
        assert_eq!(importer.source, SourceSystem::Hol4);
    }

    #[test]
    fn test_hol_importer_isabelle() {
        let importer = HolImporter::new(SourceSystem::Isabelle);
        assert_eq!(importer.source, SourceSystem::Isabelle);
    }

    #[test]
    fn test_import_truth_article() {
        let importer = HolImporter::new(SourceSystem::HolLight);
        let result = importer.import_article(TRUTH_ARTICLE).unwrap();

        assert_eq!(result.source_name, "HOL Light");
        assert_eq!(result.theorem_count, 1);
        assert_eq!(result.translated_count, 1);
        assert!(result.axiom_profile.has(AxiomProfile::HOL_AXIOMS));
        assert_eq!(result.trust_level, TrustLevel::PartiallyAxiomatized);
        assert_eq!(result.provenance.source, SourceSystem::HolLight);
    }

    #[test]
    fn test_import_empty_article_errors() {
        let importer = HolImporter::default();
        let result = importer.import_article("");
        assert!(result.is_err());
    }

    #[test]
    fn test_hol_type_constructors() {
        assert!(HolType::bool().is_bool());
        assert!(!HolType::ind().is_bool());

        let fun_ty = HolType::fun(HolType::bool(), HolType::ind());
        assert!(fun_ty.is_fun());
        let (dom, cod) = fun_ty.dest_fun().unwrap();
        assert!(dom.is_bool());
        assert_eq!(*cod, HolType::ind());

        assert!(HolType::bool().dest_fun().is_none());
    }

    #[test]
    fn test_hol_term_ty() {
        let v = HolTerm::Var("x".to_owned(), HolType::bool());
        assert_eq!(v.ty(), Some(HolType::bool()));

        let c = HolTerm::Const("T".to_owned(), HolType::bool());
        assert_eq!(c.ty(), Some(HolType::bool()));

        let abs = HolTerm::Abs(
            "x".to_owned(),
            HolType::bool(),
            Box::new(HolTerm::Var("x".to_owned(), HolType::bool())),
        );
        assert_eq!(
            abs.ty(),
            Some(HolType::fun(HolType::bool(), HolType::bool()))
        );

        let f = HolTerm::Const(
            "not".to_owned(),
            HolType::fun(HolType::bool(), HolType::bool()),
        );
        let app = HolTerm::App(
            Box::new(f),
            Box::new(HolTerm::Const("T".to_owned(), HolType::bool())),
        );
        assert_eq!(app.ty(), Some(HolType::bool()));
    }

    #[test]
    fn test_hol_thm_structure() {
        let thm = HolThm {
            hyps: vec![HolTerm::Var("P".to_owned(), HolType::bool())],
            concl: HolTerm::Var("P".to_owned(), HolType::bool()),
        };
        assert_eq!(thm.hyps.len(), 1);
        assert_eq!(thm.hyps[0], thm.concl);
    }

    #[test]
    fn test_hol_axiom_variants() {
        let ext = HolAxiom::Extensionality;
        let choice = HolAxiom::Choice;
        let inf = HolAxiom::Infinity;
        // Ensure Debug and Clone work.
        let _ = format!("{ext:?} {choice:?} {inf:?}");
        assert_ne!(ext, choice);
    }

    #[test]
    fn test_axiom_profile_hol_bits() {
        let profile = AxiomProfile::HOL_AXIOMS | AxiomProfile::FUNC_EXT | AxiomProfile::CHOICE;
        assert!(profile.has(AxiomProfile::HOL_AXIOMS));
        assert!(profile.has(AxiomProfile::FUNC_EXT));
        assert!(profile.has(AxiomProfile::CHOICE));
        assert!(!profile.has(AxiomProfile::LRA_TRUSTED));
    }

    #[test]
    fn test_import_article_hol4_source() {
        let importer = HolImporter::new(SourceSystem::Hol4);
        let result = importer.import_article(TRUTH_ARTICLE).unwrap();
        assert_eq!(result.source_name, "HOL4");
        assert_eq!(result.provenance.source, SourceSystem::Hol4);
    }

    #[test]
    fn test_import_article_isabelle_source() {
        let importer = HolImporter::new(SourceSystem::Isabelle);
        let result = importer.import_article(TRUTH_ARTICLE).unwrap();
        assert_eq!(result.source_name, "Isabelle/HOL");
        assert_eq!(result.provenance.source, SourceSystem::Isabelle);
    }

    #[test]
    fn test_hol_error_display() {
        let e1 = HolError::OpenTheoryError {
            message: "test".to_owned(),
        };
        assert!(format!("{e1}").contains("OpenTheory"));

        let e2 = HolError::TranslationError {
            message: "bad type".to_owned(),
        };
        assert!(format!("{e2}").contains("translation"));

        let e3 = HolError::UnsupportedFeature {
            feature: "type classes".to_owned(),
        };
        assert!(format!("{e3}").contains("type classes"));
    }
}
