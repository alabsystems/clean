// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! High-level arXiv importer: parses LaTeX, produces Mathverse-compatible constants.

use super::parser;
use super::types::ArxivPaper;
use crate::types::{AxiomProfile, Provenance, SourceSystem, TrustLevel};
use thiserror::Error;

// ════════════════════════════════════════════════════════════════════════════
// Configuration
// ════════════════════════════════════════════════════════════════════════════

/// Configuration for arXiv paper import.
#[derive(Clone, Debug)]
pub struct ArxivImportConfig {
    /// Include definitions (not just theorems).
    pub import_definitions: bool,
    /// Include proofs when available.
    pub import_proofs: bool,
    /// Namespace prefix for imported constants.
    pub namespace_prefix: String,
}

impl Default for ArxivImportConfig {
    fn default() -> Self {
        Self {
            import_definitions: true,
            import_proofs: true,
            namespace_prefix: "Arxiv".to_string(),
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Imported constant
// ════════════════════════════════════════════════════════════════════════════

/// Kind of arXiv imported constant.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum ArxivConstantKind {
    /// A theorem/lemma/proposition/corollary/conjecture.
    Theorem,
    /// A definition/notation/convention.
    Definition,
}

/// A single constant produced by importing an arXiv paper.
///
/// At this stage, the constant is a natural-language LaTeX statement,
/// not yet formalized. The downstream formalization pipeline converts
/// `statement_latex` into a clean type expression.
#[derive(Clone, Debug)]
pub struct ArxivImportedConstant {
    /// clean-facing name (e.g., `Arxiv.2603_28636.Theorem_1`).
    pub name: String,
    /// LaTeX statement (the content to be formalized).
    pub statement_latex: String,
    /// LaTeX proof (if available, for proof search guidance).
    pub proof_latex: String,
    /// What kind of result this is.
    pub kind: ArxivConstantKind,
    /// Axiom profile: always AXIOMATIZED | ARXIV_NL_IMPORT until formalized.
    pub axiom_profile: AxiomProfile,
    /// Trust level: TrustedOracle until formalized and verified.
    pub trust_level: TrustLevel,
    /// Full provenance record.
    pub provenance: Provenance,
    /// Labels this constant references (for dependency ordering).
    pub dependencies: Vec<String>,
    /// Original ref_label for cross-referencing.
    pub ref_label: String,
}

// ════════════════════════════════════════════════════════════════════════════
// Import result
// ════════════════════════════════════════════════════════════════════════════

/// Result of importing a complete arXiv paper.
#[derive(Clone, Debug)]
pub struct ArxivImportResult {
    /// arXiv paper ID.
    pub paper_id: String,
    /// Paper title.
    pub title: String,
    /// All constants produced from this paper.
    pub constants: Vec<ArxivImportedConstant>,
    /// Number of theorems extracted.
    pub theorem_count: usize,
    /// Number of definitions extracted.
    pub definition_count: usize,
    /// Number of theorems with associated proofs.
    pub proofs_found: usize,
    /// Custom theorem environments discovered.
    pub custom_environments: usize,
    /// Diagnostic messages collected during import.
    pub diagnostics: Vec<String>,
}

impl ArxivImportResult {
    /// Total number of constants produced.
    #[must_use]
    pub fn total_constants(&self) -> usize {
        self.constants.len()
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Errors
// ════════════════════════════════════════════════════════════════════════════

#[derive(Debug, Error)]
#[non_exhaustive]
pub enum ArxivImportError {
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
    #[error("no .tex file found in archive")]
    NoTexFile,
    #[error("failed to extract tar archive: {0}")]
    TarExtract(String),
    #[error("LaTeX parse error: {0}")]
    ParseError(String),
}

// ════════════════════════════════════════════════════════════════════════════
// Importer
// ════════════════════════════════════════════════════════════════════════════

/// arXiv paper importer.
pub struct ArxivImporter {
    config: ArxivImportConfig,
}

impl ArxivImporter {
    /// Create an importer with the given config.
    #[must_use]
    pub fn new(config: ArxivImportConfig) -> Self {
        Self { config }
    }

    /// Create an importer with default config.
    #[must_use]
    pub fn with_defaults() -> Self {
        Self::new(ArxivImportConfig::default())
    }

    /// Import from raw LaTeX source string.
    pub fn import_latex(
        &self,
        paper_id: &str,
        latex: &str,
    ) -> Result<ArxivImportResult, ArxivImportError> {
        let paper = parser::parse_latex(paper_id, latex);
        Ok(self.paper_to_result(paper))
    }

    /// Convert a parsed paper into an import result with Mathverse-compatible constants.
    fn paper_to_result(&self, paper: ArxivPaper) -> ArxivImportResult {
        let mut constants = Vec::new();
        let namespace = self.make_namespace(&paper.paper_id);

        // Import definitions first (they're the dependency base)
        let mut def_count = 0;
        if self.config.import_definitions {
            for def in &paper.definitions {
                def_count += 1;
                let name = format!("{namespace}.{}", sanitize_name(&def.label));
                constants.push(ArxivImportedConstant {
                    name,
                    statement_latex: def.latex.clone(),
                    proof_latex: String::new(),
                    kind: ArxivConstantKind::Definition,
                    axiom_profile: AxiomProfile::AXIOMATIZED.union(AxiomProfile::ARXIV_NL_IMPORT),
                    trust_level: TrustLevel::TrustedOracle,
                    provenance: Provenance {
                        source: SourceSystem::Arxiv,
                        original_name: def.label.clone(),
                        source_file: Some(format!("arxiv:{}", paper.paper_id)),
                        axiom_profile: AxiomProfile::AXIOMATIZED
                            .union(AxiomProfile::ARXIV_NL_IMPORT),
                    },
                    dependencies: def.dependencies.clone(),
                    ref_label: def.ref_label.clone(),
                });
            }
        }

        // Import theorems
        let mut thm_count = 0;
        let mut proofs_found = 0;
        for thm in &paper.theorems {
            thm_count += 1;
            if !thm.proof_latex.is_empty() {
                proofs_found += 1;
            }
            let name = format!("{namespace}.{}", sanitize_name(&thm.label));
            let proof = if self.config.import_proofs {
                thm.proof_latex.clone()
            } else {
                String::new()
            };
            constants.push(ArxivImportedConstant {
                name,
                statement_latex: thm.statement_latex.clone(),
                proof_latex: proof,
                kind: ArxivConstantKind::Theorem,
                axiom_profile: AxiomProfile::AXIOMATIZED.union(AxiomProfile::ARXIV_NL_IMPORT),
                trust_level: TrustLevel::TrustedOracle,
                provenance: Provenance {
                    source: SourceSystem::Arxiv,
                    original_name: thm.label.clone(),
                    source_file: Some(format!("arxiv:{}", paper.paper_id)),
                    axiom_profile: AxiomProfile::AXIOMATIZED.union(AxiomProfile::ARXIV_NL_IMPORT),
                },
                dependencies: thm.dependencies.clone(),
                ref_label: thm.ref_label.clone(),
            });
        }

        ArxivImportResult {
            paper_id: paper.paper_id,
            title: paper.title,
            constants,
            theorem_count: thm_count,
            definition_count: def_count,
            proofs_found,
            custom_environments: paper.custom_environments.len(),
            diagnostics: paper.warnings,
        }
    }

    /// Build namespace from paper ID: "2603.28636" → "Arxiv._2603_28636"
    fn make_namespace(&self, paper_id: &str) -> String {
        let sanitized = paper_id.replace(['.', '/', '-'], "_");
        format!("{}._{}", self.config.namespace_prefix, sanitized)
    }
}

/// Sanitize a label for use as a clean name component.
fn sanitize_name(label: &str) -> String {
    label
        .replace([' ', '.', '-', ':'], "_")
        .replace(['\'', '"'], "")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_import_simple_paper() {
        let latex = r#"
\documentclass{article}
\newtheorem{theorem}{Theorem}
\begin{document}
\title{Test}
\begin{theorem}\label{thm:main}
Every finite group of odd order is solvable.
\end{theorem}
\begin{proof}
This is the Feit-Thompson theorem.
\end{proof}
\end{document}
"#;
        let importer = ArxivImporter::with_defaults();
        let result = importer.import_latex("2603.00001", latex).unwrap();
        assert_eq!(result.theorem_count, 1);
        assert_eq!(result.proofs_found, 1);
        assert_eq!(result.constants.len(), 1);

        let c = &result.constants[0];
        assert_eq!(c.name, "Arxiv._2603_00001.Theorem_1");
        assert!(c.statement_latex.contains("solvable"));
        assert!(c.proof_latex.contains("Feit-Thompson"));
        assert_eq!(c.trust_level, TrustLevel::TrustedOracle);
        assert!(c.axiom_profile.contains(AxiomProfile::AXIOMATIZED));
        assert!(c.axiom_profile.contains(AxiomProfile::ARXIV_NL_IMPORT));
    }

    #[test]
    fn test_definitions_before_theorems() {
        let latex = r#"
\documentclass{article}
\newtheorem{definition}{Definition}
\newtheorem{theorem}{Theorem}
\begin{document}
\begin{definition}\label{def:foo}
Let $X$ be a set.
\end{definition}
\begin{theorem}\label{thm:bar}
$X$ has property P.
\end{theorem}
\end{document}
"#;
        let importer = ArxivImporter::with_defaults();
        let result = importer.import_latex("test.0002", latex).unwrap();
        assert_eq!(result.definition_count, 1);
        assert_eq!(result.theorem_count, 1);
        // Definitions come first in the constants list
        assert_eq!(result.constants[0].kind, ArxivConstantKind::Definition);
        assert_eq!(result.constants[1].kind, ArxivConstantKind::Theorem);
    }
}
