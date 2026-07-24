// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Domain types for arXiv paper extraction.

use serde::{Deserialize, Serialize};

/// Kind of theorem-like environment.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum TheoremKind {
    Theorem,
    Lemma,
    Proposition,
    Corollary,
    Conjecture,
    Claim,
    Fact,
}

/// Kind of definition-like environment.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum DefinitionKind {
    Definition,
    Notation,
    Convention,
    Example,
    Remark,
    Assumption,
    Axiom,
}

/// A mathematical definition extracted from a paper.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ArxivDefinition {
    /// Display label (e.g., "Definition 2.1").
    pub label: String,
    /// Kind of definition.
    pub kind: DefinitionKind,
    /// Raw LaTeX content.
    pub latex: String,
    /// LaTeX \label{} value for cross-referencing.
    pub ref_label: String,
    /// Labels referenced by this definition.
    pub dependencies: Vec<String>,
}

/// A theorem with optional proof extracted from a paper.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ArxivTheorem {
    /// Display label (e.g., "Theorem 1.3").
    pub label: String,
    /// Kind of theorem.
    pub kind: TheoremKind,
    /// Raw LaTeX statement.
    pub statement_latex: String,
    /// Raw LaTeX proof (empty if not found).
    pub proof_latex: String,
    /// LaTeX \label{} value.
    pub ref_label: String,
    /// Labels referenced in statement + proof.
    pub dependencies: Vec<String>,
}

/// User-defined LaTeX macros extracted from preamble.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LatexMacro {
    /// Macro name (without backslash).
    pub name: String,
    /// Number of arguments.
    pub nargs: u8,
    /// Macro body.
    pub body: String,
}

/// Complete extraction from one arXiv paper.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ArxivPaper {
    /// arXiv paper ID (e.g., "2603.28636").
    pub paper_id: String,
    /// Paper title.
    pub title: String,
    /// Author string.
    pub authors: String,
    /// arXiv categories (e.g., ["math.CO", "math.NT"]).
    pub categories: Vec<String>,
    /// Abstract in LaTeX.
    pub abstract_latex: String,
    /// User-defined macros from preamble.
    pub macros: Vec<LatexMacro>,
    /// Custom theorem-like environments discovered.
    pub custom_environments: Vec<(String, String)>,
    /// Extracted definitions (ordered by appearance).
    pub definitions: Vec<ArxivDefinition>,
    /// Extracted theorems (ordered by appearance).
    pub theorems: Vec<ArxivTheorem>,
    /// Extraction diagnostics/warnings.
    pub warnings: Vec<String>,
}

impl ArxivPaper {
    /// Total number of named results (definitions + theorems).
    #[must_use]
    pub fn total_results(&self) -> usize {
        self.definitions.len() + self.theorems.len()
    }

    /// Number of theorems with proofs.
    #[must_use]
    pub fn proofs_found(&self) -> usize {
        self.theorems
            .iter()
            .filter(|t| !t.proof_latex.is_empty())
            .count()
    }
}
