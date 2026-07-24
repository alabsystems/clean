// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Types for the Metamath `.mm` importer.
//!
//! Metamath is a simple formal system based on string substitution. Its database
//! contains constants, variables, axioms (`$a`), and provable assertions (`$p`),
//! plus floating (`$f`) and essential (`$e`) hypotheses. Proofs are sequences
//! of label references that build up a substitution-based derivation.
//!
//! Reference: <http://us.metamath.org/mpe/mmset.html>

use serde::{Deserialize, Serialize};

// ════════════════════════════════════════════════════════════════════════════
// Database
// ════════════════════════════════════════════════════════════════════════════

/// A parsed Metamath database (one `.mm` file).
///
/// Contains all constants, variables, and statements extracted from the file.
/// Scoping information (`${ ... $}`) is resolved during parsing: each
/// statement records its active hypotheses inline.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct MmDatabase {
    /// Declared constants (`$c` tokens).
    pub constants: Vec<String>,
    /// Declared variables (`$v` tokens).
    pub variables: Vec<String>,
    /// All statements (axioms, theorems, hypotheses) keyed by label.
    pub statements: Vec<MmStatement>,
}

impl MmDatabase {
    /// Number of axiom statements (`$a`).
    #[must_use]
    pub fn axiom_count(&self) -> usize {
        self.statements
            .iter()
            .filter(|s| s.kind == MmStatementKind::Axiom)
            .count()
    }

    /// Number of provable statements (`$p`).
    #[must_use]
    pub fn theorem_count(&self) -> usize {
        self.statements
            .iter()
            .filter(|s| s.kind == MmStatementKind::Theorem)
            .count()
    }

    /// Number of floating hypotheses (`$f`).
    #[must_use]
    pub fn float_hyp_count(&self) -> usize {
        self.statements
            .iter()
            .filter(|s| s.kind == MmStatementKind::FloatingHyp)
            .count()
    }

    /// Number of essential hypotheses (`$e`).
    #[must_use]
    pub fn essential_hyp_count(&self) -> usize {
        self.statements
            .iter()
            .filter(|s| s.kind == MmStatementKind::EssentialHyp)
            .count()
    }

    /// Total statement count.
    #[must_use]
    pub fn total_statements(&self) -> usize {
        self.statements.len()
    }

    /// Whether this database is empty (no statements).
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.statements.is_empty()
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Statement
// ════════════════════════════════════════════════════════════════════════════

/// A single Metamath statement.
///
/// Every labeled construct in Metamath (`$a`, `$p`, `$f`, `$e`) becomes one
/// `MmStatement`. The `expression` field holds the token sequence after the
/// keyword, and `proof` is present only for `$p` statements.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MmStatement {
    /// The label preceding the statement keyword.
    pub label: String,
    /// Statement kind.
    pub kind: MmStatementKind,
    /// Token sequence (the math string). First token is the typecode.
    pub expression: MmExpression,
    /// Proof (only for `$p` / Theorem statements).
    pub proof: Option<MmProof>,
    /// Labels of active hypotheses in scope when this statement was declared.
    pub hypotheses: Vec<String>,
}

/// Discriminant for Metamath statement types.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum MmStatementKind {
    /// Axiom (`$a`): axiomatic assertion.
    Axiom,
    /// Theorem (`$p`): provable assertion.
    Theorem,
    /// Floating hypothesis (`$f`): variable type declaration.
    FloatingHyp,
    /// Essential hypothesis (`$e`): logical hypothesis.
    EssentialHyp,
}

// ════════════════════════════════════════════════════════════════════════════
// Expression
// ════════════════════════════════════════════════════════════════════════════

/// A Metamath math expression: a sequence of tokens (constants and variables).
///
/// The first token is the "typecode" (e.g., `wff`, `class`, `|-`), and the
/// remaining tokens are the formula body.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct MmExpression {
    /// Token sequence. The first element is the typecode.
    pub tokens: Vec<String>,
}

impl MmExpression {
    /// The typecode (first token), if present.
    #[must_use]
    pub fn typecode(&self) -> Option<&str> {
        self.tokens.first().map(|s| s.as_str())
    }

    /// The formula body (everything after the typecode).
    #[must_use]
    pub fn body(&self) -> &[String] {
        if self.tokens.len() > 1 {
            &self.tokens[1..]
        } else {
            &[]
        }
    }

    /// Whether this expression is empty (no tokens).
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.tokens.is_empty()
    }

    /// Number of tokens in the expression.
    #[must_use]
    pub fn len(&self) -> usize {
        self.tokens.len()
    }

    /// Format expression tokens as a single space-separated string.
    #[must_use]
    pub fn to_string_repr(&self) -> String {
        self.tokens.join(" ")
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Proof
// ════════════════════════════════════════════════════════════════════════════

/// A Metamath proof: a sequence of label references.
///
/// Proofs in Metamath work by substitution: each step references a previously
/// proven assertion or hypothesis, and the verifier checks that the
/// substitution is consistent. Compressed proofs use a parenthesized label
/// list followed by encoded step indices.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct MmProof {
    /// Proof format.
    pub format: MmProofFormat,
    /// Proof step labels (in order of application).
    pub steps: Vec<String>,
}

/// Format of a Metamath proof.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum MmProofFormat {
    /// Normal proof: space-separated label references.
    Normal,
    /// Compressed proof: `( label1 label2 ... ) encoded_steps`.
    Compressed,
}

// ════════════════════════════════════════════════════════════════════════════
// Import statistics
// ════════════════════════════════════════════════════════════════════════════

/// Statistics from importing a Metamath database.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct MmImportStats {
    /// Total constants declared.
    pub constant_count: usize,
    /// Total variables declared.
    pub variable_count: usize,
    /// Axioms imported.
    pub axiom_count: usize,
    /// Theorems imported.
    pub theorem_count: usize,
    /// Floating hypotheses imported.
    pub float_hyp_count: usize,
    /// Essential hypotheses imported.
    pub essential_hyp_count: usize,
    /// Total shard entries written.
    pub entries_written: usize,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mm_database_default_is_empty() {
        let db = MmDatabase::default();
        assert!(db.is_empty());
        assert_eq!(db.axiom_count(), 0);
        assert_eq!(db.theorem_count(), 0);
        assert_eq!(db.total_statements(), 0);
    }

    #[test]
    fn test_mm_expression_typecode_and_body() {
        let expr = MmExpression {
            tokens: vec![
                "|-".to_string(),
                "(".to_string(),
                "ph".to_string(),
                "->".to_string(),
                "ph".to_string(),
                ")".to_string(),
            ],
        };
        assert_eq!(expr.typecode(), Some("|-"));
        assert_eq!(expr.body().len(), 5);
        assert_eq!(expr.len(), 6);
        assert!(!expr.is_empty());
    }

    #[test]
    fn test_mm_expression_empty() {
        let expr = MmExpression { tokens: vec![] };
        assert!(expr.is_empty());
        assert_eq!(expr.typecode(), None);
        assert_eq!(expr.body().len(), 0);
    }

    #[test]
    fn test_mm_expression_to_string_repr() {
        let expr = MmExpression {
            tokens: vec!["|-".to_string(), "ph".to_string()],
        };
        assert_eq!(expr.to_string_repr(), "|- ph");
    }

    #[test]
    fn test_mm_database_counts() {
        let db = MmDatabase {
            constants: vec!["(".to_string(), ")".to_string(), "->".to_string()],
            variables: vec!["ph".to_string(), "ps".to_string()],
            statements: vec![
                MmStatement {
                    label: "wph".to_string(),
                    kind: MmStatementKind::FloatingHyp,
                    expression: MmExpression {
                        tokens: vec!["wff".to_string(), "ph".to_string()],
                    },
                    proof: None,
                    hypotheses: vec![],
                },
                MmStatement {
                    label: "ax-1".to_string(),
                    kind: MmStatementKind::Axiom,
                    expression: MmExpression {
                        tokens: vec![
                            "|-".to_string(),
                            "(".to_string(),
                            "ph".to_string(),
                            "->".to_string(),
                            "(".to_string(),
                            "ps".to_string(),
                            "->".to_string(),
                            "ph".to_string(),
                            ")".to_string(),
                            ")".to_string(),
                        ],
                    },
                    proof: None,
                    hypotheses: vec!["wph".to_string(), "wps".to_string()],
                },
                MmStatement {
                    label: "a1i".to_string(),
                    kind: MmStatementKind::Theorem,
                    expression: MmExpression {
                        tokens: vec![
                            "|-".to_string(),
                            "(".to_string(),
                            "ps".to_string(),
                            "->".to_string(),
                            "ph".to_string(),
                            ")".to_string(),
                        ],
                    },
                    proof: Some(MmProof {
                        format: MmProofFormat::Normal,
                        steps: vec!["wph".to_string(), "ax-1".to_string(), "ax-mp".to_string()],
                    }),
                    hypotheses: vec!["wph".to_string(), "wps".to_string()],
                },
            ],
        };
        assert_eq!(db.axiom_count(), 1);
        assert_eq!(db.theorem_count(), 1);
        assert_eq!(db.float_hyp_count(), 1);
        assert_eq!(db.essential_hyp_count(), 0);
        assert_eq!(db.total_statements(), 3);
        assert!(!db.is_empty());
    }

    #[test]
    fn test_serde_roundtrip_statement_kind() {
        for kind in [
            MmStatementKind::Axiom,
            MmStatementKind::Theorem,
            MmStatementKind::FloatingHyp,
            MmStatementKind::EssentialHyp,
        ] {
            let json = serde_json::to_string(&kind).expect("serialize");
            let restored: MmStatementKind = serde_json::from_str(&json).expect("deserialize");
            assert_eq!(kind, restored);
        }
    }

    #[test]
    fn test_serde_roundtrip_proof_format() {
        for fmt in [MmProofFormat::Normal, MmProofFormat::Compressed] {
            let json = serde_json::to_string(&fmt).expect("serialize");
            let restored: MmProofFormat = serde_json::from_str(&json).expect("deserialize");
            assert_eq!(fmt, restored);
        }
    }

    #[test]
    fn test_serde_roundtrip_database() {
        let db = MmDatabase {
            constants: vec!["|-".to_string()],
            variables: vec!["ph".to_string()],
            statements: vec![MmStatement {
                label: "wph".to_string(),
                kind: MmStatementKind::FloatingHyp,
                expression: MmExpression {
                    tokens: vec!["wff".to_string(), "ph".to_string()],
                },
                proof: None,
                hypotheses: vec![],
            }],
        };
        let json = serde_json::to_string(&db).expect("serialize");
        let restored: MmDatabase = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(restored.constants.len(), 1);
        assert_eq!(restored.statements.len(), 1);
        assert_eq!(restored.statements[0].label, "wph");
    }

    #[test]
    fn test_import_stats_default() {
        let stats = MmImportStats::default();
        assert_eq!(stats.axiom_count, 0);
        assert_eq!(stats.theorem_count, 0);
        assert_eq!(stats.entries_written, 0);
    }
}
