// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended Resolution proof type with freshness verification.
//!
//! Extended Resolution augments standard resolution by allowing
//! introduction of extension variables, each defined as a function of
//! existing variables. This module provides a unified proof type that
//! bundles the base CNF, extension definitions, and the resolution
//! proof over the extended clause set.
//!
//! ## References
//!
//! - Tseitin (1983): On the complexity of derivation in propositional calculus.
//! - Cook (1976): A short proof of the pigeon hole principle using ER.

use std::collections::HashSet;
use std::fmt;

use super::frontier::extension_variable::{extension_definition_clauses, ExtensionDef};
use super::proof_complexity::resolution::{ResolutionProof, ResolutionStep};
use super::types::Cnf;

/// Error type for extended resolution proof verification.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ExtResError {
    /// An extension variable collides with a base variable.
    VariableCollision { ext_var: u32, max_base: u32 },
    /// Two extension variables share the same index.
    DuplicateExtension(u32),
    /// The resolution proof does not derive a contradiction.
    ResolutionNotRefutation,
    /// An input clause in the resolution proof is not in the extended clause set.
    ///
    /// This is a critical soundness check: the resolution proof must use
    /// clauses from the extended formula (base CNF + extension definitions),
    /// not from an arbitrary clause set.
    InputClauseNotInFormula { step: usize, clause: Vec<i32> },
    /// An input clause references an extension variable that has no definition.
    UndefinedExtensionVariable {
        step: usize,
        var: u32,
        clause: Vec<i32>,
    },
}

impl fmt::Display for ExtResError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExtResError::VariableCollision { ext_var, max_base } => {
                write!(
                    f,
                    "extension variable {ext_var} collides with base (max={max_base})"
                )
            }
            ExtResError::DuplicateExtension(v) => {
                write!(f, "duplicate extension variable {v}")
            }
            ExtResError::ResolutionNotRefutation => {
                write!(f, "resolution proof does not derive the empty clause")
            }
            ExtResError::InputClauseNotInFormula { step, clause } => {
                write!(
                    f,
                    "step {step}: input clause {clause:?} not in extended formula"
                )
            }
            ExtResError::UndefinedExtensionVariable { step, var, clause } => {
                write!(
                    f,
                    "step {step}: input clause {clause:?} references undefined extension variable {var}"
                )
            }
        }
    }
}

impl std::error::Error for ExtResError {}

/// An Extended Resolution proof: a base CNF, extension variable
/// definitions, and a resolution proof over the extended clause set.
#[derive(Debug, Clone)]
pub struct ExtendedResolutionProof {
    /// The original CNF formula.
    pub base_cnf: Cnf,
    /// Extension variable definitions (z <-> (a AND b)).
    pub extensions: Vec<ExtensionDef>,
    /// Resolution proof over (base clauses + extension definition clauses).
    pub resolution_proof: ResolutionProof,
}

impl ExtendedResolutionProof {
    /// Verify that all extension variables are fresh: each has an index
    /// strictly greater than `base_cnf.num_vars`, and no two extensions
    /// share the same variable index.
    pub fn verify_freshness(&self) -> Result<(), ExtResError> {
        let max_base = self.base_cnf.num_vars;
        let mut seen = HashSet::new();

        for def in &self.extensions {
            if def.var <= max_base {
                return Err(ExtResError::VariableCollision {
                    ext_var: def.var,
                    max_base,
                });
            }
            if !seen.insert(def.var) {
                return Err(ExtResError::DuplicateExtension(def.var));
            }
        }
        Ok(())
    }

    /// Full verification: freshness check + resolution proof validity +
    /// input clause binding.
    ///
    /// The resolution proof must derive the empty clause from the
    /// combined clause set (base clauses + extension definition clauses).
    /// Every input clause in the resolution proof must be a member of
    /// this combined set — a proof that uses clauses from an unrelated
    /// formula is not a valid extended resolution refutation.
    pub fn verify(&self) -> Result<(), ExtResError> {
        self.verify_freshness()?;

        if !self.resolution_proof.verify() {
            return Err(ExtResError::ResolutionNotRefutation);
        }

        // SOUNDNESS FIX (Finding 8): Verify that every Input step in the
        // resolution proof corresponds to a clause in the extended clause
        // set. Without this check, an adversary could construct a proof
        // that resolves clauses from a DIFFERENT unsatisfiable formula,
        // falsely certifying a satisfiable base_cnf as unsatisfiable.
        let extended = self.extended_clauses();
        // Build a set of sorted clauses for efficient lookup.
        let extended_set: HashSet<Vec<i32>> = extended
            .iter()
            .map(|c| {
                let mut sorted = c.clone();
                sorted.sort_by_key(|l| (l.unsigned_abs(), *l < 0));
                sorted
            })
            .collect();

        for (step_idx, step) in self.resolution_proof.steps().iter().enumerate() {
            if let ResolutionStep::Input(clause) = step {
                let mut sorted_clause = clause.clone();
                sorted_clause.sort_by_key(|l| (l.unsigned_abs(), *l < 0));
                if !extended_set.contains(&sorted_clause) {
                    return Err(ExtResError::InputClauseNotInFormula {
                        step: step_idx,
                        clause: clause.clone(),
                    });
                }
            }
        }

        let defined_extensions: HashSet<u32> = self.extensions.iter().map(|def| def.var).collect();
        for (step_idx, step) in self.resolution_proof.steps().iter().enumerate() {
            if let ResolutionStep::Input(clause) = step {
                for &lit in clause {
                    let var = lit.unsigned_abs();
                    if var > self.base_cnf.num_vars && !defined_extensions.contains(&var) {
                        return Err(ExtResError::UndefinedExtensionVariable {
                            step: step_idx,
                            var,
                            clause: clause.clone(),
                        });
                    }
                }
            }
        }

        Ok(())
    }

    /// Return extension variables that are defined but never referenced by
    /// any input clause in the proof.
    #[must_use]
    pub fn unused_extensions(&self) -> Vec<u32> {
        let referenced_extensions: HashSet<u32> = self
            .resolution_proof
            .steps()
            .iter()
            .filter_map(|step| match step {
                ResolutionStep::Input(clause) => Some(clause),
                ResolutionStep::Resolve { .. } => None,
            })
            .flat_map(|clause| clause.iter().map(|lit| lit.unsigned_abs()))
            .filter(|&var| var > self.base_cnf.num_vars)
            .collect();

        self.extensions
            .iter()
            .map(|def| def.var)
            .filter(|var| !referenced_extensions.contains(var))
            .collect()
    }

    /// Build the extended clause set: base clauses + extension definition
    /// clauses, returned as DIMACS-format vectors for interop.
    #[must_use]
    pub fn extended_clauses(&self) -> Vec<Vec<i32>> {
        let mut result = self.base_cnf.to_dimacs_clauses();
        for def in &self.extensions {
            result.extend(extension_definition_clauses(def));
        }
        result
    }

    /// Total number of clauses in the extended formula.
    #[must_use]
    pub fn total_clauses(&self) -> usize {
        self.base_cnf.num_clauses() + self.extensions.len() * 3
    }

    /// Total number of variables (base + extension).
    #[must_use]
    pub fn total_vars(&self) -> u32 {
        let ext_max = self
            .extensions
            .iter()
            .map(|d| d.var)
            .max()
            .unwrap_or(self.base_cnf.num_vars);
        ext_max.max(self.base_cnf.num_vars)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat_verify::types::{Lit, SatClause};

    fn make_simple_cnf() -> Cnf {
        Cnf {
            num_vars: 2,
            clauses: vec![
                SatClause(vec![Lit(1), Lit(2)]),
                SatClause(vec![Lit(-1), Lit(2)]),
                SatClause(vec![Lit(1), Lit(-2)]),
                SatClause(vec![Lit(-1), Lit(-2)]),
            ],
        }
    }

    #[test]
    fn test_verify_freshness_ok() {
        let cnf = make_simple_cnf();
        let ext = ExtendedResolutionProof {
            base_cnf: cnf,
            extensions: vec![
                ExtensionDef {
                    var: 3,
                    literal_a: 1,
                    literal_b: 2,
                },
                ExtensionDef {
                    var: 4,
                    literal_a: -1,
                    literal_b: 2,
                },
            ],
            resolution_proof: ResolutionProof::new(),
        };
        assert!(ext.verify_freshness().is_ok());
    }

    #[test]
    fn test_verify_freshness_collision() {
        let cnf = make_simple_cnf();
        let ext = ExtendedResolutionProof {
            base_cnf: cnf,
            extensions: vec![ExtensionDef {
                var: 2, // collides with base
                literal_a: 1,
                literal_b: -1,
            }],
            resolution_proof: ResolutionProof::new(),
        };
        let err = ext.verify_freshness().unwrap_err();
        assert!(matches!(err, ExtResError::VariableCollision { .. }));
    }

    #[test]
    fn test_verify_freshness_duplicate() {
        let cnf = make_simple_cnf();
        let ext = ExtendedResolutionProof {
            base_cnf: cnf,
            extensions: vec![
                ExtensionDef {
                    var: 3,
                    literal_a: 1,
                    literal_b: 2,
                },
                ExtensionDef {
                    var: 3, // duplicate
                    literal_a: -1,
                    literal_b: 2,
                },
            ],
            resolution_proof: ResolutionProof::new(),
        };
        let err = ext.verify_freshness().unwrap_err();
        assert!(matches!(err, ExtResError::DuplicateExtension(3)));
    }

    #[test]
    fn test_verify_full_valid() {
        // Build a trivial UNSAT formula and prove it.
        let cnf = Cnf {
            num_vars: 1,
            clauses: vec![SatClause(vec![Lit(1)]), SatClause(vec![Lit(-1)])],
        };
        let mut proof = ResolutionProof::new();
        proof.add_input(vec![1]);
        proof.add_input(vec![-1]);
        proof.add_resolve(0, 1, 1).expect("resolve");

        let ext = ExtendedResolutionProof {
            base_cnf: cnf,
            extensions: vec![],
            resolution_proof: proof,
        };
        assert!(ext.verify().is_ok());
    }

    #[test]
    fn test_verify_full_not_refutation() {
        let cnf = Cnf {
            num_vars: 1,
            clauses: vec![SatClause(vec![Lit(1)])],
        };
        let mut proof = ResolutionProof::new();
        proof.add_input(vec![1]);

        let ext = ExtendedResolutionProof {
            base_cnf: cnf,
            extensions: vec![],
            resolution_proof: proof,
        };
        let err = ext.verify().unwrap_err();
        assert_eq!(err, ExtResError::ResolutionNotRefutation);
    }

    #[test]
    fn test_extended_clauses() {
        let cnf = Cnf {
            num_vars: 2,
            clauses: vec![SatClause(vec![Lit(1), Lit(-2)])],
        };
        let ext = ExtendedResolutionProof {
            base_cnf: cnf,
            extensions: vec![ExtensionDef {
                var: 3,
                literal_a: 1,
                literal_b: 2,
            }],
            resolution_proof: ResolutionProof::new(),
        };
        let clauses = ext.extended_clauses();
        // 1 base + 3 extension definition = 4
        assert_eq!(clauses.len(), 4);
        assert_eq!(ext.total_clauses(), 4);
        assert_eq!(ext.total_vars(), 3);
    }

    #[test]
    fn test_extended_clauses_content() {
        let cnf = Cnf {
            num_vars: 2,
            clauses: vec![SatClause(vec![Lit(1)])],
        };
        let ext = ExtendedResolutionProof {
            base_cnf: cnf,
            extensions: vec![ExtensionDef {
                var: 3,
                literal_a: 1,
                literal_b: 2,
            }],
            resolution_proof: ResolutionProof::new(),
        };
        let clauses = ext.extended_clauses();
        // Extension z=3 <-> (1 AND 2):
        //   (3, -1, -2) backward
        //   (-3, 1) forward a
        //   (-3, 2) forward b
        assert_eq!(clauses[1], vec![3, -1, -2]);
        assert_eq!(clauses[2], vec![-3, 1]);
        assert_eq!(clauses[3], vec![-3, 2]);
    }

    // ---- Adversarial soundness tests (audit findings) ----

    #[test]
    fn test_soundness_unbound_resolution_proof_rejected() {
        // CRITICAL BUG (Finding 8): The verifier checked freshness and
        // that the resolution proof derives the empty clause, but never
        // verified that the resolution proof's input clauses come from
        // the extended clause set.
        //
        // Attack: Create an ExtendedResolutionProof with:
        //   - base_cnf: a SATISFIABLE formula
        //   - resolution_proof: a valid refutation of a DIFFERENT formula
        // The verifier should reject this because the proof's input clauses
        // are not in the extended clause set.
        let satisfiable_cnf = Cnf {
            num_vars: 2,
            clauses: vec![
                SatClause(vec![Lit(1), Lit(2)]), // satisfiable
            ],
        };

        // Build a resolution proof of a DIFFERENT unsatisfiable formula:
        // {3} AND {-3} -> empty clause.
        let mut proof = ResolutionProof::new();
        proof.add_input(vec![3]); // NOT in base_cnf
        proof.add_input(vec![-3]); // NOT in base_cnf
        proof.add_resolve(0, 1, 3).expect("resolve");

        let ext = ExtendedResolutionProof {
            base_cnf: satisfiable_cnf,
            extensions: vec![],
            resolution_proof: proof,
        };

        let result = ext.verify();
        assert!(
            result.is_err(),
            "SOUNDNESS BUG: resolution proof using clauses from a different formula was accepted"
        );

        let err = result.unwrap_err();
        assert!(
            matches!(err, ExtResError::InputClauseNotInFormula { .. }),
            "expected InputClauseNotInFormula, got: {err}"
        );
    }

    #[test]
    fn test_verify_full_valid_with_input_binding() {
        // Verify that a legitimate proof still passes after the fix.
        // Formula: {1} AND {-1} (UNSAT). Prove with resolution.
        let cnf = Cnf {
            num_vars: 1,
            clauses: vec![SatClause(vec![Lit(1)]), SatClause(vec![Lit(-1)])],
        };
        let mut proof = ResolutionProof::new();
        proof.add_input(vec![1]); // matches base_cnf clause 0
        proof.add_input(vec![-1]); // matches base_cnf clause 1
        proof.add_resolve(0, 1, 1).expect("resolve");

        let ext = ExtendedResolutionProof {
            base_cnf: cnf,
            extensions: vec![],
            resolution_proof: proof,
        };
        assert!(ext.verify().is_ok(), "legitimate proof should still pass");
    }

    #[test]
    fn test_verify_with_extension_clauses_in_proof() {
        // Verify that a proof using extension definition clauses passes.
        let cnf = Cnf {
            num_vars: 2,
            clauses: vec![SatClause(vec![Lit(1)]), SatClause(vec![Lit(-1)])],
        };
        // Extension: z=3 <-> (1 AND 2)
        // Definition clauses: (3, -1, -2), (-3, 1), (-3, 2)
        let ext_def = ExtensionDef {
            var: 3,
            literal_a: 1,
            literal_b: 2,
        };

        // Use input clauses from the base formula (not the extension clauses,
        // since we only need {1} and {-1} to derive empty).
        let mut proof = ResolutionProof::new();
        proof.add_input(vec![1]);
        proof.add_input(vec![-1]);
        proof.add_resolve(0, 1, 1).expect("resolve");

        let ext = ExtendedResolutionProof {
            base_cnf: cnf,
            extensions: vec![ext_def],
            resolution_proof: proof,
        };
        assert!(ext.verify().is_ok());
    }

    #[test]
    fn test_verify_rejects_undefined_extension_variable() {
        let cnf = Cnf {
            num_vars: 1,
            clauses: vec![SatClause(vec![Lit(1)]), SatClause(vec![Lit(-1)])],
        };
        let mut proof = ResolutionProof::new();
        proof.add_input(vec![1]);
        proof.add_input(vec![-1]);
        proof.add_input(vec![-2, 4]);
        proof.add_resolve(0, 1, 1).expect("resolve");

        let ext = ExtendedResolutionProof {
            base_cnf: cnf,
            extensions: vec![ExtensionDef {
                var: 2,
                literal_a: 4,
                literal_b: 1,
            }],
            resolution_proof: proof,
        };

        let err = ext.verify().unwrap_err();
        assert!(matches!(
            err,
            ExtResError::UndefinedExtensionVariable {
                step: 2,
                var: 4,
                ..
            }
        ));
    }

    #[test]
    fn test_unused_extensions_detected() {
        let cnf = Cnf {
            num_vars: 1,
            clauses: vec![SatClause(vec![Lit(1)]), SatClause(vec![Lit(-1)])],
        };
        let mut proof = ResolutionProof::new();
        proof.add_input(vec![1]);
        proof.add_input(vec![-1]);
        proof.add_input(vec![-2, 1]);
        proof.add_resolve(0, 1, 1).expect("resolve");

        let ext = ExtendedResolutionProof {
            base_cnf: cnf,
            extensions: vec![
                ExtensionDef {
                    var: 2,
                    literal_a: 1,
                    literal_b: -1,
                },
                ExtensionDef {
                    var: 3,
                    literal_a: 1,
                    literal_b: 2,
                },
            ],
            resolution_proof: proof,
        };

        assert!(ext.verify().is_ok());
        assert_eq!(ext.unused_extensions(), vec![3]);
    }

    #[test]
    fn test_verify_valid_with_all_extensions_used() {
        let cnf = Cnf {
            num_vars: 1,
            clauses: vec![SatClause(vec![Lit(1)]), SatClause(vec![Lit(-1)])],
        };
        let mut proof = ResolutionProof::new();
        proof.add_input(vec![1]);
        proof.add_input(vec![-1]);
        proof.add_input(vec![-2, 1]);
        proof.add_input(vec![-3, 2]);
        proof.add_resolve(0, 1, 1).expect("resolve");

        let ext = ExtendedResolutionProof {
            base_cnf: cnf,
            extensions: vec![
                ExtensionDef {
                    var: 2,
                    literal_a: 1,
                    literal_b: -1,
                },
                ExtensionDef {
                    var: 3,
                    literal_a: 2,
                    literal_b: 1,
                },
            ],
            resolution_proof: proof,
        };

        assert!(ext.verify().is_ok());
        assert!(ext.unused_extensions().is_empty());
    }
}
