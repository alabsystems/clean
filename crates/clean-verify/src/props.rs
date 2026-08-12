// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel Properties
//!
//! This module defines the properties we want to prove about the kernel:
//!
//! 1. **Type Preservation**: If e : T and e → e', then e' : T
//! 2. **Progress**: If e : T, then e is a value or e → e'
//! 3. **Confluence**: If e → e1 and e → e2, then ∃e3. e1 → e3 and e2 → e3
//! 4. **Decidability**: Type checking terminates on all inputs
//!
//! Each property is represented as a clean type. A proof of the property
//! is a term of that type.

// 2026-07-31: the `pub(crate)` items in this module are exercised only by its
// own `#[cfg(test)]` tests, so only the non-test `lib` build sees them as dead.
// Scoped to `not(test)` on purpose: the `lib test` build still enforces
// `dead_code` in full, so an item with no caller anywhere still fails the gate.
#![cfg_attr(not(test), allow(dead_code))]

use clean_elab::ElabCtx;
use clean_kernel::{Environment, Expr, TypeChecker};
use clean_parser::parse_expr;

/// A kernel property to be proven
#[derive(Debug, Clone)]
pub struct Property {
    /// Unique name
    pub name: String,
    /// The property as a clean type (what we want to prove)
    pub statement: String,
    /// Human-readable description
    pub description: String,
    /// Is this property proven?
    pub is_proven: bool,
    /// Category of property
    pub category: PropertyCategory,
}

/// Categories of kernel properties
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum PropertyCategory {
    /// Type soundness properties
    Soundness,
    /// Termination properties
    Termination,
    /// Confluence and determinism
    Confluence,
    /// Decidability
    Decidability,
}

/// Result of checking a property
#[derive(Debug)]
pub struct PropertyResult {
    /// Property name
    pub name: String,
    /// Was the property verified?
    pub verified: bool,
    /// Error message if not verified
    pub error: Option<String>,
    /// Proof term (if verified)
    pub proof: Option<Expr>,
}

impl Property {
    /// Create a new unproven property
    #[must_use]
    pub fn new(name: &str, statement: &str, description: &str, category: PropertyCategory) -> Self {
        Property {
            name: name.to_string(),
            statement: statement.to_string(),
            description: description.to_string(),
            is_proven: false,
            category,
        }
    }

    /// Mark as proven
    pub fn mark_proven(&mut self) {
        self.is_proven = true;
    }

    /// Verify this property using a proof term
    #[must_use]
    pub fn verify(&self, env: &Environment, proof_src: &str) -> PropertyResult {
        // Parse the property statement
        let stmt = match parse_expr(&self.statement) {
            Ok(s) => s,
            Err(e) => {
                return PropertyResult {
                    name: self.name.clone(),
                    verified: false,
                    error: Some(format!("Failed to parse property: {e}")),
                    proof: None,
                }
            }
        };

        // Parse the proof term
        let proof_surface = match parse_expr(proof_src) {
            Ok(p) => p,
            Err(e) => {
                return PropertyResult {
                    name: self.name.clone(),
                    verified: false,
                    error: Some(format!("Failed to parse proof: {e}")),
                    proof: None,
                }
            }
        };

        // Elaborate both
        let mut ctx = ElabCtx::new(env);

        let stmt_expr = match ctx.elaborate(&stmt) {
            Ok(e) => e,
            Err(e) => {
                return PropertyResult {
                    name: self.name.clone(),
                    verified: false,
                    error: Some(format!("Failed to elaborate property: {e}")),
                    proof: None,
                }
            }
        };

        let mut ctx = ElabCtx::new(env);
        let proof_expr = match ctx.elaborate(&proof_surface) {
            Ok(e) => e,
            Err(e) => {
                return PropertyResult {
                    name: self.name.clone(),
                    verified: false,
                    error: Some(format!("Failed to elaborate proof: {e}")),
                    proof: None,
                }
            }
        };

        // Type check: does the proof actually have the statement as its type?
        //
        // Elaboration alone does NOT establish this — it only confirms that the
        // proof term is itself a well-formed expression. To honestly report
        // `verified: true` we must run the kernel: infer the proof term's type
        // and confirm it is definitionally equal to the elaborated statement.
        let tc = TypeChecker::new(env);

        let proof_ty = match tc.infer_type(&proof_expr) {
            Ok(t) => t,
            Err(e) => {
                return PropertyResult {
                    name: self.name.clone(),
                    verified: false,
                    error: Some(format!("Failed to infer proof type: {e}")),
                    proof: None,
                }
            }
        };

        // The proof is valid only if its inferred type is definitionally equal
        // to the statement it is supposed to prove.
        if tc.is_def_eq(&proof_ty, &stmt_expr) {
            PropertyResult {
                name: self.name.clone(),
                verified: true,
                error: None,
                proof: Some(proof_expr),
            }
        } else {
            PropertyResult {
                name: self.name.clone(),
                verified: false,
                error: Some(format!(
                    "Proof does not prove the statement: inferred type {proof_ty:?} is not \
                     definitionally equal to the statement {stmt_expr:?}"
                )),
                proof: None,
            }
        }
    }
}

/// Library of kernel properties
pub(crate) struct PropertyLibrary {
    properties: Vec<Property>,
}

impl PropertyLibrary {
    /// Create library with standard properties
    #[must_use]
    pub(crate) fn new() -> Self {
        let mut lib = PropertyLibrary {
            properties: Vec::new(),
        };

        lib.add_soundness_properties();
        lib.add_termination_properties();
        lib.add_confluence_properties();

        lib
    }

    /// Get all properties
    #[must_use]
    pub(crate) fn all(&self) -> &[Property] {
        &self.properties
    }

    /// Get properties by category
    #[must_use]
    pub(crate) fn by_category(&self, cat: PropertyCategory) -> Vec<&Property> {
        self.properties
            .iter()
            .filter(|p| p.category == cat)
            .collect()
    }

    fn add_soundness_properties(&mut self) {
        // Type Preservation (Subject Reduction)
        self.properties.push(Property::new(
            "type_preservation",
            "(e : KExpr) -> (T : KExpr) -> (e' : KExpr) -> has_type e T -> is_def_eq e e' -> has_type e' T",
            "If e has type T and e reduces to e', then e' also has type T",
            PropertyCategory::Soundness,
        ));

        // Progress
        self.properties.push(Property::new(
            "progress",
            "(e : KExpr) -> (T : KExpr) -> has_type e T -> is_value e",
            "Every well-typed closed term is either a value or can step",
            PropertyCategory::Soundness,
        ));

        // Type uniqueness (up to def eq)
        self.properties.push(Property::new(
            "type_uniqueness",
            "(e : KExpr) -> (T1 : KExpr) -> (T2 : KExpr) -> has_type e T1 -> has_type e T2 -> DefEq T1 T2",
            "Types are unique up to definitional equality",
            PropertyCategory::Soundness,
        ));

        // Sort typing soundness
        self.properties.push(Property::new(
            "sort_soundness",
            "(n : Level) -> has_type (KExpr.sort n) (KExpr.sort (Level.succ n))",
            "Sort n has type Sort (n+1)",
            PropertyCategory::Soundness,
        ));

        // Pi soundness
        self.properties.push(Property::new(
            "pi_soundness",
            "(A : KExpr) -> (B : KExpr) -> (n : Level) -> has_type A (KExpr.sort n) -> has_type B (KExpr.sort n) -> has_type (KExpr.pi A B) (KExpr.sort n)",
            "Pi types are well-formed if domain and codomain are",
            PropertyCategory::Soundness,
        ));

        // Lambda soundness
        self.properties.push(Property::new(
            "lambda_soundness",
            "(A : KExpr) -> (b : KExpr) -> (B : KExpr) -> has_type A (KExpr.sort Level.zero) -> has_type b B -> has_type (KExpr.lam A b) (KExpr.pi A B)",
            "Lambda abstractions have Pi types",
            PropertyCategory::Soundness,
        ));

        // Application soundness
        self.properties.push(Property::new(
            "app_soundness",
            "(f : KExpr) -> (a : KExpr) -> (A : KExpr) -> (B : KExpr) -> has_type f (KExpr.pi A B) -> has_type a A -> has_type (KExpr.app f a) B",
            "Function application preserves typing",
            PropertyCategory::Soundness,
        ));
    }

    fn add_termination_properties(&mut self) {
        // WHNF termination
        self.properties.push(Property::new(
            "whnf_terminates",
            "(e : KExpr) -> (T : KExpr) -> has_type e T -> terminates_whnf e",
            "WHNF reduction terminates on well-typed terms",
            PropertyCategory::Termination,
        ));

        // Type inference termination
        self.properties.push(Property::new(
            "infer_type_terminates",
            "(e : KExpr) -> terminates_infer e",
            "Type inference always terminates",
            PropertyCategory::Termination,
        ));

        // Definitional equality decidability
        self.properties.push(Property::new(
            "def_eq_terminates",
            "(a : KExpr) -> (b : KExpr) -> terminates_def_eq a b",
            "Definitional equality checking terminates",
            PropertyCategory::Termination,
        ));
    }

    fn add_confluence_properties(&mut self) {
        // WHNF confluence
        self.properties.push(Property::new(
            "whnf_confluence",
            "(e : KExpr) -> (e1 : KExpr) -> (e2 : KExpr) -> whnf_to e e1 -> whnf_to e e2 -> DefEq e1 e2",
            "WHNF reduction is confluent",
            PropertyCategory::Confluence,
        ));

        // Def eq is an equivalence relation (using DefEq to match spec's def_eq_refl/symm/trans)
        self.properties.push(Property::new(
            "def_eq_refl",
            "(e : KExpr) -> DefEq e e",
            "Definitional equality is reflexive",
            PropertyCategory::Confluence,
        ));

        self.properties.push(Property::new(
            "def_eq_symm",
            "(a : KExpr) -> (b : KExpr) -> DefEq a b -> DefEq b a",
            "Definitional equality is symmetric",
            PropertyCategory::Confluence,
        ));

        self.properties.push(Property::new(
            "def_eq_trans",
            "(a : KExpr) -> (b : KExpr) -> (c : KExpr) -> DefEq a b -> DefEq b c -> DefEq a c",
            "Definitional equality is transitive",
            PropertyCategory::Confluence,
        ));

        // Beta reduction determinism
        self.properties.push(Property::new(
            "beta_deterministic",
            "(A : KExpr) -> (b : KExpr) -> (a : KExpr) -> (r1 : KExpr) -> (r2 : KExpr) -> beta_reduces (KExpr.app (KExpr.lam A b) a) r1 -> beta_reduces (KExpr.app (KExpr.lam A b) a) r2 -> DefEq r1 r2",
            "Beta reduction is deterministic",
            PropertyCategory::Confluence,
        ));
    }
}

impl Default for PropertyLibrary {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_property_library_creation() {
        let lib = PropertyLibrary::new();
        assert!(!lib.all().is_empty());
    }

    #[test]
    fn test_soundness_properties() {
        let lib = PropertyLibrary::new();
        let soundness = lib.by_category(PropertyCategory::Soundness);
        assert!(!soundness.is_empty());

        // Check type preservation exists
        assert!(soundness.iter().any(|p| p.name == "type_preservation"));
    }

    #[test]
    fn test_termination_properties() {
        let lib = PropertyLibrary::new();
        let termination = lib.by_category(PropertyCategory::Termination);
        assert!(!termination.is_empty());
    }

    #[test]
    fn test_confluence_properties() {
        let lib = PropertyLibrary::new();
        let confluence = lib.by_category(PropertyCategory::Confluence);
        assert!(!confluence.is_empty());

        // Check def_eq properties (using spec-aligned names)
        assert!(confluence.iter().any(|p| p.name == "def_eq_refl"));
        assert!(confluence.iter().any(|p| p.name == "def_eq_symm"));
        assert!(confluence.iter().any(|p| p.name == "def_eq_trans"));
    }

    /// HONESTY: a proof whose inferred type genuinely IS the statement must
    /// verify. The polymorphic identity term `fun (A : Type) (x : A) => x` has
    /// type `(A : Type) -> A -> A`, so verification must succeed truthfully.
    #[test]
    fn test_verify_accepts_genuine_proof() {
        let env = Environment::new();
        let prop = Property::new(
            "poly_id",
            "(A : Type) -> A -> A",
            "Polymorphic identity has an identity type",
            PropertyCategory::Soundness,
        );
        let result = prop.verify(&env, "fun (A : Type) (x : A) => x");
        assert!(
            result.verified,
            "a term whose inferred type is exactly the statement must verify; error: {:?}",
            result.error
        );
        assert!(result.error.is_none());
        assert!(result.proof.is_some());
    }

    /// HONESTY: this is the core regression guarding against the previous
    /// dishonest behavior, where `verify` returned `verified: true` for ANY
    /// proof that merely elaborated. Here the proof term elaborates fine but
    /// its type (`(A : Type) -> A -> A`) is NOT the claimed statement
    /// (`(A : Type) -> A -> A -> A`). Verification MUST report `false`.
    #[test]
    fn test_verify_rejects_proof_of_wrong_statement() {
        let env = Environment::new();
        let prop = Property::new(
            "wrong_statement",
            "(A : Type) -> A -> A -> A",
            "Claims a binary type but is given a unary identity proof",
            PropertyCategory::Soundness,
        );
        // `fun (A : Type) (x : A) => x` has type `(A : Type) -> A -> A`,
        // which is not definitionally equal to `(A : Type) -> A -> A -> A`.
        let result = prop.verify(&env, "fun (A : Type) (x : A) => x");
        assert!(
            !result.verified,
            "a well-formed proof of the WRONG statement must NOT verify (no false positives)"
        );
        assert!(
            result.error.is_some(),
            "a rejected proof must carry an explanatory error"
        );
    }
}
