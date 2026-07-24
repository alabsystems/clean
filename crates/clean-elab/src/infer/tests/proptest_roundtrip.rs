// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bounded elaboration scenario property tests.
//!
//! Each generated case provides a surface expression that is expected to
//! elaborate successfully. The oracle re-checks the elaborated result with
//! a fresh kernel `TypeChecker` and verifies that repeated elaboration
//! produces definitionally-equal results.
//!
//! Part of #1868.

use super::*;
use clean_kernel::TypeChecker;
use proptest::prelude::*;

// ---------------------------------------------------------------------------
// Case language
// ---------------------------------------------------------------------------

/// Bounded elaboration scenario families.
///
/// Each variant carries enough data to produce a surface string and an
/// expected "must elaborate" contract.
#[derive(Debug, Clone)]
enum ElabCase {
    /// `Prop`, `Type`, `Type 1`, ..., `Type n`
    SortUniverse { level: u32 },
    /// `fun (x : Prop) => x` with a generated binder name
    IdentityLambdaProp { binder: String },
    /// `fun (x : Type) => x` with a generated binder name
    IdentityLambdaType { binder: String },
    /// `let x : Prop := True in x` (let-binding over Prop, needs True in env)
    LetBindingProp { binder: String },
    /// `fun (x : Nat) => x` — identity over Nat (needs Nat in env)
    IdentityLambdaNat { binder: String },
    /// Projection lambda: `fun (x : Prop) => fun (y : Prop) => x`
    ProjectionLambda { fst: String, snd: String },
}

impl ElabCase {
    fn to_surface_string(&self) -> String {
        match self {
            ElabCase::SortUniverse { level } => {
                if *level == 0 {
                    "Prop".to_string()
                } else {
                    format!("Type {}", level - 1)
                }
            }
            ElabCase::IdentityLambdaProp { binder } => {
                format!("fun ({binder} : Prop) => {binder}")
            }
            ElabCase::IdentityLambdaType { binder } => {
                format!("fun ({binder} : Type) => {binder}")
            }
            ElabCase::LetBindingProp { binder } => {
                format!("let {binder} : Prop := True in {binder}")
            }
            ElabCase::IdentityLambdaNat { binder } => {
                format!("fun ({binder} : Nat) => {binder}")
            }
            ElabCase::ProjectionLambda { fst, snd } => {
                format!("fun ({fst} : Prop) => fun ({snd} : Prop) => {fst}")
            }
        }
    }

    /// Whether this case needs an environment with extra declarations beyond
    /// an empty `Environment::new()`.
    fn needs_nat(&self) -> bool {
        matches!(self, ElabCase::IdentityLambdaNat { .. })
    }

    fn needs_true(&self) -> bool {
        matches!(self, ElabCase::LetBindingProp { .. })
    }
}

// ---------------------------------------------------------------------------
// Strategies
// ---------------------------------------------------------------------------

/// Strategy for safe identifiers — lowercase alpha, keyword-filtered.
fn ident_strategy() -> impl Strategy<Value = String> {
    "[a-z][a-z0-9]{0,4}".prop_filter("must not be a Lean keyword", |s| !is_lean_keyword(s))
}

/// Strategy for a second identifier guaranteed distinct from the first.
fn distinct_ident_pair() -> impl Strategy<Value = (String, String)> {
    (ident_strategy(), ident_strategy()).prop_filter("identifiers must differ", |(a, b)| a != b)
}

fn is_lean_keyword(s: &str) -> bool {
    matches!(
        s,
        "def"
            | "fun"
            | "let"
            | "in"
            | "if"
            | "do"
            | "by"
            | "end"
            | "and"
            | "or"
            | "not"
            | "match"
            | "with"
            | "where"
            | "return"
            | "have"
            | "show"
            | "calc"
            | "else"
            | "then"
            | "at"
            | "from"
            | "true"
            | "false"
            | "theorem"
            | "lemma"
            | "example"
            | "axiom"
            | "constant"
            | "variable"
            | "inductive"
            | "structure"
            | "class"
            | "instance"
            | "abbrev"
            | "opaque"
            | "private"
            | "protected"
            | "partial"
            | "unsafe"
            | "noncomputable"
            | "mutual"
            | "namespace"
            | "section"
            | "open"
            | "import"
            | "export"
            | "for"
            | "deriving"
            | "extends"
            | "using"
            | "try"
            | "catch"
            | "throw"
    )
}

fn elab_case_strategy() -> impl Strategy<Value = ElabCase> {
    prop_oneof![
        // Sort/universe surfaces
        (0u32..6).prop_map(|level| ElabCase::SortUniverse { level }),
        // Identity lambda over Prop
        ident_strategy().prop_map(|binder| ElabCase::IdentityLambdaProp { binder }),
        // Identity lambda over Type
        ident_strategy().prop_map(|binder| ElabCase::IdentityLambdaType { binder }),
        // Let binding over Prop (needs True)
        ident_strategy().prop_map(|binder| ElabCase::LetBindingProp { binder }),
        // Identity lambda over Nat
        ident_strategy().prop_map(|binder| ElabCase::IdentityLambdaNat { binder }),
        // Projection lambda (depth 2)
        distinct_ident_pair().prop_map(|(fst, snd)| ElabCase::ProjectionLambda { fst, snd }),
    ]
}

// ---------------------------------------------------------------------------
// Property tests
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    /// Property: Generated elaboration cases must produce kernel-valid terms.
    ///
    /// Oracle: parse → elaborate → kernel type-check on elaborated result.
    #[test]
    fn prop_elab_roundtrip_kernel_typecheck(case in elab_case_strategy()) {
        let input = case.to_surface_string();

        // Build environment based on case requirements
        let mut env = Environment::new();
        if case.needs_nat() {
            env.init_nat().unwrap();
        }
        if case.needs_true() {
            env.init_true_false().unwrap();
        }

        // Parse
        let surface = match parse_expr(&input) {
            Ok(s) => s,
            Err(e) => {
                prop_assert!(false, "Parse failed for '{}': {:?}", input, e);
                return Ok(());
            }
        };

        // Elaborate
        let mut ctx = ElabCtx::new(&env);
        let expr = match ctx.elaborate(&surface) {
            Ok(e) => e,
            Err(e) => {
                prop_assert!(false, "Elaboration failed for '{}': {:?}", input, e);
                return Ok(());
            }
        };

        // Kernel type-check: infer the type of the elaborated expression
        let tc = TypeChecker::new(&env);
        let inferred = tc.infer_type(&expr);
        prop_assert!(
            inferred.is_ok(),
            "Kernel type inference failed for '{}' (elaborated to {:?}): {:?}",
            input,
            expr,
            inferred.err()
        );
    }

    /// Property: Elaborating the same generated case twice yields
    /// definitionally-equal results.
    #[test]
    fn prop_elab_roundtrip_deterministic(case in elab_case_strategy()) {
        let input = case.to_surface_string();

        let mut env = Environment::new();
        if case.needs_nat() {
            env.init_nat().unwrap();
        }
        if case.needs_true() {
            env.init_true_false().unwrap();
        }

        let surface = match parse_expr(&input) {
            Ok(s) => s,
            Err(err) => {
                prop_assert!(false, "Parse failed for '{}': {:?}", input, err);
                return Ok(());
            }
        };

        let mut ctx1 = ElabCtx::new(&env);
        let mut ctx2 = ElabCtx::new(&env);

        let expr1 = match ctx1.elaborate(&surface) {
            Ok(expr) => expr,
            Err(err) => {
                prop_assert!(false, "First elaboration failed for '{}': {:?}", input, err);
                return Ok(());
            }
        };
        let expr2 = match ctx2.elaborate(&surface) {
            Ok(expr) => expr,
            Err(err) => {
                prop_assert!(false, "Second elaboration failed for '{}': {:?}", input, err);
                return Ok(());
            }
        };

        let tc = TypeChecker::new(&env);
        prop_assert!(
            tc.is_def_eq(&expr1, &expr2),
            "Determinism violated for '{}': {:?} vs {:?}",
            input,
            expr1,
            expr2
        );
    }
}
