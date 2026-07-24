// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Property-based elaboration tests

use super::*;
use proptest::prelude::*;

proptest! {
    /// Property: Elaborator never panics on arbitrary input
    #[test]
    fn prop_elab_no_panic(input in "[a-zA-Z0-9_: ()=>\\[\\].,\\n ]{0,50}") {
        let env = Environment::new();
        let mut ctx = ElabCtx::new(&env);
        // Parse may fail, that's OK
        if let Ok(surface) = parse_expr(&input) {
            // Elaboration may fail, but should never panic
            let _ = ctx.elaborate(&surface);
        }
    }

    /// Property: Type universes elaborate consistently
    #[test]
    fn prop_type_universe_level(n in 0u32..10) {
        let env = Environment::new();
        let mut ctx = ElabCtx::new(&env);

        let input = if n == 0 {
            "Type".to_string()
        } else {
            format!("Type {n}")
        };

        if let Ok(surface) = parse_expr(&input) {
            let result = ctx.elaborate(&surface);
            prop_assert!(
                result.is_ok(),
                "Type {} should elaborate: {:?}",
                n, result.err()
            );
        }
    }

    /// Property: Lambda with valid identifier elaborates
    #[test]
    fn prop_lambda_elaborates(name in "[a-z][a-z0-9]{0,5}") {
        // Skip lowercase keywords that would cause parse/elab failures
        let keywords = [
            "def", "fun", "let", "in", "if", "do", "by", "end", "and", "or", "not",
            "match", "with", "where", "return", "have", "show", "calc", "else", "then",
        ];
        prop_assume!(!keywords.contains(&name.as_str()));

        let env = Environment::new();
        let mut ctx = ElabCtx::new(&env);

        let input = format!("fun ({name} : Prop) => {name}");
        if let Ok(surface) = parse_expr(&input) {
            let result = ctx.elaborate(&surface);
            prop_assert!(
                result.is_ok(),
                "Lambda with '{}' should elaborate: {:?}",
                name, result.err()
            );
        }
    }

    /// Property: Sort universes are consistent
    /// Sort n should elaborate to a Sort expression at level n
    #[test]
    fn prop_sort_universe_consistent(n in 0u32..5) {
        let env = Environment::new();
        let mut ctx = ElabCtx::new(&env);

        // Prop = Sort 0, Type = Sort 1, Type 1 = Sort 2, etc.
        let input = if n == 0 {
            "Prop".to_string()
        } else {
            format!("Type {}", n - 1)
        };

        if let Ok(surface) = parse_expr(&input) {
            let result = ctx.elaborate(&surface);
            prop_assert!(result.is_ok(), "Sort {} should elaborate", n);
            // The result should be a Sort expression
            prop_assert!(
                matches!(result.unwrap().kind(), ExprKind::Sort(_)),
                "Expected Sort expression for level {}",
                n
            );
        }
    }

    /// Property: Elaborating the same expression twice gives def-eq results
    /// Tests inference stability
    #[test]
    fn prop_elab_deterministic(name in "[a-z][a-z0-9]{0,3}") {
        // Skip Lean keywords and reserved words
        let keywords = [
            // Control flow
            "def", "fun", "let", "in", "if", "do", "by", "end", "else", "then",
            // Logic
            "and", "or", "not", "true", "false",
            // Match/Pattern
            "match", "with", "where", "return",
            // Proof
            "have", "show", "calc", "at", "from",
            // Declarations
            "theorem", "lemma", "example", "axiom", "constant", "variable",
            "inductive", "structure", "class", "instance", "abbrev", "opaque",
            // Type universes
            "Type", "Sort", "Prop",
            // Attributes/modifiers
            "private", "protected", "partial", "unsafe", "noncomputable",
            "mutual", "namespace", "section", "open", "import", "export",
            // Other
            "for", "deriving", "extends", "using", "try", "catch", "throw",
        ];
        prop_assume!(!keywords.contains(&name.as_str()));

        let env = Environment::new();
        let input = format!("fun ({name} : Prop) => {name}");

        if let Ok(surface) = parse_expr(&input) {
            let mut ctx1 = ElabCtx::new(&env);
            let mut ctx2 = ElabCtx::new(&env);

            let result1 = ctx1.elaborate(&surface);
            let result2 = ctx2.elaborate(&surface);

            match (result1, result2) {
                (Ok(e1), Ok(e2)) => {
                    // Both should succeed and be definitionally equal
                    let tc = TypeChecker::new(&env);
                    prop_assert!(
                        tc.is_def_eq(&e1, &e2),
                        "Elaboration should be deterministic: {:?} vs {:?}",
                        e1, e2
                    );
                }
                (Err(err1), Err(err2)) => {
                    // Both failing is consistent if they fail the same way.
                    let kind1 = std::mem::discriminant(&err1);
                    let kind2 = std::mem::discriminant(&err2);
                    prop_assert_eq!(
                        kind1, kind2,
                        "Both failed but with different kinds: {:?} vs {:?}",
                        err1, err2
                    );
                }
                (Ok(e), Err(err)) | (Err(err), Ok(e)) => {
                    prop_assert!(false, "Inconsistent: one succeeded {:?}, one failed {:?}", e, err);
                }
            }
        }
    }

    /// Property: Natural literal elaboration preserves value
    #[test]
    fn prop_natlit_elab_value(n in 0u64..1000) {
        let env = Environment::new();
        let mut ctx = ElabCtx::new(&env);

        let input = n.to_string();
        if let Ok(surface) = parse_expr(&input) {
            if let Ok(ref expr) = ctx.elaborate(&surface) {
                if let ExprKind::Lit(clean_kernel::Literal::Nat(v)) = expr.kind() {
                    // Should be a Lit expression with the same value
                    prop_assert_eq!(v.to_u64(), Some(n), "Natural literal value should be preserved");
                }
            }
            // Some nat values might elaborate differently (e.g., OfNat instances)
            // That's acceptable behavior
        }
    }
}
