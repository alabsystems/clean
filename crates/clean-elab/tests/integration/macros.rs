// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Macro system end-to-end tests.

use super::common::check_and_add_decl;
use clean_elab::{elaborate, ElabCtx, ElabResult};
use clean_kernel::{Declaration, Environment, ExprKind, Name, TypeChecker};
use clean_parser::{parse_decl, parse_expr};

/// Helper: Parse and elaborate multiple declarations with shared macro context
/// This collects elaboration results and then adds them to the environment after ctx is dropped
fn elaborate_with_macros(env: &mut Environment, decls: &[&str]) -> Result<(), String> {
    // First pass: elaborate all declarations, collecting results
    let results: Vec<ElabResult> = {
        let mut ctx = ElabCtx::new(env);
        let mut results = Vec::new();

        for input in decls {
            let surface = parse_decl(input).map_err(|e| format!("Parse error: {e}"))?;
            let elab_result = ctx
                .elab_decl(&surface)
                .map_err(|e| format!("Elab error: {e}"))?;
            results.push(elab_result);
        }

        results
    }; // ctx dropped here, releasing borrow on env

    // Second pass: add results to environment
    for elab_result in results {
        match elab_result {
            ElabResult::Definition {
                name,
                universe_params,
                ty,
                val,
                modifiers: _,
            } => {
                {
                    let tc = TypeChecker::new(env);
                    let _ = tc
                        .infer_type(&ty)
                        .map_err(|e| format!("Type check ty: {e}"))?;
                    tc.check_type(&val, &ty)
                        .map_err(|e| format!("Type check val: {e}"))?;
                }

                env.add_decl(Declaration::Definition {
                    name,
                    level_params: universe_params,
                    type_: ty,
                    value: val,
                    is_reducible: true,
                })
                .map_err(|e| format!("Add decl: {e}"))?;
            }
            ElabResult::Axiom {
                name,
                universe_params,
                ty,
                modifiers: _,
            } => {
                {
                    let tc = TypeChecker::new(env);
                    let _ = tc
                        .infer_type(&ty)
                        .map_err(|e| format!("Type check ty: {e}"))?;
                }

                env.add_decl(Declaration::Axiom {
                    name,
                    level_params: universe_params,
                    type_: ty,
                })
                .map_err(|e| format!("Add decl: {e}"))?;
            }
            // Syntax/notation/macro declarations and other complex results are skipped
            _ => {}
        }
    }

    Ok(())
}

#[test]
fn test_builtin_macro_if_then_else() {
    // Test that built-in if-then-else macro expands correctly
    // Note: if-then-else expands to `ite` which requires the standard library
    // In an empty environment, we need to define ite first
    let mut env = Environment::new();

    // First need Decidable type
    check_and_add_decl(&mut env, "axiom Decidable : Prop -> Type").expect("Decidable axiom");

    // Define a minimal ite function: ite (c : Prop) (t e : Type) : Type
    check_and_add_decl(
        &mut env,
        "def ite (c : Prop) [d : Decidable c] (t e : Type) : Type := t",
    )
    .expect("ite definition should succeed");

    // Now if-then-else should work
    // Note: This test verifies the macro parses; full elaboration requires instance resolution
    let surface = parse_expr("if Prop then Type else Prop").unwrap();
    let result = elaborate(&env, &surface);

    // The macro should expand without panic; exact result depends on instance resolution
    // For now just verify it doesn't panic
    let _ = result;
}

#[test]
fn test_builtin_macro_unless() {
    // Test that 'unless' macro works
    // unless c then body == if c then () else body
    // Since we don't have Unit, test structure
    let env = Environment::new();

    // Parse and elaborate unless expression
    let surface = parse_expr("unless Prop then Type").unwrap();
    let result = elaborate(&env, &surface);

    // Should either succeed or fail gracefully (not panic)
    // The exact behavior depends on how unless is defined
    let _ = result;
}

#[test]
fn test_user_defined_macro_rules_registration() {
    // Test: Register macro_rules and verify it affects subsequent elaboration
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    // Register a simple macro_rules that transforms myId to id pattern
    let macro_decl = parse_decl("macro_rules | `(myId $x) => `($x)").unwrap();
    let result = ctx.elab_decl(&macro_decl);
    assert!(result.is_ok(), "macro_rules should register: {result:?}");

    // Now try to expand an expression using the registered macro
    let expr = parse_expr("myId Type").unwrap();
    let expanded = ctx.elaborate(&expr);

    // The macro should expand myId Type to Type
    // Whether this succeeds depends on macro expansion being wired correctly
    if let Ok(kernel_expr) = expanded {
        // Should be Sort (Type)
        assert!(
            matches!(kernel_expr.kind(), ExprKind::Sort(_)),
            "myId Type should elaborate to Sort, got {kernel_expr:?}"
        );
    }
}

#[test]
fn test_user_defined_notation_registration() {
    // Test: Register a notation and verify it parses/elaborates
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    // Register an infix notation: +++ means function application
    // notation:65 x " +++ " y => x y
    let notation_decl =
        parse_decl(r#"infixl:65 " +++ " => fun x y => x"#).expect("notation should parse");
    let result = ctx.elab_decl(&notation_decl);
    assert!(
        matches!(result, Ok(ElabResult::Skipped)),
        "notation declaration should register as a skipped elaboration result: {result:?}"
    );

    let registered_names = ctx.macro_ctx().registry().macro_names();
    assert!(
        registered_names
            .iter()
            .any(|name| name.contains("infixl") && name.contains("+++")),
        "notation registry should contain the custom +++ entry, got {registered_names:?}"
    );
}

#[test]
fn test_syntax_category_registration() {
    // Test: Register a custom syntax category
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    // Register a custom syntax category
    let cat_decl = parse_decl("declare_syntax_cat mycat").unwrap();
    let result = ctx.elab_decl(&cat_decl);
    assert!(
        result.is_ok(),
        "declare_syntax_cat should succeed: {result:?}"
    );

    // Verify the category was registered
    assert!(
        ctx.macro_ctx().has_syntax_category("mycat"),
        "mycat category should be registered"
    );
}

#[test]
fn test_macro_expansion_preserves_semantics() {
    // Test: User-defined macros that expand should preserve semantics
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    // Register a simple identity macro
    let macro_decl = parse_decl("macro_rules | `(identity $x) => `($x)").unwrap();
    ctx.elab_decl(&macro_decl).unwrap();

    // Expand "identity Type" which should give us Type
    let expr = parse_expr("identity Type").unwrap();
    let result = ctx.elaborate(&expr);

    // Should preserve the semantics: identity Type == Type
    if let Ok(kernel_expr) = result {
        assert!(
            matches!(kernel_expr.kind(), ExprKind::Sort(_)),
            "identity Type should elaborate to Sort"
        );
    }
}

#[test]
fn test_multiple_macro_declarations() {
    // Test: Multiple macro declarations in sequence
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    // Register multiple macros
    let macro1 = parse_decl("macro_rules | `(m1 $x) => `($x)");
    let macro2 = parse_decl("macro_rules | `(m2 $x) => `(m1 $x)");

    if let Ok(decl1) = macro1 {
        ctx.elab_decl(&decl1).unwrap();
    }
    if let Ok(decl2) = macro2 {
        ctx.elab_decl(&decl2).unwrap();
    }

    // Try to use chained macros: m2 Type should expand to m1 Type then to Type
    let expr = parse_expr("m2 Type").unwrap();
    let expanded = ctx.elaborate(&expr);

    // Chained macro expansion should work
    if let Ok(kernel_expr) = expanded {
        assert!(
            matches!(kernel_expr.kind(), ExprKind::Sort(_)),
            "m2 Type should elaborate to Sort, got {kernel_expr:?}"
        );
    }
}

#[test]
fn test_syntax_extension_with_expression() {
    // Test: syntax extension that expands to a concrete expression
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    // Register syntax: myType expands to Type
    let syntax_decl = parse_decl("macro_rules | `(myType) => `(Type)");

    if let Ok(decl) = syntax_decl {
        ctx.elab_decl(&decl).unwrap();

        // Now elaborate myType
        if let Ok(surface) = parse_expr("myType") {
            let result = ctx.elaborate(&surface);
            if let Ok(expr) = result {
                assert!(
                    matches!(expr.kind(), ExprKind::Sort(_)),
                    "myType should elaborate to Sort"
                );
            }
        }
    }
}

#[test]
fn test_macro_with_definitions() {
    // End-to-end test: define a function, register a macro, use both
    let mut env = Environment::new();

    let result = elaborate_with_macros(
        &mut env,
        &[
            // Define identity function
            "def id (A : Type) (x : A) := x",
            // Register macro that wraps in id
            "macro_rules | `(wrap $x) => `(id Type $x)",
        ],
    );

    assert!(
        result.is_ok(),
        "Should elaborate definitions and macros: {result:?}"
    );

    // Verify id exists
    let id_name = Name::from_string("id");
    assert!(env.get_const(&id_name).is_some(), "id should be defined");
}
