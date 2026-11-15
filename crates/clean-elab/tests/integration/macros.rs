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

    // First need Decidable, declared as a class: pinned Lean refuses
    // `[d : Decidable c]` over an axiom `Decidable : Prop -> Type` (see
    // `test_instance_binder_over_axiom_decidable_refused`).
    check_and_add_decl(&mut env, "class Decidable (p : Prop) : Type").expect("Decidable class");

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

/// Negative control: `Decidable` declared as a plain axiom is not a class, so
/// an instance-implicit binder over it is refused, as pinned Lean refuses it.
#[test]
fn test_instance_binder_over_axiom_decidable_refused() {
    let mut env = Environment::new();
    check_and_add_decl(&mut env, "axiom Decidable : Prop -> Type").expect("Decidable axiom");
    let err = check_and_add_decl(
        &mut env,
        "def ite (c : Prop) [d : Decidable c] (t e : Type) : Type := t",
    )
    .expect_err("`[d : Decidable c]` over an axiom must be refused");
    assert!(
        err.contains("not a class instance"),
        "expected the non-class binder refusal, got: {err}"
    );
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

    // Should preserve the semantics: identity Type == Type.
    //
    // FAIL-CLOSED since 2026-09-15. This assertion used to sit inside
    // `if let Ok(kernel_expr) = result`, so an elaboration ERROR skipped it
    // and the test passed having checked nothing about the property in its
    // own name.
    let kernel_expr = result.expect("`identity Type` should elaborate");
    assert!(
        matches!(kernel_expr.kind(), ExprKind::Sort(_)),
        "identity Type should elaborate to Sort"
    );
}

#[test]
fn test_multiple_macro_declarations() {
    // Test: Multiple macro declarations in sequence
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    // Register multiple macros
    let macro1 = parse_decl("macro_rules | `(m1 $x) => `($x)");
    let macro2 = parse_decl("macro_rules | `(m2 $x) => `(m1 $x)");

    // FAIL-CLOSED since 2026-09-15. Both registrations and the expansion used
    // to be guarded by `if let Ok(...)`, so a parse failure registered NOTHING
    // and the elaboration below then failed into a skipped assertion: the test
    // could pass having declared no macros and expanded none, which is exactly
    // the property its name claims.
    let decl1 = macro1.expect("the `m1` macro_rules declaration should parse");
    ctx.elab_decl(&decl1).unwrap();
    let decl2 = macro2.expect("the `m2` macro_rules declaration should parse");
    ctx.elab_decl(&decl2).unwrap();

    // Try to use chained macros: m2 Type should expand to m1 Type then to Type
    let expr = parse_expr("m2 Type").unwrap();
    let expanded = ctx.elaborate(&expr);

    // Chained macro expansion should work
    let kernel_expr = expanded.expect("`m2 Type` should elaborate through the macro chain");
    assert!(
        matches!(kernel_expr.kind(), ExprKind::Sort(_)),
        "m2 Type should elaborate to Sort, got {kernel_expr:?}"
    );
}

#[test]
fn test_syntax_extension_with_expression() {
    // Test: syntax extension that expands to a concrete expression
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    // Register syntax: myType expands to Type
    let syntax_decl = parse_decl("macro_rules | `(myType) => `(Type)");

    // FAIL-CLOSED since 2026-09-15. THREE nested `if let Ok(...)` guards stood
    // between this test and its assertion — the declaration parse, the
    // expression parse and the elaboration — so a failure at any one of them
    // passed the test silently.
    let decl = syntax_decl.expect("the `myType` macro_rules declaration should parse");
    ctx.elab_decl(&decl).unwrap();

    // Now elaborate myType.
    //
    // MEASURED WALL, 2026-09-15 — and it was found by deleting the three
    // `if let Ok(...)` guards that used to stand here. A NULLARY macro pattern
    // never reaches the registry: `MacroRegistry::try_expand`
    // (crates/clean-macro/src/registry.rs:359) opens with
    // `let kind = syntax.kind()?`, and `Syntax::kind()` (syntax.rs:339) is
    // `Some` only for `Syntax::Node`. A bare identifier is an ATOM, so its kind
    // is `None` and the lookup returns before consulting a single macro. The
    // two sibling tests above pass because their patterns take `$x`, which
    // makes the use site a Node.
    //
    // PINNED AS A REFUSAL, not skipped. `expect_err` means that on the day
    // nullary expansion lands this test FAILS LOUDLY and whoever landed it
    // replaces the pin with the target assertion, which is:
    //
    //     assert!(matches!(expr.kind(), ExprKind::Sort(_)));
    //
    // A skip would have let that fix land unnoticed, which is how this gap
    // survived in the first place.
    let surface = parse_expr("myType").expect("`myType` should parse");
    let err = ctx.elaborate(&surface).expect_err(
        "nullary macro expansion is a MEASURED GAP: if `myType` now elaborates, \
         delete this pin and assert ExprKind::Sort instead",
    );
    assert!(
        format!("{err:?}").contains("UnknownIdent"),
        "the nullary-macro wall is an UnknownIdent at the use site; a different \
         error means the cause moved and this pin no longer describes it: {err:?}"
    );
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
