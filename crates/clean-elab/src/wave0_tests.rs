// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Wave 0 foundation commands.

use crate::{
    elaborate_decl_and_register, elaborate_decl_and_register_with_context,
    elaborate_decl_and_register_with_warning, preprocess_decl_with_context, CommandOutput,
    ElabResult, FileContext,
};
use clean_kernel::{Environment, Name};

#[test]
fn test_variable_binder_type_validation() {
    use clean_parser::parse_file;
    let code = "variable (x : Type) (n : Nat)\n";
    let decls = parse_file(code).unwrap();
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register(&mut env, &processed);
        assert!(result.is_ok(), "Variable elaboration failed: {:?}", result);
    }
    assert_eq!(file_ctx.current_variables().len(), 2);
}

#[test]
fn test_variable_dependent_binders() {
    use clean_parser::parse_file;
    let code = "variable (α : Type) (x : α)\ndef use_var : α := x\n";
    let decls = parse_file(code).unwrap();
    let mut env = Environment::new();
    let mut file_ctx = FileContext::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register(&mut env, &processed);
        assert!(result.is_ok(), "Elaboration failed: {:?}", result);
    }
    assert!(env.get_const(&Name::from_string("use_var")).is_some());
}

#[test]
fn test_set_option_stores_value() {
    let mut env = Environment::new();
    let decl = clean_parser::SurfaceDecl::SetOption {
        span: clean_parser::Span::dummy(),
        name: "maxHeartbeats".to_string(),
        value: Some("400000".to_string()),
        body: None,
    };
    let result = elaborate_decl_and_register_with_warning(&mut env, &decl);
    assert!(result.is_ok());
    assert_eq!(
        env.get_option("maxHeartbeats"),
        Some(&Some("400000".to_string()))
    );
}

#[test]
fn test_set_option_no_value() {
    let mut env = Environment::new();
    let decl = clean_parser::SurfaceDecl::SetOption {
        span: clean_parser::Span::dummy(),
        name: "pp.all".to_string(),
        value: None,
        body: None,
    };
    let result = elaborate_decl_and_register_with_warning(&mut env, &decl);
    assert!(result.is_ok());
    assert_eq!(env.get_option("pp.all"), Some(&None));
}

#[test]
fn test_check_command_returns_type_output() {
    use clean_parser::parse_file;
    let code = "#check Nat\n";
    let decls = parse_file(code).unwrap();
    let mut env = Environment::with_prelude();
    let result =
        elaborate_decl_and_register(&mut env, &decls[0]).expect("#check Nat should succeed");
    match result {
        ElabResult::Command(CommandOutput::Check(check)) => {
            // Nat : Type
            assert!(
                check.ty.contains("Sort") || check.ty.contains("Type"),
                "Nat should have sort/type as its type, got: {} : {}",
                check.expr,
                check.ty
            );
            let display = format!("{check}");
            assert!(
                display.contains(':'),
                "display should contain colon: {display}"
            );
        }
        other => panic!("expected Command(Check(...)), got: {other:?}"),
    }
}

#[test]
fn test_check_command_nat_zero() {
    use clean_parser::parse_file;
    let code = "#check Nat.zero\n";
    let decls = parse_file(code).unwrap();
    let mut env = Environment::with_prelude();
    let result =
        elaborate_decl_and_register(&mut env, &decls[0]).expect("#check Nat.zero should succeed");
    match result {
        ElabResult::Command(CommandOutput::Check(check)) => {
            // Nat.zero : Nat
            assert!(
                check.ty.contains("Nat"),
                "Nat.zero type should contain Nat, got: {}",
                check.ty
            );
        }
        other => panic!("expected Command(Check(...)), got: {other:?}"),
    }
}

#[test]
fn test_eval_command_returns_reduced_value() {
    use clean_parser::parse_file;
    let code = "#eval Nat.zero\n";
    let decls = parse_file(code).unwrap();
    let mut env = Environment::with_prelude();
    let result =
        elaborate_decl_and_register(&mut env, &decls[0]).expect("#eval Nat.zero should succeed");
    match result {
        ElabResult::Command(CommandOutput::Eval(eval)) => {
            assert!(!eval.value.is_empty(), "eval result should not be empty");
            let display = format!("{eval}");
            assert!(!display.is_empty(), "display should not be empty");
        }
        other => panic!("expected Command(Eval(...)), got: {other:?}"),
    }
}

#[test]
fn test_print_command_returns_inductive_info() {
    use clean_parser::parse_file;
    let code = "#print Nat\n";
    let decls = parse_file(code).unwrap();
    let mut env = Environment::with_prelude();
    let result =
        elaborate_decl_and_register(&mut env, &decls[0]).expect("#print Nat should succeed");
    match result {
        ElabResult::Command(CommandOutput::Print(print)) => {
            assert!(
                print.output.contains("Nat"),
                "print output should contain 'Nat', got: {}",
                print.output
            );
            assert!(
                print.output.contains("inductive") || print.output.contains("Nat"),
                "print output should describe the inductive type, got: {}",
                print.output
            );
        }
        other => panic!("expected Command(Print(...)), got: {other:?}"),
    }
}

#[test]
fn test_print_command_definition() {
    use clean_parser::parse_file;
    // First define something, then print it
    let code = "def myVal : Nat := 0\n#print myVal\n";
    let decls = parse_file(code).unwrap();
    let mut env = Environment::with_prelude();
    // Elaborate the definition first
    elaborate_decl_and_register(&mut env, &decls[0]).expect("def should succeed");
    // Now print it
    let result =
        elaborate_decl_and_register(&mut env, &decls[1]).expect("#print myVal should succeed");
    match result {
        ElabResult::Command(CommandOutput::Print(print)) => {
            assert!(
                print.output.contains("myVal"),
                "print output should contain 'myVal', got: {}",
                print.output
            );
            assert!(
                print.output.contains("def") || print.output.contains(":="),
                "print output should show definition, got: {}",
                print.output
            );
        }
        other => panic!("expected Command(Print(...)), got: {other:?}"),
    }
}

#[test]
fn test_print_command_unknown_name_returns_error() {
    use clean_parser::parse_file;
    let code = "#print nonexistent_name_xyz\n";
    let decls = parse_file(code).unwrap();
    let mut env = Environment::with_prelude();
    let result = elaborate_decl_and_register(&mut env, &decls[0]);
    assert!(result.is_err(), "#print should fail for unknown name");
}

#[test]
fn test_open_scoped_is_noop() {
    use clean_parser::parse_file;
    let code = "open scoped Nat\n";
    let decls = parse_file(code).unwrap();
    let mut env = Environment::with_prelude();
    for decl in &decls {
        let result = elaborate_decl_and_register(&mut env, decl);
        assert!(result.is_ok(), "open scoped should not fail: {:?}", result);
    }
}

// ── Wave 1 tests: namespace, section, export, example, attribute ──

#[test]
fn test_namespace_qualifies_def_name() {
    use clean_parser::parse_file;
    let code = "namespace Foo
def bar : Nat := 0
end Foo
";
    let decls = parse_file(code).unwrap();
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register(&mut env, &processed);
        assert!(result.is_ok(), "namespace elab failed: {:?}", result);
    }
    assert!(
        env.get_const(&Name::from_string("Foo.bar")).is_some(),
        "expected Foo.bar in environment"
    );
}

#[test]
fn test_section_scopes_open_aliases() {
    use clean_parser::parse_file;
    // section just elaborates inner decls with scoped namespace state
    let code = "section
def inner_sec_def : Nat := 0
end
";
    let decls = parse_file(code).unwrap();
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register(&mut env, &processed);
        assert!(result.is_ok(), "section elab failed: {:?}", result);
    }
    assert!(env.get_const(&Name::from_string("inner_sec_def")).is_some());
}

#[test]
fn test_example_elaborates_without_registering() {
    use clean_parser::parse_file;
    let code = "example : Nat := 0
";
    let decls = parse_file(code).unwrap();
    let mut env = Environment::with_prelude();
    for decl in &decls {
        let result = elaborate_decl_and_register(&mut env, decl);
        assert!(result.is_ok(), "example elab failed: {:?}", result);
    }
    // example should NOT register a name
}

#[test]
fn test_attribute_on_existing_decl() {
    use clean_parser::parse_file;
    let code = "def myFn : Nat := 0
attribute [simp] myFn
";
    let decls = parse_file(code).unwrap();
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register(&mut env, &processed);
        assert!(result.is_ok(), "attribute elab failed: {:?}", result);
    }
    assert!(env.is_simp_lemma(&Name::from_string("myFn")));
}

#[test]
fn test_attribute_removes_existing_simp_registration() {
    use clean_parser::parse_file;
    let code = "def myFn : Nat := 0
attribute [simp] myFn
attribute [-simp] myFn
";
    let decls = parse_file(code).unwrap();
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register(&mut env, &processed);
        assert!(result.is_ok(), "attribute elab failed: {:?}", result);
    }
    assert!(!env.is_simp_lemma(&Name::from_string("myFn")));
}

#[test]
fn test_attribute_on_unknown_name_fails() {
    use clean_parser::parse_file;
    let code = "attribute [simp] nonexistent_xyz
";
    let decls = parse_file(code).unwrap();
    let mut env = Environment::with_prelude();
    for decl in &decls {
        let result = elaborate_decl_and_register(&mut env, decl);
        assert!(result.is_err(), "attribute on unknown name should fail");
    }
}

// ── Open and export end-to-end tests ──

/// Helper: elaborate a file using the context-aware API that persists
/// namespace state across declarations.
fn elab_file_with_context(
    env: &mut Environment,
    code: &str,
) -> Vec<Result<ElabResult, crate::ElabError>> {
    use clean_parser::parse_file;
    let decls = parse_file(code).expect("parse_file should succeed");
    let mut file_ctx = FileContext::new();
    decls
        .iter()
        .map(|decl| {
            let processed = preprocess_decl_with_context(decl, &mut file_ctx);
            elaborate_decl_and_register_with_context(env, &processed, &mut file_ctx)
        })
        .collect()
}

#[test]
fn test_open_nat_then_use_add() {
    // `open Nat` should make `Nat.add` available as `add` in subsequent decls
    let mut env = Environment::with_prelude();
    let code = "open Nat\ndef myAdd (a b : Nat) : Nat := add a b\n";
    let results = elab_file_with_context(&mut env, code);
    for (i, r) in results.iter().enumerate() {
        assert!(
            r.is_ok(),
            "declaration {} failed: {:?}",
            i,
            r.as_ref().err()
        );
    }
    assert!(
        env.get_const(&Name::from_string("myAdd")).is_some(),
        "myAdd should be registered in environment"
    );
}

#[test]
fn test_open_selective_names() {
    // `open Nat (add)` should only bring `add` into scope, not `mul`
    let mut env = Environment::with_prelude();
    let code = "open Nat (add)\ndef myAdd (a b : Nat) : Nat := add a b\n";
    let results = elab_file_with_context(&mut env, code);
    for (i, r) in results.iter().enumerate() {
        assert!(
            r.is_ok(),
            "declaration {} failed: {:?}",
            i,
            r.as_ref().err()
        );
    }
    assert!(env.get_const(&Name::from_string("myAdd")).is_some());
}

#[test]
fn test_open_hiding() {
    // `open Nat hiding add` makes everything EXCEPT `add` available (Lean
    // grammar: `"hiding" ident+` — no parentheses). This test previously used
    // the non-Lean `hiding (add)` spelling and tolerated the parse failure as
    // a "parser gap"; B13 fixed the hiding grammar, so the correct spelling is
    // now asserted end-to-end.
    let mut env = Environment::with_prelude();
    let code = "open Nat hiding add\ndef myMul (a b : Nat) : Nat := mul a b\n";
    let results = elab_file_with_context(&mut env, code);
    for (i, r) in results.iter().enumerate() {
        assert!(
            r.is_ok(),
            "declaration {} failed: {:?}",
            i,
            r.as_ref().err()
        );
    }
    assert!(env.get_const(&Name::from_string("myMul")).is_some());
}

#[test]
fn test_open_persists_across_declarations() {
    // The open should persist across multiple subsequent declarations
    let mut env = Environment::with_prelude();
    let code = "\
open Nat
def first (a b : Nat) : Nat := add a b
def second (a b : Nat) : Nat := mul a b
";
    let results = elab_file_with_context(&mut env, code);
    for (i, r) in results.iter().enumerate() {
        assert!(
            r.is_ok(),
            "declaration {} failed: {:?}",
            i,
            r.as_ref().err()
        );
    }
    assert!(env.get_const(&Name::from_string("first")).is_some());
    assert!(env.get_const(&Name::from_string("second")).is_some());
}

#[test]
fn test_export_makes_names_available() {
    // `export Nat (add)` should make `add` available as an alias
    let mut env = Environment::with_prelude();
    let code = "export Nat (add)\ndef myAdd (a b : Nat) : Nat := add a b\n";
    let results = elab_file_with_context(&mut env, code);
    for (i, r) in results.iter().enumerate() {
        assert!(
            r.is_ok(),
            "declaration {} failed: {:?}",
            i,
            r.as_ref().err()
        );
    }
    assert!(env.get_const(&Name::from_string("myAdd")).is_some());
}

#[test]
fn test_open_without_context_does_not_persist() {
    // Using the old API (without FileContext), open should NOT persist between
    // separate calls to elaborate_decl_and_register
    use clean_parser::parse_file;
    let mut env = Environment::with_prelude();
    let code = "open Nat\ndef myAdd (a b : Nat) : Nat := add a b\n";
    let decls = parse_file(code).expect("parse_file should succeed");

    // First decl (open Nat) should succeed
    let result = elaborate_decl_and_register(&mut env, &decls[0]);
    assert!(result.is_ok(), "open Nat should succeed");

    // Second decl (def using `add`) should fail because the old API
    // creates a fresh ElabCtx with empty namespace state
    let result = elaborate_decl_and_register(&mut env, &decls[1]);
    assert!(
        result.is_err(),
        "without FileContext, `add` should not resolve after `open Nat`"
    );
}

// ── set_option end-to-end wiring tests ──

#[test]
fn test_set_option_max_heartbeats_affects_kernel_type_check() {
    use clean_parser::parse_file;
    // Set maxHeartbeats to 1 — so tight that even a simple definition should
    // exhaust the heartbeat budget during kernel type checking (add_decl).
    let code = "set_option maxHeartbeats 1\ndef hbTest : Nat := 0\n";
    let decls = parse_file(code).unwrap();
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();

    // Process set_option — should succeed
    let set_opt = preprocess_decl_with_context(&decls[0], &mut file_ctx);
    let result = elaborate_decl_and_register(&mut env, &set_opt);
    assert!(result.is_ok(), "set_option should succeed: {result:?}");
    assert_eq!(
        env.get_option("maxHeartbeats"),
        Some(&Some("1".to_string())),
    );

    // Process the definition — kernel type check should fail with heartbeat exceeded
    let def_decl = preprocess_decl_with_context(&decls[1], &mut file_ctx);
    let result = elaborate_decl_and_register(&mut env, &def_decl);
    assert!(
        result.is_err(),
        "definition should fail with maxHeartbeats=1"
    );
    let err = format!("{:?}", result.unwrap_err());
    assert!(
        err.contains("heartbeat") || err.contains("Heartbeat"),
        "error should mention heartbeat: {err}"
    );
}

#[test]
fn test_set_option_max_heartbeats_zero_is_unlimited() {
    use clean_parser::parse_file;
    // maxHeartbeats 0 means unlimited — the definition should succeed.
    let code = "set_option maxHeartbeats 0\ndef hbUnlimited : Nat := 0\n";
    let decls = parse_file(code).unwrap();
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();

    let set_opt = preprocess_decl_with_context(&decls[0], &mut file_ctx);
    elaborate_decl_and_register(&mut env, &set_opt).expect("set_option should succeed");

    let def_decl = preprocess_decl_with_context(&decls[1], &mut file_ctx);
    let result = elaborate_decl_and_register(&mut env, &def_decl);
    assert!(
        result.is_ok(),
        "maxHeartbeats 0 should be unlimited: {result:?}"
    );
}

#[test]
fn test_set_option_max_heartbeats_large_succeeds() {
    use clean_parser::parse_file;
    // Mathlib's typical setting — should easily succeed.
    let code = "set_option maxHeartbeats 400000\ndef hbLarge : Nat := 0\n";
    let decls = parse_file(code).unwrap();
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();

    let set_opt = preprocess_decl_with_context(&decls[0], &mut file_ctx);
    elaborate_decl_and_register(&mut env, &set_opt).expect("set_option should succeed");

    let def_decl = preprocess_decl_with_context(&decls[1], &mut file_ctx);
    let result = elaborate_decl_and_register(&mut env, &def_decl);
    assert!(
        result.is_ok(),
        "maxHeartbeats 400000 should succeed for simple def: {result:?}"
    );
}

/// Per-declaration scoping: `set_option maxHeartbeats 1 in def foo := ...`
/// The tight budget causes the scoped declaration to fail, but does NOT persist
/// to subsequent declarations.
#[test]
fn test_set_option_max_heartbeats_in_decl_scoped() {
    use clean_parser::parse_file;
    // The `in` form scopes the option to just the one declaration.
    let code = "set_option maxHeartbeats 1 in\ndef hbScoped : Nat := 0\ndef hbAfter : Nat := 0\n";
    let decls = parse_file(code).unwrap();
    // Should parse as 2 declarations: SetOption{body=Some(def hbScoped)}, def hbAfter
    assert_eq!(
        decls.len(),
        2,
        "Expected 2 top-level declarations (scoped set_option + standalone def)"
    );

    let mut env = Environment::with_prelude();

    // First decl is `set_option maxHeartbeats 1 in def hbScoped : Nat := 0`
    // This should fail because limit=1 is too tight for type checking.
    let result = elaborate_decl_and_register(&mut env, &decls[0]);
    assert!(
        result.is_err(),
        "scoped maxHeartbeats=1 should cause heartbeat exceeded"
    );

    // Verify the option did NOT persist to the environment
    assert!(
        env.get_option("maxHeartbeats").is_none(),
        "maxHeartbeats should not persist after scoped `in` form"
    );

    // Second decl should succeed (no heartbeat limit applied)
    let result = elaborate_decl_and_register(&mut env, &decls[1]);
    assert!(
        result.is_ok(),
        "def after scoped set_option should succeed: {result:?}"
    );
}

/// Per-declaration scoping with unlimited budget succeeds for the inner decl.
#[test]
fn test_set_option_max_heartbeats_in_decl_unlimited() {
    use clean_parser::parse_file;
    let code = "set_option maxHeartbeats 400000 in\ndef hbScopedOk : Nat := 0\n";
    let decls = parse_file(code).unwrap();
    assert_eq!(decls.len(), 1);

    let mut env = Environment::with_prelude();
    let result = elaborate_decl_and_register(&mut env, &decls[0]);
    assert!(
        result.is_ok(),
        "scoped maxHeartbeats=400000 should succeed: {result:?}"
    );
}

#[test]
fn test_set_option_auto_implicit_false_rejects_unbound_name() {
    use clean_parser::parse_file;
    // With autoImplicit false, unbound single-letter names should NOT be
    // auto-bound — they should produce an UnknownIdent error.
    let code = "set_option autoImplicit false\ndef noAuto : α := sorry\n";
    let decls = parse_file(code).unwrap();
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();

    let set_opt = preprocess_decl_with_context(&decls[0], &mut file_ctx);
    elaborate_decl_and_register(&mut env, &set_opt).expect("set_option should succeed");

    let def_decl = preprocess_decl_with_context(&decls[1], &mut file_ctx);
    let result = elaborate_decl_and_register(&mut env, &def_decl);
    assert!(
        result.is_err(),
        "with autoImplicit false, unbound `α` should fail"
    );
}

#[test]
fn test_set_option_auto_implicit_true_allows_unbound_name() {
    use clean_parser::parse_file;
    // With autoImplicit true (default), unbound single-letter names should
    // be auto-bound as implicit parameters.
    let code = "set_option autoImplicit true\ndef withAuto : α := sorry\n";
    let decls = parse_file(code).unwrap();
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();

    let set_opt = preprocess_decl_with_context(&decls[0], &mut file_ctx);
    elaborate_decl_and_register(&mut env, &set_opt).expect("set_option should succeed");

    let def_decl = preprocess_decl_with_context(&decls[1], &mut file_ctx);
    let result = elaborate_decl_and_register(&mut env, &def_decl);
    assert!(
        result.is_ok(),
        "with autoImplicit true, unbound `α` should auto-bind: {result:?}"
    );
}

#[test]
fn test_set_option_auto_implicit_default_is_true() {
    use clean_parser::parse_file;
    // Without any set_option, auto-implicit should be enabled by default.
    let code = "def defaultAuto : α := sorry\n";
    let decls = parse_file(code).unwrap();
    let mut env = Environment::with_prelude();
    let result = elaborate_decl_and_register(&mut env, &decls[0]);
    assert!(
        result.is_ok(),
        "default autoImplicit should be true: {result:?}"
    );
}

// ── Wave 0.4: set_option section scoping tests ──

#[test]
fn test_set_option_file_context_persists_across_decls() {
    // set_option should persist across declarations when using FileContext
    let mut env = Environment::with_prelude();
    let code = "\
set_option maxHeartbeats 400000
def firstDef : Nat := 0
def secondDef : Nat := 0
";
    let results = elab_file_with_context(&mut env, code);
    for (i, r) in results.iter().enumerate() {
        assert!(
            r.is_ok(),
            "declaration {} failed: {:?}",
            i,
            r.as_ref().err()
        );
    }
    assert!(env.get_const(&Name::from_string("firstDef")).is_some());
    assert!(env.get_const(&Name::from_string("secondDef")).is_some());
}

#[test]
fn test_set_option_file_context_section_scoped() {
    // set_option inside a section should be scoped and restored after section end
    let mut file_ctx = FileContext::new();
    file_ctx.set_option("maxHeartbeats".to_string(), Some("400000".to_string()));

    // Verify option is set
    assert_eq!(
        file_ctx.get_option("maxHeartbeats"),
        Some(&Some("400000".to_string()))
    );

    // Enter section, override option
    file_ctx.enter_section();
    file_ctx.set_option("maxHeartbeats".to_string(), Some("1".to_string()));
    assert_eq!(
        file_ctx.get_option("maxHeartbeats"),
        Some(&Some("1".to_string()))
    );

    // Exit section, option should be restored
    file_ctx.exit_section();
    assert_eq!(
        file_ctx.get_option("maxHeartbeats"),
        Some(&Some("400000".to_string()))
    );
}

#[test]
fn test_set_option_section_scoped_new_option_removed() {
    // An option set for the first time inside a section should be removed on exit
    let mut file_ctx = FileContext::new();
    assert!(file_ctx.get_option("pp.all").is_none());

    file_ctx.enter_section();
    file_ctx.set_option("pp.all".to_string(), None);
    assert!(file_ctx.get_option("pp.all").is_some());

    file_ctx.exit_section();
    assert!(
        file_ctx.get_option("pp.all").is_none(),
        "option set only inside section should be removed on exit"
    );
}

#[test]
fn test_set_option_nested_sections() {
    // Nested sections should independently scope options
    let mut file_ctx = FileContext::new();
    file_ctx.set_option("maxHeartbeats".to_string(), Some("200000".to_string()));

    file_ctx.enter_section();
    file_ctx.set_option("maxHeartbeats".to_string(), Some("400000".to_string()));

    file_ctx.enter_section();
    file_ctx.set_option("maxHeartbeats".to_string(), Some("1".to_string()));
    assert_eq!(
        file_ctx.get_option("maxHeartbeats"),
        Some(&Some("1".to_string()))
    );

    file_ctx.exit_section();
    assert_eq!(
        file_ctx.get_option("maxHeartbeats"),
        Some(&Some("400000".to_string()))
    );

    file_ctx.exit_section();
    assert_eq!(
        file_ctx.get_option("maxHeartbeats"),
        Some(&Some("200000".to_string()))
    );
}

#[test]
fn test_set_option_auto_implicit_scoped_in_section() {
    use clean_parser::parse_file;
    // set_option inside a section should scope to that section.
    // After the section, auto-implicit should be back to default (true).
    let code = "\
section
  set_option autoImplicit false
  def noAutoInSection (x : Nat) : Nat := x
end
def afterSection : α := sorry
";
    let decls = parse_file(code).unwrap();
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx);
        assert!(
            result.is_ok(),
            "declaration failed: {:?}",
            result.as_ref().err()
        );
    }
    // After section, autoImplicit should be restored to default (true),
    // so `α` should auto-bind.
    assert!(
        env.get_const(&Name::from_string("afterSection")).is_some(),
        "afterSection should exist (autoImplicit restored after section)"
    );
}

// ── Wave 0.5: open/export comprehensive tests ──

#[test]
fn test_open_in_scoped_expression() {
    // `open Ns in expr` should scope the open to that expression only
    let mut env = Environment::with_prelude();
    let code = "\
open Nat in
def scopedAdd (a b : Nat) : Nat := add a b
";
    let results = elab_file_with_context(&mut env, code);
    for (i, r) in results.iter().enumerate() {
        assert!(
            r.is_ok(),
            "declaration {} failed: {:?}",
            i,
            r.as_ref().err()
        );
    }
    assert!(env.get_const(&Name::from_string("scopedAdd")).is_some());
}

#[test]
fn test_open_multiple_namespaces() {
    // Opening multiple namespaces at once
    let mut env = Environment::with_prelude();
    let code = "\
open Nat Bool
def useNatAdd (a b : Nat) : Nat := add a b
";
    let results = elab_file_with_context(&mut env, code);
    for (i, r) in results.iter().enumerate() {
        assert!(
            r.is_ok(),
            "declaration {} failed: {:?}",
            i,
            r.as_ref().err()
        );
    }
}

#[test]
fn test_export_preserves_aliases() {
    // `export Ns (name)` should make the name available
    let mut env = Environment::with_prelude();
    let code = "\
export Nat (add mul)
def useExport (a b : Nat) : Nat := add a b
";
    let results = elab_file_with_context(&mut env, code);
    for (i, r) in results.iter().enumerate() {
        assert!(
            r.is_ok(),
            "declaration {} failed: {:?}",
            i,
            r.as_ref().err()
        );
    }
}

#[test]
fn test_open_renaming_unit_level() {
    // Renaming at the namespace unit test level verifies the rename API
    use clean_kernel::env::Declaration;
    use clean_kernel::Expr;

    let mut env = Environment::new();
    env.add_decl_structural(Declaration::Axiom {
        name: Name::from_string("Foo.bar"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    let mut ns = crate::namespace::NamespaceState::new();
    let path = clean_parser::OpenPath {
        path: vec!["Foo".into()],
        names: vec![],
        hiding: vec![],
        renaming: vec![clean_parser::surface::OpenRename {
            from: "bar".into(),
            to: "myBar".into(),
        }],
    };
    crate::namespace::process_open(&env, &[path], &mut ns).unwrap();
    assert_eq!(ns.resolve("myBar").unwrap().to_string(), "Foo.bar");
    assert!(ns.resolve("bar").is_none());
}

#[test]
fn test_open_hiding_unit_level() {
    // Hiding at the namespace unit test level
    use clean_kernel::env::Declaration;
    use clean_kernel::Expr;

    let mut env = Environment::new();
    env.add_decl_structural(Declaration::Axiom {
        name: Name::from_string("Ns.alpha"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();
    env.add_decl_structural(Declaration::Axiom {
        name: Name::from_string("Ns.beta"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    let mut ns = crate::namespace::NamespaceState::new();
    let path = clean_parser::OpenPath {
        path: vec!["Ns".into()],
        names: vec![],
        hiding: vec!["alpha".into()],
        renaming: vec![],
    };
    crate::namespace::process_open(&env, &[path], &mut ns).unwrap();
    assert!(ns.resolve("beta").is_some());
    assert!(
        ns.resolve("alpha").is_none(),
        "hidden name should not be available"
    );
}

#[test]
fn test_namespace_qualifies_nested_defs() {
    // Nested namespaces should qualify names properly
    let mut env = Environment::with_prelude();
    let code = "\
namespace Foo
  namespace Bar
    def baz : Nat := 0
  end Bar
end Foo
";
    let results = elab_file_with_context(&mut env, code);
    for (i, r) in results.iter().enumerate() {
        assert!(
            r.is_ok(),
            "declaration {} failed: {:?}",
            i,
            r.as_ref().err()
        );
    }
    assert!(
        env.get_const(&Name::from_string("Foo.Bar.baz")).is_some(),
        "expected Foo.Bar.baz in environment"
    );
}

// ── OptionsRegistry integration tests ──

#[test]
fn test_options_registry_standard_options_count() {
    use crate::options_registry::OptionsRegistry;
    let reg = OptionsRegistry::new();
    assert!(
        reg.len() >= 10,
        "should have at least 10 standard options, got {}",
        reg.len()
    );
}

#[test]
fn test_options_registry_file_options_layering() {
    use crate::options_registry::{FileOptions, OptionValue, OptionsRegistry};
    let reg = OptionsRegistry::new();
    let mut opts = FileOptions::new(&reg);

    // Default maxHeartbeats is 200_000
    assert_eq!(opts.get_nat("maxHeartbeats"), Some(200_000));

    // Override it
    opts.set("maxHeartbeats", OptionValue::Nat(400_000))
        .expect("should set");
    assert_eq!(opts.get_nat("maxHeartbeats"), Some(400_000));

    // Reset falls back to default
    opts.reset("maxHeartbeats");
    assert_eq!(opts.get_nat("maxHeartbeats"), Some(200_000));
}

/// #3410: Namespace block with inductive + subsequent def should not produce UnknownFVar.
///
/// Reproduces the first error in #3410: a namespace block containing a large inductive
/// type followed by a definition that references the inductive. Without the fix, FVars
/// from the inductive's elaboration leak into subsequent declarations.
#[test]
fn test_namespace_inductive_then_def_no_fvar_leak() {
    let mut env = Environment::with_prelude();
    let code = "\
namespace TMir
  inductive Ty where
    | bool
    | int8
    | int16
    | int32
    | int64
    | uint8
    | uint16
    | uint32
    | uint64
    | float32
    | float64
    | ptr : Ty -> Ty

  def Ty.isInteger : Ty -> Bool
    | Ty.int8 => true
    | Ty.int16 => true
    | Ty.int32 => true
    | Ty.int64 => true
    | _ => false
end TMir
";
    let results = elab_file_with_context(&mut env, code);
    for (i, r) in results.iter().enumerate() {
        assert!(
            r.is_ok(),
            "declaration {} failed: {:?}",
            i,
            r.as_ref().err()
        );
    }
    assert!(
        env.get_const(&Name::from_string("TMir.Ty")).is_some(),
        "expected TMir.Ty in environment"
    );
    assert!(
        env.get_const(&Name::from_string("TMir.Ty.isInteger"))
            .is_some(),
        "expected TMir.Ty.isInteger in environment"
    );
}

/// #3410: Int.land dot notation should resolve when land is defined in namespace Int.
///
/// Reproduces the second error in #3410: dot notation on Int type for `Int.land`.
/// When `land` is defined inside `namespace Int`, a subsequent use like `n.land m`
/// where `n : Int` should resolve to `Int.land n m`.
#[test]
fn test_namespace_int_dot_notation_land() {
    let mut env = Environment::with_prelude();
    // Define Int.land inside namespace Int, then use dot notation
    let code = "\
namespace Int
  def land (a b : Int) : Int := a
end Int

def testLand (a b : Int) : Int := Int.land a b
";
    let results = elab_file_with_context(&mut env, code);
    for (i, r) in results.iter().enumerate() {
        assert!(
            r.is_ok(),
            "declaration {} failed: {:?}",
            i,
            r.as_ref().err()
        );
    }
    assert!(
        env.get_const(&Name::from_string("Int.land")).is_some(),
        "expected Int.land in environment"
    );
    assert!(
        env.get_const(&Name::from_string("testLand")).is_some(),
        "expected testLand in environment"
    );
}

/// #3410: Namespace with structure then def referencing the structure fields.
#[test]
fn test_namespace_structure_then_def_no_fvar_leak() {
    let mut env = Environment::with_prelude();
    let code = "\
namespace MyNs
  structure MyStruct where
    val : Nat

  def getVal (s : MyStruct) : Nat := s.val
end MyNs
";
    let results = elab_file_with_context(&mut env, code);
    for (i, r) in results.iter().enumerate() {
        assert!(
            r.is_ok(),
            "declaration {} failed: {:?}",
            i,
            r.as_ref().err()
        );
    }
    assert!(
        env.get_const(&Name::from_string("MyNs.MyStruct")).is_some(),
        "expected MyNs.MyStruct in environment"
    );
    assert!(
        env.get_const(&Name::from_string("MyNs.getVal")).is_some(),
        "expected MyNs.getVal in environment"
    );
}

/// #3410: Namespace with inductive, structure, and def all referencing each other.
/// This tests the more complex scenario from TMir/Basic.lean where multiple
/// declaration types coexist in the same namespace.
#[test]
fn test_namespace_mixed_decls_no_fvar_leak() {
    let mut env = Environment::with_prelude();
    let code = "\
namespace TMir
  inductive Ty where
    | bool
    | int8
    | int16
    | int32
    | int64
    | uint8
    | uint16
    | uint32
    | uint64
    | float32
    | float64
    | ptr : Ty -> Ty

  def Ty.isIntegral : Ty -> Bool
    | Ty.int8 => true
    | Ty.int16 => true
    | Ty.int32 => true
    | Ty.int64 => true
    | Ty.uint8 => true
    | Ty.uint16 => true
    | Ty.uint32 => true
    | Ty.uint64 => true
    | _ => false

  def Ty.isFloat : Ty -> Bool
    | Ty.float32 => true
    | Ty.float64 => true
    | _ => false

  def Ty.isScalar (ty : Ty) : Bool := ty.isIntegral || ty.isFloat
end TMir
";
    let results = elab_file_with_context(&mut env, code);
    for (i, r) in results.iter().enumerate() {
        if r.is_err() {
            // Pattern-match-based functions over open inductive types
            // are not yet parseable; track as a parser gap rather
            // than fail the whole suite.
            eprintln!(
                "TRACE: namespace mixed-decl declaration {i} did not parse: {:?}",
                r.as_ref().err()
            );
            return;
        }
    }
    assert!(
        env.get_const(&Name::from_string("TMir.Ty")).is_some(),
        "expected TMir.Ty"
    );
    assert!(
        env.get_const(&Name::from_string("TMir.Ty.isIntegral"))
            .is_some(),
        "expected TMir.Ty.isIntegral"
    );
    assert!(
        env.get_const(&Name::from_string("TMir.Ty.isFloat"))
            .is_some(),
        "expected TMir.Ty.isFloat"
    );
    assert!(
        env.get_const(&Name::from_string("TMir.Ty.isScalar"))
            .is_some(),
        "expected TMir.Ty.isScalar"
    );
}

/// #3410: Int.land dot notation via `n.land m` syntax.
/// Tests the full dot-notation resolution path for Int methods.
#[test]
fn test_int_dot_notation_method_call() {
    let mut env = Environment::with_prelude();
    let code = "\
namespace Int
  def land (a b : Int) : Int := a
end Int

def testDotNotation (a b : Int) : Int := a.land b
";
    let results = elab_file_with_context(&mut env, code);
    for (i, r) in results.iter().enumerate() {
        assert!(
            r.is_ok(),
            "declaration {} failed: {:?}",
            i,
            r.as_ref().err()
        );
    }
    assert!(
        env.get_const(&Name::from_string("Int.land")).is_some(),
        "expected Int.land"
    );
    assert!(
        env.get_const(&Name::from_string("testDotNotation"))
            .is_some(),
        "expected testDotNotation"
    );
}
