// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Public direct-elaboration policy, exercised through genuine registered results.

use clean_elab::{
    elaborate_decl_and_register_with_context_and_warning, preprocess_decl_with_context,
    with_source_compilation_checks, ElabResult, FileContext,
};
use clean_kernel::{Environment, Name, TypeChecker};

const SOURCE: &str = "axiom n : Nat\ndef bad : Nat := n\n";

fn direct(source: &str) -> (Environment, Vec<ElabResult>) {
    let parsed = clean_parser::parse_file_with_diagnostics(source).expect("source parses");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut env = Environment::with_prelude();
    let mut context = FileContext::default();
    let results = parsed
        .decls
        .iter()
        .map(|decl| {
            let decl = preprocess_decl_with_context(decl, &mut context);
            elaborate_decl_and_register_with_context_and_warning(&mut env, &decl, &mut context)
                .expect("actual mathematical registration")
                .result
        })
        .collect();
    (env, results)
}

fn compiler_error() -> bool {
    let (env, results) = direct(SOURCE);
    let bad = env
        .get_const(&Name::from_string("bad"))
        .expect("registered bad");
    TypeChecker::new(&env)
        .check_type(
            bad.value.as_ref().expect("real value, not an axiom"),
            &bad.type_,
        )
        .expect("real mathematical kernel judgment");
    results[1]
        .source_error_message()
        .is_some_and(|error| error.contains("noncomputable"))
}

#[test]
fn source_compilation_scope_adds_source_errors_without_revoking_kernel_registration() {
    assert!(!clean_elab::source_compilation_checks_enabled());
    assert!(
        !compiler_error(),
        "ordinary direct elaboration remains mathematical"
    );
    assert!(with_source_compilation_checks(|| {
        assert!(clean_elab::source_compilation_checks_enabled());
        compiler_error()
    }));
    assert!(
        !compiler_error(),
        "the source scope must restore its prior policy"
    );
}

#[test]
fn source_compilation_scope_nested_calls_preserve_the_enabled_policy() {
    with_source_compilation_checks(|| {
        assert!(compiler_error());
        assert!(with_source_compilation_checks(compiler_error));
        assert!(
            compiler_error(),
            "the inner return cannot disable the outer scope"
        );
    });
    assert!(!compiler_error());
}

#[test]
fn source_compilation_scope_restores_after_unwinding() {
    let result = std::panic::catch_unwind(|| {
        with_source_compilation_checks(|| {
            assert!(compiler_error());
            panic!("intentional scope unwind");
        });
    });
    assert!(result.is_err());
    assert!(!clean_elab::source_compilation_checks_enabled());
    assert!(
        !compiler_error(),
        "unwinding must not leak source compiler policy"
    );
}

#[test]
fn source_compilation_scope_preserves_nested_result_diagnostics() {
    let (env, results) = with_source_compilation_checks(|| {
        direct("namespace Nested\naxiom n : Nat\ndef bad : Nat := n\nend Nested\n")
    });
    assert!(env.get_const(&Name::from_string("Nested.bad")).is_some());
    assert!(results.iter().any(|result| result
        .source_error_message()
        .is_some_and(|message| message.contains("noncomputable"))));
}
