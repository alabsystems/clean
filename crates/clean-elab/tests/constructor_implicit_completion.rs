// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Frozen Lean 4.35 constructor-generalization boundary, via source registration.
use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::{Environment, Name};
use clean_parser::parse_file_with_diagnostics;

fn failed(result: &ElabResult) -> bool {
    match result {
        ElabResult::Failed { .. } => true,
        ElabResult::Multiple(results) => results.iter().any(failed),
        _ => false,
    }
}

#[test]
fn constructor_implicit_completion_matches_frozen_oracle() {
    let cases = [
        ("historical-1616", include_str!("../../../reports/constructor-implicit-2026-11-13/fixtures/historical-1616.lean"), false),
        ("fully-explicit-linear", include_str!("../../../reports/constructor-implicit-2026-11-13/fixtures/fully-explicit-linear.lean"), true),
        ("cover-only", include_str!("../../../reports/constructor-implicit-2026-11-13/fixtures/cover-only.lean"), true),
        ("palindrome", include_str!("../../../reports/constructor-implicit-2026-11-13/fixtures/palindrome.lean"), true),
    ];
    let mut mismatches = Vec::new();
    for (name, source, accepted) in cases {
        let parsed = parse_file_with_diagnostics(source).expect("frozen fixture parses");
        assert!(
            parsed.diagnostics.is_empty(),
            "{name}: {:?}",
            parsed.diagnostics
        );
        let mut env = Environment::with_prelude();
        let mut context = FileContext::new();
        context.set_main_module(Name::from_string("ConstructorCompletion"));
        context.set_file_header(&parsed.header);
        let mut errors = Vec::new();
        for decl in parsed.decls {
            let decl = preprocess_decl_with_context(&decl, &mut context);
            match elaborate_decl_and_register_with_context(&mut env, &decl, &mut context) {
                Ok(result) if failed(&result) => errors.push(format!("{result:?}")),
                Ok(_) => {}
                Err(error) => errors.push(error.to_string()),
            }
        }
        if errors.is_empty() != accepted {
            mismatches.push(format!("{name}: accepted={accepted}, errors={errors:?}"));
        }
        if !accepted {
            assert!(env.get_const(&Name::from_string("Linear")).is_none());
        }
    }
    assert!(mismatches.is_empty(), "{}", mismatches.join("\n"));
}
