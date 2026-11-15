// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Frozen Lean4.35 mutable-shadowing controls via source registration.
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
fn supported_mutable_shadowing_controls_match_frozen_oracle() {
    // The after-return oracle fixture remains a separately measured existing
    // Lean4.8-vs4.35 control-flow gap, outside these shadowing agreements.
    let cases = [
        ("historical-916", include_str!("../../../reports/mutable-shadowing-2026-11-13/fixtures/historical-916.lean"), false),
        ("let-shadow", include_str!("../../../reports/mutable-shadowing-2026-11-13/fixtures/let-shadow.lean"), false),
        ("mut-shadow", include_str!("../../../reports/mutable-shadowing-2026-11-13/fixtures/mut-shadow.lean"), false),
        ("ordinary-shadow", include_str!("../../../reports/mutable-shadowing-2026-11-13/fixtures/ordinary-shadow.lean"), true),
        ("mut-after-let", include_str!("../../../reports/mutable-shadowing-2026-11-13/fixtures/mut-after-let.lean"), true),
        ("nested-do-shadow", include_str!("../../../reports/mutable-shadowing-2026-11-13/fixtures/nested-do-shadow.lean"), true),
        ("branch-shadow", include_str!("../../../reports/mutable-shadowing-2026-11-13/fixtures/branch-shadow.lean"), false),
        ("different-have", include_str!("../../../reports/mutable-shadowing-2026-11-13/fixtures/different-have.lean"), true),
        ("for-binder", include_str!("../../../reports/mutable-shadowing-2026-11-13/fixtures/for-binder.lean"), false),
        ("match-binder", include_str!("../../../reports/mutable-shadowing-2026-11-13/fixtures/match-binder.lean"), false),
        ("if-let-binder", include_str!("../../../reports/mutable-shadowing-2026-11-13/fixtures/if-let-binder.lean"), false),
        ("branch-local-mut", include_str!("../../../reports/mutable-shadowing-2026-11-13/fixtures/branch-local-mut.lean"), true),
        ("have-before-mut", include_str!("../../../reports/mutable-shadowing-2026-11-13/fixtures/have-before-mut.lean"), true),
        ("term-lambda", include_str!("../../../reports/mutable-shadowing-2026-11-13/fixtures/term-lambda.lean"), true),
        ("bind-shadow", include_str!("../../../reports/mutable-shadowing-2026-11-13/fixtures/bind-shadow.lean"), false),
        ("witness-shadow", include_str!("../../../reports/mutable-shadowing-2026-11-13/fixtures/witness-shadow.lean"), true),
        ("reassignment-computes", include_str!("../../../reports/mutable-shadowing-2026-11-13/fixtures/reassignment-computes.lean"), true),
        ("anonymous-bindings", include_str!("../../../reports/mutable-shadowing-2026-11-13/fixtures/anonymous-bindings.lean"), true),
        ("quoted-underscore-shadow", include_str!("../../../reports/mutable-shadowing-2026-11-13/fixtures/quoted-underscore-shadow.lean"), false),
        ("anonymous-over-quoted", include_str!("../../../reports/mutable-shadowing-2026-11-13/fixtures/anonymous-over-quoted.lean"), true),
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
        context.set_main_module(Name::from_string("MutableShadowing"));
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
    }
    assert!(mismatches.is_empty(), "{}", mismatches.join("\n"));
}
