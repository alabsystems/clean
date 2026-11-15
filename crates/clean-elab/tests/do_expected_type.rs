// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Lean4.35 monadic expected-type and required Pure controls.
use clean_elab::module_driver::{module_environment, EnvironmentSetup};
use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::Name;
use clean_parser::parse_file_with_diagnostics;

fn failed(result: &ElabResult) -> bool {
    match result {
        ElabResult::Failed { .. } => true,
        ElabResult::Multiple(results) => results.iter().any(failed),
        _ => false,
    }
}

#[test]
fn supported_do_expected_types_match_frozen_oracle() {
    // ReaderT is absent from the baseline source environment; its oracle
    // fixture stays in the paired CLI cohort as a separate Init coverage gap.
    let cases = [
        (
            "historical-770",
            include_str!(
                "../../../reports/do-expected-type-2026-11-13/fixtures/historical-770.lean"
            ),
            false,
        ),
        (
            "id-result",
            include_str!("../../../reports/do-expected-type-2026-11-13/fixtures/id-result.lean"),
            true,
        ),
        (
            "nat-return",
            include_str!("../../../reports/do-expected-type-2026-11-13/fixtures/nat-return.lean"),
            false,
        ),
        (
            "nat-terminal",
            include_str!("../../../reports/do-expected-type-2026-11-13/fixtures/nat-terminal.lean"),
            false,
        ),
        (
            "id-alias",
            include_str!("../../../reports/do-expected-type-2026-11-13/fixtures/id-alias.lean"),
            true,
        ),
        (
            "nat-alias",
            include_str!("../../../reports/do-expected-type-2026-11-13/fixtures/nat-alias.lean"),
            false,
        ),
        (
            "inferred-io",
            include_str!("../../../reports/do-expected-type-2026-11-13/fixtures/inferred-io.lean"),
            true,
        ),
        (
            "prop-result",
            include_str!("../../../reports/do-expected-type-2026-11-13/fixtures/prop-result.lean"),
            false,
        ),
        (
            "prop-application",
            include_str!(
                "../../../reports/do-expected-type-2026-11-13/fixtures/prop-application.lean"
            ),
            false,
        ),
        (
            "inferred-numeral",
            include_str!(
                "../../../reports/do-expected-type-2026-11-13/fixtures/inferred-numeral.lean"
            ),
            false,
        ),
        (
            "inferred-pure",
            include_str!(
                "../../../reports/do-expected-type-2026-11-13/fixtures/inferred-pure.lean"
            ),
            false,
        ),
        (
            "function-result",
            include_str!(
                "../../../reports/do-expected-type-2026-11-13/fixtures/function-result.lean"
            ),
            false,
        ),
        (
            "constant-functor",
            include_str!(
                "../../../reports/do-expected-type-2026-11-13/fixtures/constant-functor.lean"
            ),
            false,
        ),
        (
            "pure-only-return",
            include_str!(
                "../../../reports/do-expected-type-2026-11-13/fixtures/pure-only-return.lean"
            ),
            true,
        ),
        (
            "no-classes-terminal",
            include_str!(
                "../../../reports/do-expected-type-2026-11-13/fixtures/no-classes-terminal.lean"
            ),
            false,
        ),
        (
            "pure-only-terminal",
            include_str!(
                "../../../reports/do-expected-type-2026-11-13/fixtures/pure-only-terminal.lean"
            ),
            true,
        ),
        (
            "result-type-alias",
            include_str!(
                "../../../reports/do-expected-type-2026-11-13/fixtures/result-type-alias.lean"
            ),
            true,
        ),
        (
            "term-let-type",
            include_str!(
                "../../../reports/do-expected-type-2026-11-13/fixtures/term-let-type.lean"
            ),
            true,
        ),
        (
            "id-run-pure",
            include_str!("../../../reports/do-expected-type-2026-11-13/fixtures/id-run-pure.lean"),
            true,
        ),
    ];
    let mut mismatches = Vec::new();
    for (name, source, accepted) in cases {
        let parsed = parse_file_with_diagnostics(source).expect("frozen fixture parses");
        assert!(
            parsed.diagnostics.is_empty(),
            "{name}: {:?}",
            parsed.diagnostics
        );
        let mut env =
            module_environment(EnvironmentSetup::default()).expect("production check environment");
        let mut context = FileContext::new();
        context.set_main_module(Name::from_string("DoExpectedType"));
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

#[test]
fn do_match_regressions_use_monadic_expected_type() {
    let source =
        include_str!("../../../reports/do-expected-type-2026-11-13/regressions/do-match.lean");
    let parsed = parse_file_with_diagnostics(source).expect("oracle fixture parses");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut env =
        module_environment(EnvironmentSetup::default()).expect("production check environment");
    let mut context = FileContext::new();
    context.set_main_module(Name::from_string("DoMatchExpectedType"));
    context.set_file_header(&parsed.header);
    for decl in parsed.decls {
        let decl = preprocess_decl_with_context(&decl, &mut context);
        let result = elaborate_decl_and_register_with_context(&mut env, &decl, &mut context)
            .expect("valid monadic match and its value pin elaborate");
        assert!(!failed(&result), "{result:?}");
    }
}
