// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for builtin `Option`/`Result` enum lowering to VIR.

use clean_rust_sem::vir::{AggregateKind, Term};
use clean_rust_sem::{Body, LoweredProgram, Rvalue, SourceProgram, Stmt};

/// Lower a snippet, panicking with the test name on failure. Wave 108
/// closed the `?` operator gap for both `Result` and `Option`; the
/// previous TRACE+return wrapper has been hard-asserted.
fn require_lowered_program(source: &str, test_name: &str) -> LoweredProgram {
    let program = SourceProgram::parse(source).expect("source should parse");
    program
        .lower_to_vir()
        .unwrap_or_else(|err| panic!("{test_name}: source should lower to VIR: {err:?}"))
}

fn function_body<'a>(lowered: &'a LoweredProgram, name: &str) -> &'a Body {
    lowered
        .functions
        .get(name)
        .unwrap_or_else(|| panic!("lowered program should contain `{name}`"))
}

fn assert_nll_clean(lowered: &LoweredProgram, name: &str) {
    let analyses = lowered.check_borrows();
    let result = analyses
        .get(name)
        .unwrap_or_else(|| panic!("borrow analyses should contain `{name}`"));
    assert!(
        result.errors.is_empty(),
        "`{name}` should stay NLL-clean after lowering: {:?}",
        result.errors
    );
}

#[test]
fn test_try_operator_result_lowers_through_builtin_result_variants() {
    let source = r#"
        fn get_value(r: Result<u32, u32>) -> Result<u32, u32> {
            let v: u32 = r?;
            Result::Ok(v)
        }

        fn main() -> u32 {
            let err: Result<u32, u32> = Result::Err(99u32);
            match get_value(err) {
                Result::Ok(_v) => 0u32,
                Result::Err(e) => e,
            }
        }
    "#;

    let lowered = require_lowered_program(
        source,
        "test_try_operator_result_lowers_through_builtin_result_variants",
    );
    let body = function_body(&lowered, "get_value");

    let has_discriminant_test =
        body.blocks
            .iter()
            .flat_map(|bb| bb.statements.iter())
            .any(|stmt| {
                matches!(
                    stmt,
                    Stmt::Assign {
                        rvalue: Rvalue::Discriminant(_),
                        ..
                    }
                )
            });
    assert!(
        has_discriminant_test,
        "`r?` should lower through a builtin-Result match discriminant test"
    );

    let has_ok_aggregate = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .any(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    rvalue: Rvalue::Aggregate {
                        kind: AggregateKind::Adt { name, variant_index },
                        operands,
                    },
                    ..
                } if name == "Result" && *variant_index == 0 && operands.len() == 1
            )
        });
    let has_err_aggregate = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .any(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    rvalue: Rvalue::Aggregate {
                        kind: AggregateKind::Adt { name, variant_index },
                        operands,
                    },
                    ..
                } if name == "Result" && *variant_index == 1 && operands.len() == 1
            )
        });

    assert!(
        has_ok_aggregate,
        "successful `Result::Ok` construction should lower through builtin Result metadata: {body:#?}"
    );
    assert!(
        has_err_aggregate,
        "the early-return `Result::Err` path from `?` should lower through builtin Result metadata: {body:#?}"
    );

    assert_nll_clean(&lowered, "get_value");
    assert_nll_clean(&lowered, "main");
}

#[test]
fn test_try_operator_option_lowers_through_builtin_option_variants() {
    let source = r#"
        fn extract(opt: Option<u32>) -> Option<u32> {
            let v: u32 = opt?;
            Option::Some(v)
        }

        fn main() -> u32 {
            let none: Option<u32> = Option::None;
            match extract(none) {
                Option::Some(_v) => 1u32,
                Option::None => 42u32,
            }
        }
    "#;

    let lowered = require_lowered_program(
        source,
        "test_try_operator_option_lowers_through_builtin_option_variants",
    );
    let body = function_body(&lowered, "extract");

    let switch_count = body
        .blocks
        .iter()
        .filter(|bb| matches!(bb.terminator, Term::SwitchInt { .. }))
        .count();
    assert!(
        switch_count >= 1,
        "`opt?` should lower through a builtin-Option match switch"
    );

    let has_some_aggregate = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .any(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    rvalue: Rvalue::Aggregate {
                        kind: AggregateKind::Adt { name, variant_index },
                        operands,
                    },
                    ..
                } if name == "Option" && *variant_index == 1 && operands.len() == 1
            )
        });
    let has_none_aggregate = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .any(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    rvalue: Rvalue::Aggregate {
                        kind: AggregateKind::Adt { name, variant_index },
                        operands,
                    },
                    ..
                } if name == "Option" && *variant_index == 0 && operands.is_empty()
            )
        });

    assert!(
        has_some_aggregate,
        "successful `Option::Some` construction should lower through builtin Option metadata: {body:#?}"
    );
    assert!(
        has_none_aggregate,
        "the early-return `Option::None` path from `?` should lower through builtin Option metadata: {body:#?}"
    );

    assert_nll_clean(&lowered, "extract");
    assert_nll_clean(&lowered, "main");
}

#[test]
fn test_match_arm_never_unifies_with_concrete_arm() {
    // Negative for Wave 108's Never-arm widening: ensure that a match
    // mixing a concrete arm with a diverging arm type-checks. Without
    // the widening, this previously failed with
    // `match arms must share a type, got Uint(U32) and Never`. With
    // the widening this lowers and the inferred match type is
    // `Uint(U32)`.
    let source = r#"
        fn classify(r: Result<u32, u32>) -> u32 {
            match r {
                Result::Ok(v) => v,
                Result::Err(e) => return e,
            }
        }

        fn main() -> u32 {
            classify(Result::Ok(7u32))
        }
    "#;
    require_lowered_program(source, "test_match_arm_never_unifies_with_concrete_arm");
}

#[test]
fn test_try_operator_on_non_result_option_still_errors() {
    // Negative: the `?` operator desugar emits arms for both
    // `Result` and `Option`. For a scrutinee whose type is neither
    // (e.g. a bare `u32`), the lowering must NOT silently invent a
    // match — the `nominal_type_name(u32)` lookup returns None, so
    // `builtin_try_pattern_compatible` keeps the arms; the
    // pattern-binding then fails because `u32` is not an enum.
    let source = r#"
        fn bad(x: u32) -> u32 {
            x?
        }
    "#;
    let program = SourceProgram::parse(source).expect("source should parse");
    let err = program
        .lower_to_vir()
        .expect_err("the `?` operator must not succeed on a non-Result/Option scrutinee");
    let detail = format!("{err:?}");
    assert!(
        detail.contains("enum") || detail.contains("pattern") || detail.contains("Unsupported"),
        "the failure must be a lowering error (enum/pattern/Unsupported): got {detail}"
    );
}
