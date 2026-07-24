// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for block-local type items flowing through source-to-VIR lowering.

use clean_rust_sem::vir::Term;
use clean_rust_sem::{Body, Operand, Place, Rvalue, SourceProgram, Stmt};

fn lowered_main(source: &str) -> Body {
    let program = SourceProgram::parse(source).expect("source should parse");
    program
        .lower_to_vir()
        .expect("source should lower to VIR")
        .functions
        .get("main")
        .cloned()
        .expect("lowered program should contain `main`")
}

fn borrow_result_for_main(source: &str) -> clean_rust_sem::NllResult {
    let program = SourceProgram::parse(source).expect("source should parse");
    let mut analyses = program
        .check_borrows()
        .expect("source should lower and run NLL");
    analyses
        .remove("main")
        .expect("borrow analyses should contain `main`")
}

fn local_id(body: &Body, name: &str) -> u32 {
    body.locals
        .iter()
        .enumerate()
        .find_map(|(idx, decl)| (decl.name.as_deref() == Some(name)).then_some(idx as u32))
        .expect("named local should exist")
}

#[test]
fn test_block_local_tuple_struct_pattern_match_lowers() {
    let source = r#"
        fn main() -> u32 {
            struct Point(u32, u32);
            let p = Point(10u32, 32u32);
            match p {
                Point(x, y) => x + y,
            }
        }
    "#;

    let body = lowered_main(source);
    let x_local = local_id(&body, "x");
    let y_local = local_id(&body, "y");

    let x_assign = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .find(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    place: Place::Local(dst),
                    rvalue: Rvalue::Use(Operand::Copy(Place::Field { base, field })),
                } if *dst == x_local
                    && field == "0"
                    && matches!(base.as_ref(), Place::Local(_))
            )
        });
    let y_assign = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .find(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    place: Place::Local(dst),
                    rvalue: Rvalue::Use(Operand::Copy(Place::Field { base, field })),
                } if *dst == y_local
                    && field == "1"
                    && matches!(base.as_ref(), Place::Local(_))
            )
        });

    assert!(
        x_assign.is_some() && y_assign.is_some(),
        "block-local tuple struct pattern should bind fields from the matched local: {body:#?}"
    );

    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "block-local tuple struct match should stay NLL-clean: {:?}",
        result.errors
    );
}

#[test]
fn test_block_local_enum_pattern_match_lowers() {
    let source = r#"
        fn main() -> u32 {
            enum Mode {
                Ready(u32),
                Done,
            }

            let mode = Mode::Ready(7u32);
            match mode {
                Mode::Ready(value) => value,
                Mode::Done => 0u32,
            }
        }
    "#;

    let body = lowered_main(source);
    let value_local = local_id(&body, "value");

    let has_discriminant_test =
        body.blocks
            .iter()
            .flat_map(|bb| bb.statements.iter())
            .any(|stmt| {
                matches!(
                    stmt,
                    Stmt::Assign {
                        rvalue: Rvalue::Discriminant(Place::Local(_)),
                        ..
                    }
                )
            });
    assert!(
        has_discriminant_test,
        "block-local enum match should test the scrutinee discriminant"
    );

    let has_payload_binding = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .any(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    place: Place::Local(dst),
                    rvalue: Rvalue::Use(
                        Operand::Copy(Place::Field { base, field })
                        | Operand::Move(Place::Field { base, field })
                    ),
                }
                if *dst == value_local
                    && field == "0"
                    && matches!(
                        base.as_ref(),
                        Place::Downcast { variant, .. }
                        if variant == "Ready"
                    )
            )
        });
    assert!(
        has_payload_binding,
        "block-local enum tuple pattern should bind through a downcast field projection: {body:#?}"
    );

    let has_switch = body
        .blocks
        .iter()
        .any(|bb| matches!(&bb.terminator, Term::SwitchInt { .. }));
    assert!(
        has_switch,
        "block-local enum match should emit a switch terminator"
    );

    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "block-local enum match should stay NLL-clean: {:?}",
        result.errors
    );
}
