// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for for-loop desugaring and union/raw-deref lowering to VIR.

use clean_rust_sem::vir::{AggregateKind, Constant, Term};
use clean_rust_sem::{Operand, Place, Rvalue, SourceProgram, Stmt, VirLoweringError};

fn lowered_main(source: &str) -> clean_rust_sem::Body {
    let program = SourceProgram::parse(source).expect("source should parse");
    program
        .lower_to_vir()
        .expect("source should lower to VIR")
        .functions
        .get("main")
        .cloned()
        .expect("lowered program should contain `main`")
}

fn local_id(body: &clean_rust_sem::Body, name: &str) -> u32 {
    body.locals
        .iter()
        .enumerate()
        .find_map(|(idx, decl)| (decl.name.as_deref() == Some(name)).then_some(idx as u32))
        .expect("named local should exist")
}

#[test]
fn test_for_loop_over_range_lowers_to_iterator_protocol_cfg() {
    let source = r#"
        fn main() -> u32 {
            let mut sum: u32 = 0u32;
            for i in 0u32..3u32 {
                sum = sum + i;
            }
            sum
        }
    "#;

    let body = lowered_main(source);

    // For-loop desugaring creates: entry, header, call-cont, body, exit, break-exit, merge.
    assert!(
        body.blocks.len() >= 6,
        "for-loop desugaring should produce multiple CFG blocks, got {}",
        body.blocks.len()
    );

    // Should contain a Term::Call to Iterator::next.
    let has_next_call = body.blocks.iter().any(|bb| {
        matches!(
            &bb.terminator,
            Term::Call {
                func: Operand::Constant(Constant::FnDef { name, .. }),
                ..
            } if name == "Iterator::next"
        )
    });
    assert!(
        has_next_call,
        "for-loop desugaring should emit a call to Iterator::next"
    );

    // Should contain a SwitchInt on the Option discriminant.
    let has_switch = body
        .blocks
        .iter()
        .any(|bb| matches!(&bb.terminator, Term::SwitchInt { .. }));
    assert!(
        has_switch,
        "for-loop desugaring should switch on the Option discriminant"
    );
}

#[test]
fn test_for_loop_break_exits_loop() {
    let source = r#"
        fn main() -> u32 {
            let mut count: u32 = 0u32;
            for i in 0u32..10u32 {
                if i == 3u32 {
                    break;
                }
                count = count + 1u32;
            }
            count
        }
    "#;

    let body = lowered_main(source);
    assert!(
        body.blocks.len() >= 8,
        "for-loop with break should produce enough blocks, got {}",
        body.blocks.len()
    );
}

#[test]
fn test_union_init_lowers_to_adt_aggregate() {
    let source = r#"
        union MyUnion { i: u32, f: u32 }
        fn main() -> u32 {
            let u = MyUnion { i: 42u32 };
            0u32
        }
    "#;

    let body = lowered_main(source);
    let u_local = local_id(&body, "u");
    let has_adt_aggregate = body.blocks.iter().any(|bb| {
        bb.statements.iter().any(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    place: Place::Local(dst),
                    rvalue: Rvalue::Aggregate {
                        kind: AggregateKind::Adt { name, variant_index: 0 },
                        operands,
                    },
                } if *dst == u_local && name == "MyUnion" && operands.len() == 1
            )
        })
    });
    assert!(
        has_adt_aggregate,
        "union init should lower to Adt aggregate with a single operand"
    );
}

#[test]
fn test_for_loop_over_non_iterable_struct_fails_closed() {
    let source = r#"
        struct Foo {}
        fn main() {
            let f = Foo {};
            for x in f {
            }
        }
    "#;
    let program = SourceProgram::parse(source).expect("source should parse");
    let result = program.lower_to_vir();
    assert!(
        result.is_err(),
        "for-loop over non-iterable struct should fail closed, not silently use Unit"
    );
    let err = result.unwrap_err();
    assert!(
        matches!(err, VirLoweringError::MissingType { .. }),
        "error should be MissingType for unrecognized iterator element type, got: {err:?}"
    );
}
