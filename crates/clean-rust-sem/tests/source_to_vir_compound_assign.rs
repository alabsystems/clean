// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_rust_sem::vir::{BinOp as VirBinOp, Constant, Term};
use clean_rust_sem::{Body, NllResult, Operand, Place, Rvalue, SourceProgram, Stmt};

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

fn borrow_result_for_main(source: &str) -> NllResult {
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

fn call_count(body: &Body, fn_name: &str) -> usize {
    body.blocks
        .iter()
        .filter(|bb| {
            matches!(
                &bb.terminator,
                Term::Call {
                    func: Operand::Constant(Constant::FnDef { name, .. }),
                    ..
                } if name == fn_name
            )
        })
        .count()
}

#[test]
fn test_compound_assign_local_lowers_to_in_place_binary_op() {
    let source = r#"
        fn main() -> u32 {
            let mut x: u32 = 1u32;
            x += 2u32;
            x
        }
    "#;

    let body = lowered_main(source);
    let x_local = local_id(&body, "x");
    let compound_assign = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .find(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    place: Place::Local(dst),
                    rvalue: Rvalue::BinaryOp {
                        op: VirBinOp::Add,
                        lhs: Operand::Copy(Place::Local(src)),
                        rhs: Operand::Constant(Constant::Scalar(_)),
                    },
                } if *dst == x_local && *src == x_local
            )
        })
        .expect("compound assignment should lower into an in-place binary op");

    assert!(
        matches!(compound_assign, Stmt::Assign { .. }),
        "compound assignment should keep the place on both sides: {compound_assign:?}"
    );

    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "local compound assignment should stay NLL-clean: {:?}",
        result.errors
    );
}

#[test]
fn test_compound_assign_index_target_evaluates_target_once() {
    let source = r#"
        fn next_idx(counter: &mut usize) -> usize {
            let current: usize = *counter;
            *counter += 1usize;
            current
        }

        fn main() -> u32 {
            let mut idx: usize = 0usize;
            let mut arr: [u32; 3] = [1u32, 2u32, 3u32];
            arr[next_idx(&mut idx)] += 4u32;
            idx as u32
        }
    "#;

    let body = lowered_main(source);
    assert_eq!(
        call_count(&body, "next_idx"),
        1,
        "compound-assignment index target should evaluate its call-based index once"
    );

    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "compound-assignment index lowering should stay NLL-clean: {:?}",
        result.errors
    );
}
