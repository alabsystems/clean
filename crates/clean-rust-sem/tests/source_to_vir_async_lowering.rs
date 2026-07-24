// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for async/await expression lowering to VIR.

use clean_rust_sem::vir::{AggregateKind, Constant};
use clean_rust_sem::{
    LoweredProgram, Operand, Place, RustType, Rvalue, SourceProgram, Stmt, Term, UintType,
};

fn lowered_program(source: &str) -> LoweredProgram {
    let program = SourceProgram::parse(source).expect("source should parse");
    program.lower_to_vir().expect("source should lower to VIR")
}

#[test]
fn test_async_block_lowers_to_generator_aggregate() {
    let source = r#"
        fn main() -> u32 {
            let f = async { 42u32 };
            0u32
        }
    "#;

    let lowered = lowered_program(source);
    let body = lowered
        .functions
        .get("main")
        .expect("lowered program should contain `main`");

    // The async block should produce an AggregateKind::Generator
    let generator_assign = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .find_map(|stmt| match stmt {
            Stmt::Assign {
                rvalue:
                    Rvalue::Aggregate {
                        kind: AggregateKind::Generator { def_id },
                        operands,
                    },
                ..
            } => Some((def_id.clone(), operands.clone())),
            _ => None,
        })
        .expect("async block should lower through AggregateKind::Generator");

    let (def_id, operands) = generator_assign;
    assert!(
        def_id.contains("{async#"),
        "generator def_id should include {{async#N}}: {def_id}"
    );
    assert!(
        operands.is_empty(),
        "async block with no captures should have empty operands: {operands:?}"
    );

    // The generator body should be registered as a separate function
    let gen_fn = lowered
        .functions
        .keys()
        .find(|k| k.contains("{async#"))
        .expect("generator body should be registered as a separate function in LoweredProgram");
    let gen_body = &lowered.functions[gen_fn];
    assert_eq!(
        gen_body.arg_count, 0,
        "async block with no captures should have arg_count=0, got {}",
        gen_body.arg_count
    );
}

#[test]
fn test_async_move_block_captures_by_value() {
    let source = r#"
        fn main() -> u32 {
            let x: u32 = 5u32;
            let f = async move { x };
            0u32
        }
    "#;

    let lowered = lowered_program(source);
    let body = lowered
        .functions
        .get("main")
        .expect("lowered program should contain `main`");

    let (def_id, operands) = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .find_map(|stmt| match stmt {
            Stmt::Assign {
                rvalue:
                    Rvalue::Aggregate {
                        kind: AggregateKind::Generator { def_id },
                        operands,
                    },
                ..
            } => Some((def_id.clone(), operands.clone())),
            _ => None,
        })
        .expect("async move block should lower through AggregateKind::Generator");

    assert_eq!(
        operands.len(),
        1,
        "async move block capturing one variable should have one operand: {operands:?}"
    );

    // u32 is Copy, so capture should use Operand::Copy
    assert!(
        matches!(&operands[0], Operand::Copy(Place::Local(_))),
        "async move capturing a Copy type should use Operand::Copy, got: {:?}",
        operands[0]
    );

    // The generator body should have 1 param (the capture)
    let gen_body = &lowered.functions[&def_id];
    assert_eq!(
        gen_body.arg_count, 1,
        "async move block with one capture should have arg_count=1, got {}",
        gen_body.arg_count
    );
}

#[test]
fn test_await_lowers_to_call_terminator() {
    let source = r#"
        fn main() -> u32 {
            let f = async { 42u32 };
            let result: u32 = f.await;
            result
        }
    "#;

    let lowered = lowered_program(source);
    let body = lowered
        .functions
        .get("main")
        .expect("lowered program should contain `main`");

    // The `.await` should produce a Term::Call terminator
    let has_call = body
        .blocks
        .iter()
        .any(|bb| matches!(&bb.terminator, Term::Call { .. }));
    assert!(
        has_call,
        "`.await` expression should lower to a Term::Call terminator: {body:#?}"
    );
}

#[test]
fn test_async_fn_lowers_successfully() {
    let source = r#"
        async fn compute() -> u32 {
            42u32
        }

        fn main() -> u32 {
            0u32
        }
    "#;

    let lowered = lowered_program(source);
    assert!(
        lowered.functions.contains_key("compute"),
        "async function should be lowered into the program: {:?}",
        lowered.functions.keys().collect::<Vec<_>>()
    );
}

#[test]
fn test_await_uses_future_local_for_capturing_async_block() {
    let source = r#"
        fn main() -> u32 {
            let x: u32 = 10u32;
            let f = async { x };
            let result: u32 = f.await;
            result
        }
    "#;

    let lowered = lowered_program(source);
    let body = lowered
        .functions
        .get("main")
        .expect("lowered program should contain `main`");

    let has_future_local_call = body.blocks.iter().any(|bb| {
        matches!(
            &bb.terminator,
            Term::Call {
                func: Operand::Move(Place::Local(_)),
                ..
            }
        )
    });
    assert!(
        has_future_local_call,
        "await should call the future local so captures stay attached: {body:#?}"
    );

    let has_direct_generator_call = body.blocks.iter().any(|bb| {
        matches!(
            &bb.terminator,
            Term::Call {
                func: Operand::Constant(Constant::FnDef { name, .. }),
                ..
            } if name.contains("{async#")
        )
    });
    assert!(
        !has_direct_generator_call,
        "await should not bypass the future value and call the generator body directly: {body:#?}"
    );
}

#[test]
fn test_async_fn_call_lowers_to_future_producer_and_await() {
    let source = r#"
        async fn compute(x: u32) -> u32 {
            x + 1u32
        }

        fn main() -> u32 {
            compute(4u32).await
        }
    "#;

    let lowered = lowered_program(source);
    let compute_body = lowered
        .functions
        .get("compute")
        .expect("lowered program should contain `compute`");
    let has_generator_aggregate = compute_body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .any(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    rvalue: Rvalue::Aggregate {
                        kind: AggregateKind::Generator { .. },
                        ..
                    },
                    ..
                }
            )
        });
    assert!(
        has_generator_aggregate,
        "async fn should lower to a future-producing wrapper body: {compute_body:#?}"
    );
    assert!(
        lowered
            .functions
            .keys()
            .any(|name| name.starts_with("compute::{async#")),
        "async fn lowering should register the nested generator body: {:?}",
        lowered.functions.keys().collect::<Vec<_>>()
    );

    let main_body = lowered
        .functions
        .get("main")
        .expect("lowered program should contain `main`");
    let has_async_fn_call = main_body.blocks.iter().any(|bb| {
        matches!(
            &bb.terminator,
            Term::Call {
                func: Operand::Constant(Constant::FnDef { name, .. }),
                ..
            } if name == "compute"
        )
    });
    let has_await_call = main_body.blocks.iter().any(|bb| {
        matches!(
            &bb.terminator,
            Term::Call {
                func: Operand::Move(Place::Local(_)),
                ..
            }
        )
    });
    assert!(
        has_async_fn_call && has_await_call,
        "async fn await should first call the function and then await the returned future: {main_body:#?}"
    );
}

#[test]
fn test_await_infers_output_for_direct_async_fn_calls() {
    let source = r#"
        async fn compute(x: u32) -> u32 {
            x + 1u32
        }

        fn main() -> u32 {
            let total = compute(4u32).await + compute(5u32).await;
            total
        }
    "#;

    let lowered = lowered_program(source);
    let body = lowered
        .functions
        .get("main")
        .expect("lowered program should contain `main`");

    let total_local = body
        .locals
        .iter()
        .find(|local| local.name.as_deref() == Some("total"))
        .expect("lowered body should declare `total`");
    assert_eq!(
        total_local.ty,
        RustType::Uint(UintType::U32),
        "direct async fn await should infer `u32`, got {:?}",
        total_local.ty
    );
}

#[test]
fn test_await_infers_output_for_named_future_local() {
    let source = r#"
        async fn compute(x: u32) -> u32 {
            x + 1u32
        }

        fn main() -> u32 {
            let future = compute(4u32);
            let result = future.await;
            result + result
        }
    "#;

    let lowered = lowered_program(source);
    let body = lowered
        .functions
        .get("main")
        .expect("lowered program should contain `main`");

    let (result_local, result_decl) = body
        .locals
        .iter()
        .enumerate()
        .find(|(_, local)| local.name.as_deref() == Some("result"))
        .expect("lowered body should declare `result`");
    assert_eq!(
        result_decl.ty,
        RustType::Uint(UintType::U32),
        "awaiting a named future should infer `u32`, got {:?}",
        result_decl.ty
    );

    let has_copying_add = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .any(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    rvalue: Rvalue::BinaryOp {
                        lhs: Operand::Copy(Place::Local(lhs)),
                        rhs: Operand::Copy(Place::Local(rhs)),
                        ..
                    },
                    ..
                } if *lhs as usize == result_local && *rhs as usize == result_local
            )
        });
    assert!(
        has_copying_add,
        "await result should be treated as a copyable `u32`: {body:#?}"
    );
}

#[test]
fn test_async_block_borrow_capture() {
    let source = r#"
        fn main() -> u32 {
            let x: u32 = 10u32;
            let f = async { x };
            0u32
        }
    "#;

    let lowered = lowered_program(source);
    let body = lowered
        .functions
        .get("main")
        .expect("lowered program should contain `main`");

    let (_, operands) = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .find_map(|stmt| match stmt {
            Stmt::Assign {
                rvalue:
                    Rvalue::Aggregate {
                        kind: AggregateKind::Generator { def_id },
                        operands,
                    },
                ..
            } => Some((def_id.clone(), operands.clone())),
            _ => None,
        })
        .expect("async block should lower through AggregateKind::Generator");

    // Non-move async block captures by reference
    assert_eq!(
        operands.len(),
        1,
        "async block capturing `x` should have one operand: {operands:?}"
    );
    // Borrow capture: the operand should be a Move of a Ref temp
    assert!(
        matches!(&operands[0], Operand::Move(Place::Local(_))),
        "borrow-capture async block should use Move of a Ref temp, got: {:?}",
        operands[0]
    );
}
