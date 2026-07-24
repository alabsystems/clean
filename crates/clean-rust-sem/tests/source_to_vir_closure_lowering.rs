// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for closure expression lowering to VIR.

use clean_rust_sem::vir::{AggregateKind, BorrowKind};
use clean_rust_sem::{Body, LoweredProgram, Operand, Place, Rvalue, SourceProgram, Stmt};

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

fn lowered_program(source: &str) -> LoweredProgram {
    let program = SourceProgram::parse(source).expect("source should parse");
    program.lower_to_vir().expect("source should lower to VIR")
}

fn local_id(body: &Body, name: &str) -> u32 {
    body.locals
        .iter()
        .enumerate()
        .find_map(|(idx, decl)| (decl.name.as_deref() == Some(name)).then_some(idx as u32))
        .expect("named local should exist")
}

#[test]
fn test_closure_no_captures_lowers_to_closure_aggregate() {
    let source = r#"
        fn main() -> u32 {
            let f = |x: u32| -> u32 { x + 1u32 };
            0u32
        }
    "#;

    let lowered = lowered_program(source);
    let body = lowered
        .functions
        .get("main")
        .expect("lowered program should contain `main`");

    // The closure construction should produce an AggregateKind::Closure
    let closure_assign = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .find(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    rvalue: Rvalue::Aggregate {
                        kind: AggregateKind::Closure { .. },
                        ..
                    },
                    ..
                }
            )
        })
        .expect("closure expression should lower through AggregateKind::Closure");

    // No captures → empty operands list
    match closure_assign {
        Stmt::Assign {
            rvalue:
                Rvalue::Aggregate {
                    kind: AggregateKind::Closure { def_id },
                    operands,
                },
            ..
        } => {
            assert!(
                def_id.contains("{closure#"),
                "closure def_id should include {{closure#N}}: {def_id}"
            );
            assert!(
                operands.is_empty(),
                "closure with no captures should have empty operands: {operands:?}"
            );
        }
        _ => panic!("expected closure aggregate"),
    }

    // The closure body should be registered as a separate function
    let closure_fn = lowered
        .functions
        .keys()
        .find(|k| k.contains("{closure#"))
        .expect("closure body should be registered as a separate function in LoweredProgram");
    let closure_body = &lowered.functions[closure_fn];
    assert!(
        closure_body.arg_count == 1,
        "closure with one param and no captures should have arg_count=1, got {}",
        closure_body.arg_count
    );
}

#[test]
fn test_closure_with_capture_emits_borrow_operand() {
    let source = r#"
        fn main() -> u32 {
            let y: u32 = 5u32;
            let f = |x: u32| -> u32 { x + y };
            0u32
        }
    "#;

    let lowered = lowered_program(source);
    let body = lowered
        .functions
        .get("main")
        .expect("lowered program should contain `main`");

    // Closure construction should capture `y`
    let closure_assign = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .find_map(|stmt| match stmt {
            Stmt::Assign {
                rvalue:
                    Rvalue::Aggregate {
                        kind: AggregateKind::Closure { def_id },
                        operands,
                    },
                ..
            } => Some((def_id.clone(), operands.clone())),
            _ => None,
        })
        .expect("closure expression should lower through AggregateKind::Closure");

    let (def_id, operands) = closure_assign;
    assert_eq!(
        operands.len(),
        1,
        "closure capturing one variable should have one operand: {operands:?}"
    );

    // Borrow closure: the capture operand should be a Move of a Ref temp
    assert!(
        matches!(&operands[0], Operand::Move(Place::Local(_))),
        "borrow-closure capture should be a Move of a Ref temp, got: {:?}",
        operands[0]
    );

    // The closure body should have 2 params: capture `y` + explicit `x`
    let closure_body = &lowered.functions[&def_id];
    assert_eq!(
        closure_body.arg_count, 2,
        "closure with one capture and one param should have arg_count=2, got {}",
        closure_body.arg_count
    );
}

#[test]
fn test_move_closure_captures_by_value() {
    let source = r#"
        fn main() -> u32 {
            let y: u32 = 5u32;
            let f = move |x: u32| -> u32 { x + y };
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
                        kind: AggregateKind::Closure { def_id },
                        operands,
                    },
                ..
            } => Some((def_id.clone(), operands.clone())),
            _ => None,
        })
        .expect("move closure expression should lower through AggregateKind::Closure");

    assert_eq!(
        operands.len(),
        1,
        "move closure should have one capture operand"
    );

    // Move/Copy closure: u32 is Copy, so should be Operand::Copy
    assert!(
        matches!(&operands[0], Operand::Copy(Place::Local(_))),
        "move closure capturing a Copy type should use Operand::Copy, got: {:?}",
        operands[0]
    );
}

#[test]
fn test_borrow_closure_emits_ref_for_capture() {
    let source = r#"
        fn main() -> u32 {
            let y: u32 = 5u32;
            let f = |x: u32| -> u32 { x + y };
            0u32
        }
    "#;

    let body = lowered_main(source);

    // Should find a Ref statement for the capture before the Closure aggregate
    let has_closure_ref = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .any(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    rvalue: Rvalue::Ref {
                        borrow_kind: BorrowKind::Shared,
                        ..
                    },
                    ..
                }
            )
        });

    assert!(
        has_closure_ref,
        "borrow closure should emit a Ref statement for the captured variable"
    );
}

#[test]
fn test_closure_body_sees_block_local_tuple_struct_symbols() {
    let source = r#"
        fn main() -> u32 {
            struct Point(u32, u32);
            let f = |x: u32| -> u32 {
                let p = Point(x, 1u32);
                let first = p.0;
                let second = p.1;
                0u32
            };
            0u32
        }
    "#;

    let lowered = lowered_program(source);
    let (closure_name, closure_body) = lowered
        .functions
        .iter()
        .find(|(name, _)| name.contains("{closure#"))
        .expect("closure body should be registered as a separate function");
    let p_local = local_id(closure_body, "p");
    let first_local = local_id(closure_body, "first");
    let second_local = local_id(closure_body, "second");

    let has_field_binds = closure_body
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
                if ((*dst == first_local && field == "0")
                    || (*dst == second_local && field == "1"))
                    && matches!(base.as_ref(), Place::Local(local) if *local == p_local)
            )
        });
    assert!(
        has_field_binds,
        "closure body should project block-local tuple-struct fields through the local `p`: {closure_body:#?}"
    );

    let borrow_results = lowered.check_borrows();
    let closure_result = borrow_results
        .get(closure_name)
        .expect("borrow analyses should include the lowered closure body");
    assert!(
        closure_result.errors.is_empty(),
        "closure body using a block-local tuple struct should stay NLL-clean: {:?}",
        closure_result.errors
    );
}

#[test]
fn test_closure_block_tail_can_use_block_local_binding() {
    let source = r#"
        fn main() -> u32 {
            let f = |x: u32| {
                let y = x + 1u32;
                y
            };
            0u32
        }
    "#;

    let lowered = lowered_program(source);
    let (closure_name, closure_body) = lowered
        .functions
        .iter()
        .find(|(name, _)| name.contains("{closure#"))
        .expect("closure body should be registered as a separate function");
    let y_local = local_id(closure_body, "y");

    let has_y_assignment = closure_body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .any(
            |stmt| matches!(stmt, Stmt::Assign { place: Place::Local(dst), .. } if *dst == y_local),
        );
    assert!(
        has_y_assignment,
        "closure body should lower the block-local `y` binding before returning it: {closure_body:#?}"
    );

    let borrow_results = lowered.check_borrows();
    let closure_result = borrow_results
        .get(closure_name)
        .expect("borrow analyses should include the lowered closure body");
    assert!(
        closure_result.errors.is_empty(),
        "closure body returning a block-local binding should stay NLL-clean: {:?}",
        closure_result.errors
    );
}

#[test]
fn test_closure_block_tail_can_use_block_local_tuple_struct() {
    let source = r#"
        fn main() -> u32 {
            let f = |x: u32| {
                struct Pair(u32, u32);
                let pair = Pair(x, 1u32);
                pair.0 + pair.1
            };
            0u32
        }
    "#;

    let lowered = lowered_program(source);
    let (closure_name, closure_body) = lowered
        .functions
        .iter()
        .find(|(name, _)| name.contains("{closure#"))
        .expect("closure body should be registered as a separate function");
    let pair_local = local_id(closure_body, "pair");

    let has_pair_projection = closure_body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .any(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    place: Place::Local(0),
                    rvalue: Rvalue::BinaryOp { lhs, rhs, .. },
                    ..
                } if matches!(
                    lhs,
                    Operand::Copy(Place::Field { base, field })
                    | Operand::Move(Place::Field { base, field })
                    if matches!(base.as_ref(), Place::Local(local) if *local == pair_local)
                        && field == "0"
                ) && matches!(
                    rhs,
                    Operand::Copy(Place::Field { base, field })
                    | Operand::Move(Place::Field { base, field })
                    if matches!(base.as_ref(), Place::Local(local) if *local == pair_local)
                        && field == "1"
                )
            )
        });
    assert!(
        has_pair_projection,
        "closure tail should project fields from the block-local tuple struct binding: {closure_body:#?}"
    );

    let borrow_results = lowered.check_borrows();
    let closure_result = borrow_results
        .get(closure_name)
        .expect("borrow analyses should include the lowered closure body");
    assert!(
        closure_result.errors.is_empty(),
        "closure tail using a block-local tuple struct should stay NLL-clean: {:?}",
        closure_result.errors
    );
}

#[test]
fn test_closure_block_tail_can_use_block_local_enum() {
    let source = r#"
        fn main() -> u32 {
            let f = || {
                enum Mode {
                    Ready(u32),
                    Done,
                }

                let mode = Mode::Ready(7u32);
                match mode {
                    Mode::Ready(value) => value,
                    Mode::Done => 0u32,
                }
            };
            0u32
        }
    "#;

    let lowered = lowered_program(source);
    let (closure_name, closure_body) = lowered
        .functions
        .iter()
        .find(|(name, _)| name.contains("{closure#"))
        .expect("closure body should be registered as a separate function");
    let value_local = local_id(closure_body, "value");

    let has_discriminant_test = closure_body
        .blocks
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
        "closure tail using a block-local enum should test the scrutinee discriminant"
    );

    let has_payload_binding = closure_body
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
        "closure tail should bind the block-local enum payload through a downcast field projection: {closure_body:#?}"
    );

    let borrow_results = lowered.check_borrows();
    let closure_result = borrow_results
        .get(closure_name)
        .expect("borrow analyses should include the lowered closure body");
    assert!(
        closure_result.errors.is_empty(),
        "closure tail using a block-local enum should stay NLL-clean: {:?}",
        closure_result.errors
    );
}

#[test]
fn test_closure_call_lowers_through_local_operand() {
    let source = r#"
        fn main() -> u32 {
            let f = |x: u32| -> u32 { x + 1u32 };
            let result: u32 = f(5u32);
            result
        }
    "#;

    let body = lowered_main(source);
    let f_local = local_id(&body, "f");
    let result_local = local_id(&body, "result");

    // The call terminator should use a Move of the closure local, not a
    // Constant::FnDef, because `f` is a local variable holding a closure.
    let has_closure_call = body.blocks.iter().any(|bb| {
        matches!(
            &bb.terminator,
            clean_rust_sem::vir::Term::Call {
                func: Operand::Move(Place::Local(func_local)),
                destination: Place::Local(dest),
                ..
            } if *func_local == f_local && *dest == result_local
        )
    });
    assert!(
        has_closure_call,
        "calling a closure variable should emit Term::Call with \
         Operand::Move of the closure local, not Constant::FnDef: {body:#?}"
    );
}

#[test]
fn test_closure_call_with_capture_runs_nll_clean() {
    let source = r#"
        fn main() -> u32 {
            let y: u32 = 10u32;
            let f = |x: u32| -> u32 { x + y };
            let result: u32 = f(5u32);
            result
        }
    "#;

    let lowered = lowered_program(source);
    let _body = lowered
        .functions
        .get("main")
        .expect("lowered program should contain `main`");

    // The closure call should lower and pass NLL without errors.
    let borrow_results = lowered.check_borrows();
    let main_result = borrow_results
        .get("main")
        .expect("borrow analyses should include `main`");
    assert!(
        main_result.errors.is_empty(),
        "calling a closure that captures a shared variable should stay NLL-clean: {:?}",
        main_result.errors
    );
}

#[test]
fn test_move_closure_call_result_type_correct() {
    let source = r#"
        fn main() -> u32 {
            let y: u32 = 3u32;
            let f = move |x: u32| -> u32 { x + y };
            let result: u32 = f(7u32);
            result
        }
    "#;

    let body = lowered_main(source);
    let result_local = local_id(&body, "result");

    // Verify that the result local has the correct type (u32).
    let result_ty = &body.locals[result_local as usize].ty;
    assert_eq!(
        *result_ty,
        clean_rust_sem::RustType::Uint(clean_rust_sem::UintType::U32),
        "closure call result should have the closure's return type"
    );
}
