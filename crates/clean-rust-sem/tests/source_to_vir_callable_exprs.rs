// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for callable-expression lowering to VIR.

use clean_rust_sem::vir::{BorrowKind, Constant, Term};
use clean_rust_sem::{Body, LoweredProgram, Operand, Place, RustType, Rvalue, SourceProgram};

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
fn test_function_item_binding_lowers_to_local_fn_operand_call() {
    let source = r#"
        fn add_one(x: u32) -> u32 { x + 1u32 }

        fn main() -> u32 {
            let f = add_one;
            let result = f(5u32);
            result
        }
    "#;

    let lowered = lowered_program(source);
    let body = lowered
        .functions
        .get("main")
        .expect("lowered program should contain `main`");
    let f_local = local_id(body, "f");
    let result_local = local_id(body, "result");

    let has_fn_item_assign = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .any(|stmt| {
            matches!(
                stmt,
                clean_rust_sem::Stmt::Assign {
                    place: Place::Local(dst),
                    rvalue: Rvalue::Use(Operand::Constant(Constant::FnDef { name, .. })),
                } if *dst == f_local && name == "add_one"
            )
        });
    assert!(
        has_fn_item_assign,
        "binding a function item should lower through Constant::FnDef into the local `f`: {body:#?}"
    );

    let has_local_callee_call = body.blocks.iter().any(|bb| {
        matches!(
            &bb.terminator,
            Term::Call {
                func: Operand::Copy(Place::Local(func_local)),
                destination: Place::Local(dest),
                ..
            } if *func_local == f_local && *dest == result_local
        )
    });
    assert!(
        has_local_callee_call,
        "calling a local fn value should use the local operand, not a synthetic FnDef lookup: {body:#?}"
    );

    assert!(
        lowered
            .check_borrows()
            .get("main")
            .expect("borrow analyses should include `main`")
            .errors
            .is_empty(),
        "local fn-value call should stay NLL-clean"
    );
}

#[test]
fn test_returned_callable_expression_materializes_temp_callee() {
    let source = r#"
        fn add_one(x: u32) -> u32 { x + 1u32 }

        fn chooser() -> fn(u32) -> u32 {
            add_one
        }

        fn main() -> u32 {
            let result = chooser()(41u32);
            result
        }
    "#;

    let lowered = lowered_program(source);
    let body = lowered
        .functions
        .get("main")
        .expect("lowered program should contain `main`");
    let result_local = local_id(body, "result");

    let callee_temp = body.blocks.iter().find_map(|bb| match &bb.terminator {
        Term::Call {
            func: Operand::Copy(Place::Local(func_local)),
            destination: Place::Local(dest),
            ..
        } if *dest == result_local => Some(*func_local),
        _ => None,
    });
    let callee_temp = callee_temp
        .expect("calling a returned fn value should use a temporary local as the callee operand");

    assert!(
        body.locals[callee_temp as usize].name.is_none(),
        "returned callable should materialize into an anonymous temp local: {body:#?}"
    );
    assert_eq!(
        body.locals[callee_temp as usize].ty,
        RustType::Function {
            params: vec![RustType::Uint(clean_rust_sem::UintType::U32)],
            ret: Box::new(RustType::Uint(clean_rust_sem::UintType::U32)),
        },
        "the callee temp should preserve the returned bare-fn type"
    );

    assert!(
        lowered
            .check_borrows()
            .get("main")
            .expect("borrow analyses should include `main`")
            .errors
            .is_empty(),
        "calling a returned fn value should stay NLL-clean"
    );
}

#[test]
fn test_non_capturing_closure_let_annotation_coerces_to_fn_pointer() {
    let source = r#"
        fn main() -> u32 {
            let f: fn(u32) -> u32 = |x: u32| -> u32 { x + 1u32 };
            f(41u32)
        }
    "#;

    let lowered = lowered_program(source);
    let body = lowered
        .functions
        .get("main")
        .expect("lowered program should contain `main`");
    let f_local = local_id(body, "f");
    let closure_name = lowered
        .functions
        .keys()
        .find(|name| name.starts_with("main::{closure#"))
        .cloned()
        .expect("lowered program should register a closure body");

    let has_fn_ptr_assign = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .any(|stmt| {
            matches!(
                stmt,
                clean_rust_sem::Stmt::Assign {
                    place: Place::Local(dst),
                    rvalue: Rvalue::Use(Operand::Constant(Constant::FnDef { name, .. })),
                } if *dst == f_local && name == &closure_name
            )
        });
    assert!(
        has_fn_ptr_assign,
        "non-capturing closure let annotation should lower as Constant::FnDef into the fn-typed local: {body:#?}"
    );
    assert_eq!(
        body.locals[f_local as usize].ty,
        RustType::Function {
            params: vec![RustType::Uint(clean_rust_sem::UintType::U32)],
            ret: Box::new(RustType::Uint(clean_rust_sem::UintType::U32)),
        },
        "the annotated local should keep the bare fn-pointer type"
    );
}

#[test]
fn test_non_capturing_closure_argument_coerces_to_fn_pointer() {
    let source = r#"
        fn apply(f: fn(u32) -> u32, value: u32) -> u32 {
            f(value)
        }

        fn main() -> u32 {
            let f = |x: u32| -> u32 { x + 1u32 };
            apply(f, 41u32)
        }
    "#;

    let lowered = lowered_program(source);
    let body = lowered
        .functions
        .get("main")
        .expect("lowered program should contain `main`");
    let closure_name = lowered
        .functions
        .keys()
        .find(|name| name.starts_with("main::{closure#"))
        .cloned()
        .expect("lowered program should register a closure body");

    let coerced_arg_local = body.blocks.iter().find_map(|bb| match &bb.terminator {
        Term::Call {
            func: Operand::Constant(Constant::FnDef { name, .. }),
            args,
            ..
        } if name == "apply" => match args.first() {
            Some(Operand::Copy(Place::Local(local))) | Some(Operand::Move(Place::Local(local))) => {
                Some(*local)
            }
            _ => None,
        },
        _ => None,
    });
    let coerced_arg_local =
        coerced_arg_local.expect("call to `apply` should use a coerced fn-pointer local");

    let has_fn_ptr_assign = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .any(|stmt| {
            matches!(
                stmt,
                clean_rust_sem::Stmt::Assign {
                    place: Place::Local(dst),
                    rvalue: Rvalue::Use(Operand::Constant(Constant::FnDef { name, .. })),
                } if *dst == coerced_arg_local && name == &closure_name
            )
        });
    assert!(
        has_fn_ptr_assign,
        "passing a non-capturing closure to a bare-fn parameter should synthesize a fn-pointer temp: {body:#?}"
    );
    assert_eq!(
        body.locals[coerced_arg_local as usize].ty,
        RustType::Function {
            params: vec![RustType::Uint(clean_rust_sem::UintType::U32)],
            ret: Box::new(RustType::Uint(clean_rust_sem::UintType::U32)),
        },
        "the coerced argument temp should carry the callee's fn-pointer type"
    );
}

#[test]
fn test_free_function_shared_ref_arg_autoderefs_like_method_receiver() {
    let source = r#"
        struct Pair { value: u32 }

        fn takes(pair: &Pair) -> u32 {
            pair.value
        }

        fn main() -> u32 {
            let pair = Pair { value: 42u32 };
            let r1: &Pair = &pair;
            let r2: &&Pair = &r1;
            takes(r2)
        }
    "#;

    let lowered = lowered_program(source);
    let body = lowered
        .functions
        .get("main")
        .expect("lowered program should contain `main`");
    let r2_local = local_id(body, "r2");

    let coerced_arg_local = body.blocks.iter().find_map(|bb| match &bb.terminator {
        Term::Call {
            func: Operand::Constant(Constant::FnDef { name, .. }),
            args,
            ..
        } if name == "takes" => match args.first() {
            Some(Operand::Copy(Place::Local(local))) | Some(Operand::Move(Place::Local(local))) => {
                Some(*local)
            }
            _ => None,
        },
        _ => None,
    });
    let coerced_arg_local =
        coerced_arg_local.expect("call to `takes` should use a coerced shared-reference temp");

    let borrowed_place = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .find_map(|stmt| match stmt {
            clean_rust_sem::Stmt::Assign {
                place: Place::Local(temp),
                rvalue:
                    Rvalue::Ref {
                        borrow_kind: BorrowKind::Shared,
                        place,
                    },
            } if *temp == coerced_arg_local => Some(place.clone()),
            _ => None,
        })
        .expect("the coerced call arg should be initialized by a shared reborrow");

    assert!(
        matches!(
            &borrowed_place,
            Place::Deref(inner)
                if matches!(
                    inner.as_ref(),
                    Place::Deref(root)
                        if matches!(root.as_ref(), Place::Local(local) if *local == r2_local)
                )
        ),
        "free-function `&Pair` arguments should autoderef `&&Pair` to the referent before reborrowing: {body:#?}"
    );
    assert!(
        lowered
            .check_borrows()
            .get("main")
            .expect("borrow analyses should include `main`")
            .errors
            .is_empty(),
        "free-function shared-ref coercion should stay NLL-clean"
    );
}
