// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_rust_sem::vir::{BorrowKind, Constant, MutBorrowKind, Term};
use clean_rust_sem::{Body, Mutability, Operand, Place, RustType, Rvalue, SourceProgram, Stmt};

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
fn test_method_call_on_shared_ref_receiver_reborrows_referent() {
    let source = r#"
        struct Counter { val: u32 }
        impl Counter {
            fn get(&self) -> u32 {
                self.val
            }
        }
        fn main() -> u32 {
            let c = Counter { val: 42u32 };
            let r: &Counter = &c;
            r.get()
        }
    "#;

    let body = lowered_main(source);
    let r_local = local_id(&body, "r");
    let receiver_temp = body
        .blocks
        .iter()
        .find_map(|bb| match &bb.terminator {
            Term::Call {
                func: Operand::Constant(Constant::FnDef { name, .. }),
                args,
                ..
            } if name == "Counter::get" => match args.first() {
                Some(Operand::Move(Place::Local(local))) => Some(*local),
                other => panic!("shared receiver call should use a temporary local, got {other:?}"),
            },
            _ => None,
        })
        .expect("borrowed shared receiver call should exist");
    let borrowed_place = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .find_map(|stmt| match stmt {
            Stmt::Assign {
                place: Place::Local(temp),
                rvalue:
                    Rvalue::Ref {
                        borrow_kind: BorrowKind::Shared,
                        place,
                    },
            } if *temp == receiver_temp => Some(place.clone()),
            _ => None,
        })
        .expect("borrowed shared receiver should emit a shared reborrow temp");

    assert!(
        matches!(
            &borrowed_place,
            Place::Deref(base) if matches!(base.as_ref(), Place::Local(local) if *local == r_local)
        ),
        "borrowed shared receiver should reborrow the referent, not the reference local: {body:#?}"
    );
    match &body.locals[receiver_temp as usize].ty {
        RustType::Reference {
            mutability, inner, ..
        } => {
            assert_eq!(
                *mutability,
                Mutability::Shared,
                "shared receiver temp should stay shared: {body:#?}"
            );
            assert!(
                matches!(inner.as_ref(), RustType::Named { name, .. } if name == "Counter"),
                "shared receiver temp should point at `Counter`, not a nested reference: {body:#?}"
            );
        }
        other => panic!("shared receiver temp should be a reference, found {other:?} in {body:#?}"),
    }

    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "borrowed shared receiver method call should stay NLL-clean: {:?}",
        result.errors
    );
}

#[test]
fn test_method_call_on_temporary_shared_receiver_materializes_receiver_place() {
    let source = r#"
        struct Counter { val: u32 }
        impl Counter {
            fn get(&self) -> u32 {
                self.val
            }
        }
        fn main() -> u32 {
            Counter { val: 42u32 }.get()
        }
    "#;

    let body = lowered_main(source);
    let receiver_temp = body
        .blocks
        .iter()
        .find_map(|bb| match &bb.terminator {
            Term::Call {
                func: Operand::Constant(Constant::FnDef { name, .. }),
                args,
                ..
            } if name == "Counter::get" => match args.first() {
                Some(Operand::Move(Place::Local(local))) => Some(*local),
                other => panic!("shared receiver call should use a temporary local, got {other:?}"),
            },
            _ => None,
        })
        .expect("temporary shared receiver call should exist");
    let borrowed_place = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .find_map(|stmt| match stmt {
            Stmt::Assign {
                place: Place::Local(temp),
                rvalue:
                    Rvalue::Ref {
                        borrow_kind: BorrowKind::Shared,
                        place,
                    },
            } if *temp == receiver_temp => Some(place.clone()),
            _ => None,
        })
        .expect("temporary shared receiver should borrow a materialized place");
    let materialized_local = match borrowed_place {
        Place::Local(local) => local,
        other => panic!("temporary shared receiver should borrow a temp local, got {other:?}"),
    };

    assert!(
        matches!(
            &body.locals[materialized_local as usize].ty,
            RustType::Named { name, .. } if name == "Counter"
        ),
        "temporary shared receiver should materialize the `Counter` value before borrowing: {body:#?}"
    );

    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "temporary shared receiver method call should stay NLL-clean: {:?}",
        result.errors
    );
}

#[test]
fn test_method_call_on_mut_ref_receiver_reborrows_referent_two_phase() {
    let source = r#"
        struct Counter { value: u32 }
        impl Counter {
            fn bump(&mut self) -> u32 {
                self.value = self.value + 1u32;
                self.value
            }
        }
        fn main() -> u32 {
            let mut counter = Counter { value: 1u32 };
            let r: &mut Counter = &mut counter;
            r.bump()
        }
    "#;

    let body = lowered_main(source);
    let r_local = local_id(&body, "r");
    let receiver_temp = body
        .blocks
        .iter()
        .find_map(|bb| match &bb.terminator {
            Term::Call {
                func: Operand::Constant(Constant::FnDef { name, .. }),
                args,
                ..
            } if name == "Counter::bump" => match args.first() {
                Some(Operand::Move(Place::Local(local))) => Some(*local),
                other => {
                    panic!("mutable receiver call should use a temporary local, got {other:?}")
                }
            },
            _ => None,
        })
        .expect("borrowed mutable receiver call should exist");
    let borrowed_place = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .find_map(|stmt| match stmt {
            Stmt::Assign {
                place: Place::Local(temp),
                rvalue:
                    Rvalue::Ref {
                        borrow_kind:
                            BorrowKind::Mut {
                                kind: MutBorrowKind::TwoPhaseBorrow,
                            },
                        place,
                    },
            } if *temp == receiver_temp => Some(place.clone()),
            _ => None,
        })
        .expect("borrowed mutable receiver should emit a two-phase reborrow temp");

    assert!(
        matches!(
            &borrowed_place,
            Place::Deref(base) if matches!(base.as_ref(), Place::Local(local) if *local == r_local)
        ),
        "borrowed mutable receiver should reborrow the referent, not the reference local: {body:#?}"
    );
    match &body.locals[receiver_temp as usize].ty {
        RustType::Reference {
            mutability, inner, ..
        } => {
            assert_eq!(
                *mutability,
                Mutability::Mutable,
                "mutable receiver temp should stay mutable: {body:#?}"
            );
            assert!(
                matches!(inner.as_ref(), RustType::Named { name, .. } if name == "Counter"),
                "mutable receiver temp should point at `Counter`, not a nested reference: {body:#?}"
            );
        }
        other => {
            panic!("mutable receiver temp should be a reference, found {other:?} in {body:#?}")
        }
    }

    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "borrowed mutable receiver method call should stay NLL-clean: {:?}",
        result.errors
    );
}
