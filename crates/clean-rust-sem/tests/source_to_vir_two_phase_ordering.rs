// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_rust_sem::vir::{BorrowKind, Constant, MutBorrowKind, Term};
use clean_rust_sem::{Body, Operand, Place, SourceProgram};

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
fn test_method_call_mut_receiver_reservation_precedes_shared_argument_borrow() {
    let source = r#"
        struct Counter { value: u32 }
        impl Counter {
            fn get(&self) -> u32 {
                self.value
            }

            fn add(&mut self, n: u32) -> u32 {
                self.value = self.value + n;
                self.value
            }
        }

        fn main() -> u32 {
            let mut counter = Counter { value: 1u32 };
            counter.add(counter.get())
        }
    "#;

    let body = lowered_main(source);
    let counter_local = local_id(&body, "counter");

    let has_get_call = body.blocks.iter().any(|bb| {
        matches!(
            &bb.terminator,
            Term::Call {
                func: Operand::Constant(Constant::FnDef { name, .. }),
                ..
            } if name == "Counter::get"
        )
    });
    assert!(
        has_get_call,
        "shared receiver argument should lower through an explicit `Counter::get` call"
    );

    let has_add_call = body.blocks.iter().any(|bb| {
        matches!(
            &bb.terminator,
            Term::Call {
                func: Operand::Constant(Constant::FnDef { name, .. }),
                ..
            } if name == "Counter::add"
        )
    });
    assert!(
        has_add_call,
        "mutable receiver call should lower through an explicit `Counter::add` call"
    );

    let result = borrow_result_for_main(source);
    let two_phase = result
        .borrows
        .iter()
        .find(|borrow| {
            matches!(
                borrow.kind,
                BorrowKind::Mut {
                    kind: MutBorrowKind::TwoPhaseBorrow,
                }
            ) && matches!(borrow.borrowed_place, Place::Local(local) if local == counter_local)
        })
        .expect("outer mutable receiver should reserve a two-phase borrow of `counter`");
    let shared = result
        .borrows
        .iter()
        .find(|borrow| {
            matches!(borrow.kind, BorrowKind::Shared)
                && matches!(borrow.borrowed_place, Place::Local(local) if local == counter_local)
        })
        .expect("shared argument call should borrow the same `counter` local");
    assert!(
        two_phase.origin < shared.origin,
        "receiver reservation should occur before the shared argument borrow: {result:#?}"
    );
    assert!(
        result.errors.is_empty(),
        "two-phase receiver reservation should stay compatible with the shared argument borrow until activation: {:?}",
        result.errors
    );
}
