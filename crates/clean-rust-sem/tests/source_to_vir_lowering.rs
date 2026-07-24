// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_rust_sem::vir::{AggregateKind, BorrowKind, CastKind, Constant, MutBorrowKind, Term};
use clean_rust_sem::{Body, Operand, Place, RustType, Rvalue, SourceProgram, Stmt, UintType};

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

fn copied_from_local(body: &Body, destination: u32) -> u32 {
    body.blocks[0]
        .statements
        .iter()
        .find_map(|stmt| match stmt {
            Stmt::Assign {
                place: Place::Local(dst),
                rvalue:
                    Rvalue::Use(Operand::Copy(Place::Local(src)))
                    | Rvalue::Use(Operand::Move(Place::Local(src))),
            } if *dst == destination => Some(*src),
            _ => None,
        })
        .expect("destination should be assigned from a source local")
}

#[test]
fn test_source_program_lower_to_vir_runs_nll_on_shared_borrow() {
    let source = r#"
        fn main() -> u32 {
            let mut x: u32 = 1u32;
            let r = &x;
            let y: u32 = *r;
            x = 2u32;
            y
        }
    "#;

    let body = lowered_main(source);
    let borrow_stmt = body.blocks[0]
        .statements
        .iter()
        .find(|stmt| {
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
        })
        .expect("lowering should emit an explicit shared borrow");
    assert!(
        matches!(
            borrow_stmt,
            Stmt::Assign {
                place: Place::Local(_),
                rvalue: Rvalue::Ref {
                    borrow_kind: BorrowKind::Shared,
                    place: Place::Local(_),
                },
            }
        ),
        "borrow lowering should stay on local places: {borrow_stmt:?}"
    );

    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "borrow should die at last use before the later write: {:?}",
        result.errors
    );
}

#[test]
fn test_source_program_lower_to_vir_rejects_write_while_borrowed() {
    let source = r#"
        fn main() -> u32 {
            let mut x: u32 = 1u32;
            let r = &x;
            x = 2u32;
            *r
        }
    "#;

    let result = borrow_result_for_main(source);
    assert!(
        result
            .errors
            .iter()
            .any(|err| matches!(err, clean_rust_sem::NllError::AssignWhileBorrowed { .. })),
        "write through the original local should conflict with the live borrow: {:?}",
        result.errors
    );
}

#[test]
fn test_source_program_lower_to_vir_distinguishes_shadowed_bindings() {
    let source = r#"
        fn main() -> u32 {
            let x: u32 = 1u32;
            {
                let x: u32 = 2u32;
                let shadow_copy: u32 = x;
            }
            let outer_copy: u32 = x;
            outer_copy
        }
    "#;

    let body = lowered_main(source);
    let x_locals: Vec<u32> = body
        .locals
        .iter()
        .enumerate()
        .filter_map(|(idx, decl)| (decl.name.as_deref() == Some("x")).then_some(idx as u32))
        .collect();
    assert_eq!(x_locals.len(), 2, "shadowing should allocate a fresh local");

    let outer_x = x_locals[0];
    let inner_x = x_locals[1];
    let shadow_copy = local_id(&body, "shadow_copy");
    let outer_copy = local_id(&body, "outer_copy");

    assert_eq!(
        copied_from_local(&body, shadow_copy),
        inner_x,
        "inner copy should read from the shadowed local"
    );
    assert_eq!(
        copied_from_local(&body, outer_copy),
        outer_x,
        "outer copy should read from the original local"
    );
}

#[test]
fn test_if_expr_lowers_to_multi_block_cfg() {
    let source = r#"
        fn main() -> u32 {
            let x: bool = true;
            if x { 1u32 } else { 2u32 }
        }
    "#;

    let body = lowered_main(source);
    assert!(
        body.blocks.len() >= 4,
        "if-expression should produce at least 4 blocks (entry, then, else, merge), got {}",
        body.blocks.len()
    );

    // The entry block should have a SwitchInt terminator.
    let has_switch = body
        .blocks
        .iter()
        .any(|bb| matches!(&bb.terminator, Term::SwitchInt { .. }));
    assert!(
        has_switch,
        "if-expression should produce a SwitchInt terminator"
    );
}

#[test]
fn test_if_expr_borrow_confined_to_then_branch() {
    // Borrow lives only in the then-branch, write happens after the if.
    // NLL should accept this because the borrow's region doesn't extend
    // past the branch.
    let source = r#"
        fn main() -> u32 {
            let mut x: u32 = 1u32;
            let cond: bool = true;
            let y: u32 = if cond {
                let r = &x;
                *r
            } else {
                0u32
            };
            x = 2u32;
            y
        }
    "#;

    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "borrow confined to then-branch should not conflict with post-if write: {:?}",
        result.errors
    );
}

#[test]
fn test_if_expr_both_branches_return_produces_terminated_cfg() {
    let source = r#"
        fn main() -> u32 {
            let x: bool = true;
            if x {
                return 1u32;
            } else {
                return 2u32;
            }
        }
    "#;

    let body = lowered_main(source);
    // Both branches return, so the merge block should be unreachable.
    // The function should still have valid structure.
    let return_count = body
        .blocks
        .iter()
        .filter(|bb| matches!(bb.terminator, Term::Return))
        .count();
    assert!(
        return_count >= 2,
        "both branches returning should produce at least 2 Return terminators, got {return_count}"
    );
}

#[test]
fn test_match_expr_lowers_literal_arms_to_cfg() {
    let source = r#"
        fn main() -> u32 {
            let tag: u32 = 1u32;
            match tag {
                0u32 => 7u32,
                1u32 => 9u32,
                _ => 11u32,
            }
        }
    "#;

    let body = lowered_main(source);
    let switch_count = body
        .blocks
        .iter()
        .filter(|bb| matches!(&bb.terminator, Term::SwitchInt { .. }))
        .count();
    assert!(
        switch_count >= 2,
        "literal match should emit one SwitchInt per tested arm, got {switch_count}"
    );
    assert!(
        body.blocks.len() >= 6,
        "multi-arm match should expand into a multi-block CFG, got {} blocks",
        body.blocks.len()
    );

    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "literal match lowering should still produce an NLL-clean body: {:?}",
        result.errors
    );
}

#[test]
fn test_match_guard_false_falls_through_to_later_arm() {
    let source = r#"
        fn main() -> u32 {
            let mut x: u32 = 1u32;
            let tag: u32 = 1u32;
            let y: u32 = match tag {
                n if n == 0u32 => {
                    let r = &x;
                    *r
                }
                _ => {
                    x = 2u32;
                    x
                }
            };
            x = 3u32;
            y
        }
    "#;

    let body = lowered_main(source);
    assert!(
        body.locals
            .iter()
            .any(|decl| decl.name.as_deref() == Some("n")),
        "guarded binding arm should allocate a named local for the bound scrutinee"
    );

    let switch_count = body
        .blocks
        .iter()
        .filter(|bb| matches!(&bb.terminator, Term::SwitchInt { .. }))
        .count();
    assert!(
        switch_count >= 1,
        "guarded irrefutable arm should still emit a guard switch, got {switch_count}"
    );

    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "guard-false fallthrough should not leak borrows across match arms: {:?}",
        result.errors
    );
}

#[test]
fn test_tuple_let_binding_destructures_into_field_places() {
    let source = r#"
        fn main() -> u32 {
            let pair: (u32, u32) = (40u32, 2u32);
            let (a, b) = pair;
            a + b
        }
    "#;

    let body = lowered_main(source);
    let pair_local = local_id(&body, "pair");
    let a_local = local_id(&body, "a");
    let b_local = local_id(&body, "b");

    let a_assign = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .find(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    place: Place::Local(dst),
                    rvalue: Rvalue::Use(Operand::Copy(Place::Field { base, field })),
                } if *dst == a_local
                    && matches!(base.as_ref(), Place::Local(local) if *local == pair_local)
                    && field == "0"
            )
        })
        .expect("tuple destructuring should bind `a` from tuple field 0");
    let b_assign = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .find(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    place: Place::Local(dst),
                    rvalue: Rvalue::Use(Operand::Copy(Place::Field { base, field })),
                } if *dst == b_local
                    && matches!(base.as_ref(), Place::Local(local) if *local == pair_local)
                    && field == "1"
            )
        })
        .expect("tuple destructuring should bind `b` from tuple field 1");

    assert!(
        matches!(a_assign, Stmt::Assign { .. }) && matches!(b_assign, Stmt::Assign { .. }),
        "tuple destructuring should lower through tuple field places: {a_assign:?} / {b_assign:?}"
    );

    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "tuple destructuring should keep the lowered CFG NLL-clean: {:?}",
        result.errors
    );
}

#[test]
fn test_let_else_tuple_pattern_lowers_diverging_failure_branch() {
    let source = r#"
        fn main() -> u32 {
            let pair: (u32, u32) = (40u32, 2u32);
            let (a, 2u32) = pair else {
                return 0u32;
            };
            a + 2u32
        }
    "#;

    let body = lowered_main(source);
    let a_local = local_id(&body, "a");
    let return_count = body
        .blocks
        .iter()
        .filter(|bb| matches!(bb.terminator, Term::Return))
        .count();
    let switch_count = body
        .blocks
        .iter()
        .filter(|bb| matches!(&bb.terminator, Term::SwitchInt { .. }))
        .count();

    assert!(
        switch_count >= 1,
        "refutable let-else tuple pattern should emit a branching test, got {switch_count}"
    );
    assert!(
        return_count >= 2,
        "let-else success + diverging else should produce at least 2 return paths, got {return_count}"
    );
    assert!(
        body.blocks
            .iter()
            .flat_map(|bb| bb.statements.iter())
            .any(|stmt| {
                matches!(
                    stmt,
                    Stmt::Assign {
                        place: Place::Local(dst),
                        rvalue: Rvalue::Use(Operand::Copy(Place::Field { field, .. })),
                    } if *dst == a_local && field == "0"
                )
            }),
        "successful let-else branch should still bind `a` from tuple field 0"
    );

    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "let-else tuple lowering should stay NLL-clean: {:?}",
        result.errors
    );
}

#[test]
fn test_loop_expr_labeled_break_value_lowers_without_annotation() {
    let source = r#"
        fn main() -> u32 {
            let result = 'outer: loop {
                loop {
                    break 'outer 42u32;
                }
            };
            result
        }
    "#;

    let body = lowered_main(source);
    assert!(
        body.blocks.len() >= 6,
        "nested loop lowering should produce multiple CFG blocks, got {}",
        body.blocks.len()
    );
    assert!(
        body.locals
            .iter()
            .any(|decl| decl.name.as_deref() == Some("result")),
        "loop result should lower into the named binding"
    );

    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "labeled break value should produce a valid NLL body: {:?}",
        result.errors
    );
}

#[test]
fn test_while_continue_cleans_loop_scoped_borrows() {
    let source = r#"
        fn main() -> u32 {
            let mut x: u32 = 0u32;
            let mut i: u32 = 0u32;
            while i < 2u32 {
                let r = &x;
                if i == 0u32 {
                    i = 1u32;
                    continue;
                }
                let y: u32 = *r;
                i = y + 2u32;
            }
            x = 2u32;
            x
        }
    "#;

    let body = lowered_main(source);
    assert!(
        body.blocks
            .iter()
            .any(|bb| matches!(&bb.terminator, Term::SwitchInt { .. })),
        "while-expression should lower through a condition switch"
    );

    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "continue should kill loop-scoped borrows before the next edge: {:?}",
        result.errors
    );
}

#[test]
fn test_labeled_continue_targets_outer_loop_header() {
    let source = r#"
        fn main() -> u32 {
            let mut outer: u32 = 0u32;
            let mut total: u32 = 0u32;
            'outer: while outer < 3u32 {
                outer = outer + 1u32;
                let mut inner: u32 = 0u32;
                loop {
                    inner = inner + 1u32;
                    if inner == 2u32 {
                        continue 'outer;
                    }
                }
                total = 99u32;
            }
            outer + total
        }
    "#;

    let body = lowered_main(source);
    assert!(
        body.blocks.len() >= 8,
        "nested labeled continue should expand into multiple CFG blocks, got {}",
        body.blocks.len()
    );

    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "labeled continue to an outer loop should keep the lowered CFG NLL-clean: {:?}",
        result.errors
    );
}

#[test]
fn test_direct_call_lowers_to_term_call_with_continuation() {
    let source = r#"
        fn add(a: u32, b: u32) -> u32 {
            a + b
        }
        fn main() -> u32 {
            let x: u32 = 1u32;
            let y: u32 = 2u32;
            add(x, y)
        }
    "#;

    let program = SourceProgram::parse(source).expect("source should parse");
    let lowered = program.lower_to_vir().expect("source should lower to VIR");
    let body = lowered
        .functions
        .get("main")
        .expect("lowered program should contain `main`");

    let has_call = body.blocks.iter().any(|bb| {
        matches!(
            &bb.terminator,
            Term::Call {
                func: Operand::Constant(Constant::FnDef { name, .. }),
                target: Some(_),
                ..
            } if name == "add"
        )
    });
    assert!(
        has_call,
        "direct function call should produce a Term::Call with a continuation block"
    );

    assert!(
        lowered.functions.contains_key("add"),
        "helper function `add` should also be lowered"
    );
}

#[test]
fn test_method_call_shared_receiver_creates_borrow() {
    let source = r#"
        struct Counter { val: u32 }
        impl Counter {
            fn get(&self) -> u32 {
                self.val
            }
        }
        fn main() -> u32 {
            let c = Counter { val: 42u32 };
            c.get()
        }
    "#;

    let program = SourceProgram::parse(source).expect("source should parse");
    let lowered = program.lower_to_vir().expect("source should lower to VIR");
    let body = lowered
        .functions
        .get("main")
        .expect("lowered program should contain `main`");

    let has_shared_borrow = body.blocks.iter().any(|bb| {
        bb.statements.iter().any(|stmt| {
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
        })
    });
    assert!(
        has_shared_borrow,
        "method call with &self should emit a shared borrow for the receiver"
    );

    let has_method_call = body.blocks.iter().any(|bb| {
        matches!(
            &bb.terminator,
            Term::Call {
                func: Operand::Constant(Constant::FnDef { name, .. }),
                ..
            } if name == "Counter::get"
        )
    });
    assert!(
        has_method_call,
        "method call should produce a Term::Call with the qualified name"
    );

    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "shared receiver method call should be NLL-clean: {:?}",
        result.errors
    );
}

#[test]
fn test_method_call_mut_receiver_creates_two_phase_borrow() {
    let source = r#"
        struct Acc { total: u32 }
        impl Acc {
            fn add(&mut self, n: u32) -> u32 {
                self.total = self.total + n;
                self.total
            }
        }
        fn main() -> u32 {
            let mut a = Acc { total: 0u32 };
            a.add(5u32)
        }
    "#;

    let program = SourceProgram::parse(source).expect("source should parse");
    let lowered = program.lower_to_vir().expect("source should lower to VIR");
    let body = lowered
        .functions
        .get("main")
        .expect("lowered program should contain `main`");

    let has_two_phase = body.blocks.iter().any(|bb| {
        bb.statements.iter().any(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    rvalue: Rvalue::Ref {
                        borrow_kind: BorrowKind::Mut {
                            kind: MutBorrowKind::TwoPhaseBorrow,
                        },
                        ..
                    },
                    ..
                }
            )
        })
    });
    assert!(
        has_two_phase,
        "method call with &mut self should emit a two-phase mutable borrow"
    );

    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "two-phase mutable receiver call should be NLL-clean: {:?}",
        result.errors
    );
}

#[test]
fn test_call_as_argument_materializes_into_temp() {
    let source = r#"
        fn double(x: u32) -> u32 {
            x + x
        }
        fn main() -> u32 {
            double(double(3u32))
        }
    "#;

    let program = SourceProgram::parse(source).expect("source should parse");
    let lowered = program.lower_to_vir().expect("source should lower to VIR");
    let body = lowered
        .functions
        .get("main")
        .expect("lowered program should contain `main`");

    let call_count = body
        .blocks
        .iter()
        .filter(|bb| matches!(&bb.terminator, Term::Call { .. }))
        .count();
    assert!(
        call_count >= 2,
        "nested call should produce at least 2 Term::Call terminators (inner + outer), got {call_count}"
    );

    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "nested direct calls should be NLL-clean: {:?}",
        result.errors
    );
}

#[test]
fn test_tuple_expr_lowers_to_tuple_aggregate() {
    let source = r#"
        fn main() -> u32 {
            let pair: (u32, bool) = (1u32, true);
            0u32
        }
    "#;

    let body = lowered_main(source);
    let pair_local = local_id(&body, "pair");
    let tuple_assign = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .find(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    place: Place::Local(dst),
                    rvalue: Rvalue::Aggregate {
                        kind: AggregateKind::Tuple,
                        operands,
                    },
                } if *dst == pair_local && operands.len() == 2
            )
        })
        .expect("tuple binding should lower through AggregateKind::Tuple");

    assert!(
        matches!(
            tuple_assign,
            Stmt::Assign {
                place: Place::Local(_),
                rvalue: Rvalue::Aggregate {
                    kind: AggregateKind::Tuple,
                    operands,
                },
            } if operands.len() == 2
        ),
        "tuple lowering should preserve both operands: {tuple_assign:?}"
    );

    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "tuple aggregate lowering should stay NLL-clean: {:?}",
        result.errors
    );
}

#[test]
fn test_array_expr_lowers_to_array_aggregate() {
    let source = r#"
        fn main() -> u32 {
            let arr: [u32; 3] = [1u32, 2u32, 3u32];
            0u32
        }
    "#;

    let body = lowered_main(source);
    let arr_local = local_id(&body, "arr");
    let array_assign = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .find(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    place: Place::Local(dst),
                    rvalue: Rvalue::Aggregate {
                        kind: AggregateKind::Array(RustType::Uint(UintType::U32)),
                        operands,
                    },
                } if *dst == arr_local && operands.len() == 3
            )
        })
        .expect("array binding should lower through AggregateKind::Array");

    assert!(
        matches!(
            array_assign,
            Stmt::Assign {
                place: Place::Local(_),
                rvalue: Rvalue::Aggregate {
                    kind: AggregateKind::Array(RustType::Uint(UintType::U32)),
                    operands,
                },
            } if operands.len() == 3
        ),
        "array lowering should preserve the element type and arity: {array_assign:?}"
    );

    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "array aggregate lowering should stay NLL-clean: {:?}",
        result.errors
    );
}

#[test]
fn test_index_expr_lowers_through_place_index() {
    let source = r#"
        fn main() -> u32 {
            let arr: [u32; 3] = [1u32, 2u32, 3u32];
            let picked: u32 = arr[1usize];
            picked
        }
    "#;

    let body = lowered_main(source);
    let arr_local = local_id(&body, "arr");
    let picked_local = local_id(&body, "picked");
    let picked_assign = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .find_map(|stmt| match stmt {
            Stmt::Assign {
                place: Place::Local(dst),
                rvalue:
                    Rvalue::Use(Operand::Copy(Place::Index { base, index }))
                    | Rvalue::Use(Operand::Move(Place::Index { base, index })),
            } if *dst == picked_local => Some((base.as_ref(), index.as_ref())),
            _ => None,
        })
        .expect("indexed read should lower through Place::Index");

    let (base_place, index_place) = picked_assign;
    assert!(
        matches!(base_place, Place::Local(local) if *local == arr_local),
        "indexed base should stay rooted on the array local: {base_place:?}"
    );

    let index_local = match index_place {
        Place::Local(local) => *local,
        other => panic!("index expression should materialize into a temp local, got {other:?}"),
    };
    assert_eq!(
        body.locals[index_local as usize].ty,
        RustType::Uint(UintType::Usize),
        "literal index should materialize with the parsed usize type"
    );

    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "indexed reads should stay NLL-clean: {:?}",
        result.errors
    );
}

#[test]
fn test_cast_expr_lowers_to_rvalue_cast() {
    let source = r#"
        fn main() -> u32 {
            let flag: bool = true;
            let as_num: u32 = flag as u32;
            as_num
        }
    "#;

    let body = lowered_main(source);
    let flag_local = local_id(&body, "flag");
    let as_num_local = local_id(&body, "as_num");
    let cast_assign = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .find(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    place: Place::Local(dst),
                    rvalue: Rvalue::Cast {
                        kind: CastKind::IntToInt,
                        operand: Operand::Copy(Place::Local(src)),
                        ty: RustType::Uint(UintType::U32),
                    },
                } if *dst == as_num_local && *src == flag_local
            )
        })
        .expect("cast binding should lower through Rvalue::Cast");

    assert!(
        matches!(
            cast_assign,
            Stmt::Assign {
                place: Place::Local(_),
                rvalue: Rvalue::Cast {
                    kind: CastKind::IntToInt,
                    operand: Operand::Copy(Place::Local(_)),
                    ty: RustType::Uint(UintType::U32),
                },
            }
        ),
        "cast lowering should preserve the operand and target type: {cast_assign:?}"
    );

    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "cast lowering should stay NLL-clean: {:?}",
        result.errors
    );
}

#[test]
fn test_source_byte_string_literal_expr_lowers_to_byte_str_constant() {
    // A byte-string literal `b"ab"` is represented in semantic values as a
    // `Value::Array` of `u8` scalars; VIR lowering must reconstruct the
    // dedicated `Constant::ByteStr` rather than rejecting it as a non-scalar
    // literal.
    let source = r#"
        fn main() {
            let x = b"ab";
        }
    "#;

    let body = lowered_main(source);
    let byte_str = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .find_map(|stmt| match stmt {
            Stmt::Assign {
                rvalue: Rvalue::Use(Operand::Constant(Constant::ByteStr(bytes))),
                ..
            } => Some(bytes.clone()),
            _ => None,
        })
        .expect("byte-string literal should lower to a `Constant::ByteStr`");

    assert_eq!(
        byte_str,
        vec![b'a', b'b'],
        "byte-string constant must preserve the exact byte sequence"
    );
}

#[test]
fn test_source_byte_string_literal_pattern_lowers_to_eq_against_byte_str() {
    // Matching against a byte-string literal pattern compares the scrutinee for
    // equality with the byte-string constant, exactly as MIR models it.
    let source = r#"
        fn main() -> u32 {
            let s = b"ab";
            match s {
                b"ab" => 1u32,
                _ => 0u32,
            }
        }
    "#;

    let body = lowered_main(source);
    let has_byte_str_eq = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .any(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    place: _,
                    rvalue: Rvalue::BinaryOp {
                        op: clean_rust_sem::vir::BinOp::Eq,
                        rhs: Operand::Constant(Constant::ByteStr(bytes)),
                        ..
                    },
                } if bytes.as_slice() == b"ab"
            )
        });

    assert!(
        has_byte_str_eq,
        "byte-string pattern should lower to an `Eq` against a `Constant::ByteStr`: {:?}",
        body.blocks
    );

    // The lowering must remain borrow-clean.
    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "byte-string pattern lowering should stay NLL-clean: {:?}",
        result.errors
    );
}

/// Collects the byte payload of the first `Constant::ByteStr` produced by
/// lowering `main`, panicking with a descriptive message if none exists.
fn first_byte_str_in_main(source: &str) -> Vec<u8> {
    let body = lowered_main(source);
    body.blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .find_map(|stmt| match stmt {
            Stmt::Assign {
                rvalue: Rvalue::Use(Operand::Constant(Constant::ByteStr(bytes))),
                ..
            } => Some(bytes.clone()),
            _ => None,
        })
        .expect("C-string literal should lower to a `Constant::ByteStr`")
}

#[test]
fn test_source_c_string_literal_expr_lowers_to_nul_terminated_bytes() {
    // A C-string literal `c"abc"` denotes a `&CStr`: a NUL-terminated byte
    // sequence. It is represented as a `Value::Array` of `u8` scalars whose
    // final element is the trailing NUL, so `c"abc"` lowers to [97, 98, 99, 0].
    let source = r#"
        fn main() {
            let x = c"abc";
        }
    "#;

    assert_eq!(
        first_byte_str_in_main(source),
        vec![97, 98, 99, 0],
        "C-string `c\"abc\"` must lower to its content bytes plus a trailing NUL"
    );
}

#[test]
fn test_source_empty_c_string_literal_lowers_to_single_nul() {
    // An empty C-string `c""` is still NUL-terminated: it lowers to [0].
    let source = r#"
        fn main() {
            let x = c"";
        }
    "#;

    assert_eq!(
        first_byte_str_in_main(source),
        vec![0],
        "empty C-string `c\"\"` must lower to a single trailing NUL byte"
    );
}

#[test]
fn test_source_raw_c_string_literal_lowers_to_nul_terminated_bytes() {
    // The raw form `cr"..."` is surfaced by syn as the same `Lit::CStr` and must
    // share the NUL-terminated lowering. Backslashes are not escapes in raw
    // strings, so `cr"a\b"` carries the literal bytes [97, 92, 98] plus NUL.
    let source = r#"
        fn main() {
            let x = cr"a\b";
        }
    "#;

    assert_eq!(
        first_byte_str_in_main(source),
        vec![97, 92, 98, 0],
        "raw C-string `cr\"a\\b\"` must preserve literal bytes plus a trailing NUL"
    );
}

#[test]
fn test_source_c_string_literal_used_in_expression_stays_borrow_clean() {
    // A C-string used in an expression (here bound and re-borrowed) must lower
    // and the resulting VIR must remain NLL-clean.
    let source = r#"
        fn main() {
            let s = c"hi";
            let r = &s;
            let _ = r;
        }
    "#;

    // Lowering succeeds and yields the NUL-terminated byte payload.
    assert_eq!(
        first_byte_str_in_main(source),
        vec![104, 105, 0],
        "C-string used in an expression must lower to its bytes plus a trailing NUL"
    );

    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "C-string expression lowering should stay NLL-clean: {:?}",
        result.errors
    );
}
