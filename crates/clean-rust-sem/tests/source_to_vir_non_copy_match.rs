// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for non-Copy scrutinee match lowering (issue #2842).
//!
//! Verifies that guarded bindings over non-Copy scrutinees lower to VIR
//! using by-ref bindings in the guard scope and by-move in the arm body,
//! and that literal matching on non-Copy scrutinees emits shared borrows.

use clean_rust_sem::vir::{BinOp, BorrowKind, Operand, Term};
use clean_rust_sem::{Body, Place, Rvalue, SourceProgram, Stmt};

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

/// Guarded binding on non-Copy enum scrutinee: the guard scope should bind
/// by shared reference, then the arm body should rebind by move.
#[test]
fn test_non_copy_enum_guard_binding_lowers_to_vir() {
    let source = r#"
        struct Payload {
            value: u32,
        }

        enum Action {
            Run(Payload),
            Stop,
        }

        fn main() -> u32 {
            let a: Action = Action::Run(Payload { value: 42u32 });
            match a {
                Action::Run(p) if p.value > 0u32 => p.value,
                _ => 0u32,
            }
        }
    "#;

    let body = lowered_main(source);

    // The lowered body should contain at least one Ref statement for the
    // guard-scope by-ref binding of `p`.
    let has_shared_ref = body.blocks.iter().any(|block| {
        block.statements.iter().any(|stmt| {
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
        has_shared_ref,
        "guard scope should create shared references for non-Copy bindings"
    );

    // The body should not terminate with Unreachable in the first block
    // (meaning lowering actually succeeded and produced meaningful VIR).
    assert!(
        !matches!(body.blocks[0].terminator, Term::Unreachable),
        "lowered body should have a real terminator, not Unreachable"
    );
}

/// Non-Copy scrutinee with guard but no bindings (wildcard arm with guard)
/// should continue to work as before — no ref binding needed.
#[test]
fn test_non_copy_guard_without_binding_still_works() {
    let source = r#"
        struct Payload {
            value: u32,
        }

        enum Action {
            Run(Payload),
            Stop,
        }

        fn main() -> u32 {
            let a: Action = Action::Run(Payload { value: 42u32 });
            let flag: bool = true;
            match a {
                Action::Run(_) if flag => 1u32,
                _ => 0u32,
            }
        }
    "#;

    let body = lowered_main(source);
    assert!(
        !matches!(body.blocks[0].terminator, Term::Unreachable),
        "non-Copy guard without bindings should lower successfully"
    );
}

/// Guarded binding on a non-Copy struct scrutinee.
#[test]
fn test_non_copy_struct_guard_binding_lowers() {
    let source = r#"
        struct Pair {
            x: u32,
            y: u32,
        }

        fn main() -> u32 {
            let p: Pair = Pair { x: 1u32, y: 2u32 };
            match p {
                Pair { x, y } if x > 0u32 => y,
                _ => 0u32,
            }
        }
    "#;

    let body = lowered_main(source);
    assert!(
        !matches!(body.blocks[0].terminator, Term::Unreachable),
        "non-Copy struct guard binding should lower successfully"
    );
}

/// Guarded binding on a non-Copy slice scrutinee should bind the indexed
/// element by shared reference during guard evaluation.
#[test]
fn test_non_copy_slice_guard_binding_lowers_to_index_ref() {
    let source = r#"
        struct Payload {
            value: u32,
        }

        fn main() -> u32 {
            let items: [Payload; 2] = [
                Payload { value: 1u32 },
                Payload { value: 2u32 },
            ];
            match items {
                [head, ..] if head.value > 0u32 => 1u32,
                _ => 0u32,
            }
        }
    "#;

    let body = lowered_main(source);

    let has_index_ref = body.blocks.iter().any(|block| {
        block.statements.iter().any(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    rvalue: Rvalue::Ref {
                        borrow_kind: BorrowKind::Shared,
                        place: Place::Index { .. },
                    },
                    ..
                }
            )
        })
    });
    assert!(
        has_index_ref,
        "slice guard binding should create a shared ref from an indexed element place"
    );
    assert!(
        !matches!(body.blocks[0].terminator, Term::Unreachable),
        "non-Copy slice guard binding should lower successfully"
    );
}

/// Rest-pattern suffix bindings should also stay by-ref in the guard scope.
#[test]
fn test_non_copy_slice_guard_suffix_binding_lowers_to_index_ref() {
    let source = r#"
        struct Payload {
            value: u32,
        }

        fn main() -> u32 {
            let items: [Payload; 3] = [
                Payload { value: 1u32 },
                Payload { value: 2u32 },
                Payload { value: 3u32 },
            ];
            match items {
                [first, .., last] if last.value > first.value => last.value,
                _ => 0u32,
            }
        }
    "#;

    let body = lowered_main(source);

    let index_ref_count = body
        .blocks
        .iter()
        .flat_map(|block| block.statements.iter())
        .filter(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    rvalue: Rvalue::Ref {
                        borrow_kind: BorrowKind::Shared,
                        place: Place::Index { .. },
                    },
                    ..
                }
            )
        })
        .count();
    assert!(
        index_ref_count >= 2,
        "rest slice guard binding should create shared refs for both prefix and suffix element places"
    );

    let has_suffix_index = body.blocks.iter().any(|block| {
        block.statements.iter().any(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    rvalue: Rvalue::BinaryOp { op: BinOp::Sub, .. },
                    ..
                }
            )
        })
    });
    assert!(
        has_suffix_index,
        "rest slice guard binding should compute a suffix index from the array length"
    );
    assert!(
        !matches!(body.blocks[0].terminator, Term::Unreachable),
        "non-Copy rest slice guard binding should lower successfully"
    );
}

/// `name @ subpattern` over a non-Copy scrutinee where the subpattern is
/// test-only (no inner bindings) should lower: the outer `whole` binding moves
/// the whole non-Copy value, and the subpattern emits no extra moves.
#[test]
fn test_at_binding_non_copy_scrutinee_test_only_subpattern_lowers_by_move() {
    let source = r#"
        struct Payload { value: u32 }
        enum Action { Run(Payload), Stop }
        fn main() -> u32 {
            let a: Action = Action::Run(Payload { value: 42u32 });
            match a {
                whole @ Action::Run(_) => 1u32,
                _ => 0u32,
            }
        }
    "#;

    let body = lowered_main(source);

    // The outer `whole` binding claims the whole non-Copy scrutinee, so there
    // must be a `Move` use of the scrutinee place into a fresh local.
    let has_move_use = body.blocks.iter().any(|block| {
        block.statements.iter().any(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    rvalue: Rvalue::Use(Operand::Move(_)),
                    ..
                }
            )
        })
    });
    assert!(
        has_move_use,
        "`whole @ pat` over a non-Copy scrutinee should move the whole value into `whole`"
    );
    assert!(
        !matches!(body.blocks[0].terminator, Term::Unreachable),
        "`@`-binding over a non-Copy scrutinee should lower successfully"
    );
}

/// `name @ subpattern` over a non-Copy scrutinee where the subpattern itself
/// binds an inner field: the inner binding must be taken *by reference*
/// (it cannot move a field out while `whole` moves the whole value), and the
/// outer `whole` binding still moves the whole value.
#[test]
fn test_at_binding_non_copy_inner_binding_lowers_subpattern_by_ref() {
    let source = r#"
        struct Payload { value: u32 }
        enum Action { Run(Payload), Stop }
        fn main() -> u32 {
            let a: Action = Action::Run(Payload { value: 42u32 });
            match a {
                whole @ Action::Run(p) => 7u32,
                _ => 0u32,
            }
        }
    "#;

    let body = lowered_main(source);

    // The inner `p` binding observes the value via a shared borrow.
    let has_shared_ref = body.blocks.iter().any(|block| {
        block.statements.iter().any(|stmt| {
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
        has_shared_ref,
        "the inner sub-binding of `whole @ Action::Run(p)` should be bound by shared reference"
    );

    // The outer `whole` binding still moves the whole non-Copy value.
    let has_move_use = body.blocks.iter().any(|block| {
        block.statements.iter().any(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    rvalue: Rvalue::Use(Operand::Move(_)),
                    ..
                }
            )
        })
    });
    assert!(
        has_move_use,
        "the outer `whole` binding should move the whole non-Copy value"
    );
    assert!(
        !matches!(body.blocks[0].terminator, Term::Unreachable),
        "`whole @ Action::Run(p)` should lower successfully"
    );
}

/// `name @ subpattern` over a *Copy* scrutinee keeps the cheaper by-value path:
/// no shared borrow is needed because each binding is an independent copy.
#[test]
fn test_at_binding_copy_scrutinee_stays_by_value_no_regression() {
    let source = r#"
        fn main() -> u32 {
            let n: u32 = 5u32;
            match n {
                whole @ 5u32 => whole,
                _ => 0u32,
            }
        }
    "#;

    let body = lowered_main(source);

    // Copy `@` binding should not introduce a shared reference for the binding.
    let has_shared_ref = body.blocks.iter().any(|block| {
        block.statements.iter().any(|stmt| {
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
        !has_shared_ref,
        "`@`-binding over a Copy scrutinee should not introduce a shared borrow"
    );
    assert!(
        !matches!(body.blocks[0].terminator, Term::Unreachable),
        "Copy `@`-binding should lower successfully"
    );
}

/// A plain (non-`@`) binding over a non-Copy scrutinee matched behind a
/// reference (`match &v`) binds by reference per default binding modes:
/// the reference scrutinee is Copy, so the binding copies the reference and
/// no move of the underlying non-Copy value occurs.
#[test]
fn test_ref_match_non_copy_binds_by_ref() {
    let source = r#"
        struct Payload { value: u32 }
        fn main() -> u32 {
            let p: Payload = Payload { value: 9u32 };
            let r: &Payload = &p;
            match r {
                bound => 3u32,
            }
        }
    "#;

    let body = lowered_main(source);

    // The scrutinee `r` is a `&Payload` (Copy), so the binding `bound` copies
    // the reference rather than moving the underlying non-Copy `Payload`.
    let has_copy_use = body.blocks.iter().any(|block| {
        block.statements.iter().any(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    rvalue: Rvalue::Use(Operand::Copy(_)),
                    ..
                }
            )
        })
    });
    assert!(
        has_copy_use,
        "binding over a reference scrutinee should copy the reference, not move the value"
    );
    assert!(
        !matches!(body.blocks[0].terminator, Term::Unreachable),
        "reference-scrutinee binding should lower successfully"
    );
}
