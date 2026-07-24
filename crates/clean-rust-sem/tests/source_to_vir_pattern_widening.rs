// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for pattern and expression widening in VIR lowering.

use clean_rust_sem::vir::{AggregateKind, BinOp, Term};
use clean_rust_sem::{Operand, Place, RustType, Rvalue, SourceProgram, Stmt, UintType};

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

fn borrow_result_for_main(source: &str) -> clean_rust_sem::NllResult {
    let program = SourceProgram::parse(source).expect("source should parse");
    let mut analyses = program
        .check_borrows()
        .expect("source should lower and run NLL");
    analyses
        .remove("main")
        .expect("borrow analyses should contain `main`")
}

fn local_id(body: &clean_rust_sem::Body, name: &str) -> u32 {
    body.locals
        .iter()
        .enumerate()
        .find_map(|(idx, decl)| (decl.name.as_deref() == Some(name)).then_some(idx as u32))
        .expect("named local should exist")
}

#[test]
fn test_struct_pattern_destructures_named_fields() {
    let source = r#"
        struct Point { x: u32, y: u32 }
        fn main() -> u32 {
            let p = Point { x: 3u32, y: 7u32 };
            let Point { x, y } = p;
            x + y
        }
    "#;

    let body = lowered_main(source);
    let x_local = local_id(&body, "x");
    let y_local = local_id(&body, "y");

    let has_x = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .any(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    place: Place::Local(dst),
                    rvalue: Rvalue::Use(Operand::Copy(Place::Field { field, .. })
                        | Operand::Move(Place::Field { field, .. })),
                } if *dst == x_local && field == "x"
            )
        });
    let has_y = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .any(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    place: Place::Local(dst),
                    rvalue: Rvalue::Use(Operand::Copy(Place::Field { field, .. })
                        | Operand::Move(Place::Field { field, .. })),
                } if *dst == y_local && field == "y"
            )
        });

    assert!(has_x, "struct destructuring should bind `x` from field `x`");
    assert!(has_y, "struct destructuring should bind `y` from field `y`");

    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "struct destructuring should keep the lowered CFG NLL-clean: {:?}",
        result.errors
    );
}

#[test]
fn test_match_struct_pattern_binds_fields_in_arm() {
    let source = r#"
        struct Pair { a: u32, b: u32 }
        fn main() -> u32 {
            let p = Pair { a: 10u32, b: 20u32 };
            match p {
                Pair { a, b } => a + b,
            }
        }
    "#;

    let body = lowered_main(source);
    assert!(
        body.locals
            .iter()
            .any(|decl| decl.name.as_deref() == Some("a")),
        "struct pattern in match arm should bind `a`"
    );
    assert!(
        body.locals
            .iter()
            .any(|decl| decl.name.as_deref() == Some("b")),
        "struct pattern in match arm should bind `b`"
    );

    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "struct match pattern should stay NLL-clean: {:?}",
        result.errors
    );
}

#[test]
fn test_match_enum_tuple_variant_tests_discriminant_and_binds_payload() {
    let source = r#"
        enum OptionU32 {
            None,
            Some(u32),
        }

        fn main() -> u32 {
            let opt = OptionU32::Some(9u32);
            match opt {
                OptionU32::Some(x) => x,
                OptionU32::None => 0u32,
            }
        }
    "#;

    let body = lowered_main(source);
    let opt_local = local_id(&body, "opt");
    let x_local = local_id(&body, "x");

    let has_enum_aggregate = body.blocks.iter().flat_map(|bb| bb.statements.iter()).any(|stmt| {
        matches!(
            stmt,
            Stmt::Assign {
                place: Place::Local(dst),
                rvalue: Rvalue::Aggregate {
                    kind: AggregateKind::Adt { name, variant_index },
                    operands,
                },
            } if *dst == opt_local && name == "OptionU32" && *variant_index == 1 && operands.len() == 1
        )
    });
    assert!(
        has_enum_aggregate,
        "tuple enum constructor should lower through AggregateKind::Adt for `OptionU32::Some`"
    );

    // The match lowering moves the scrutinee into a temporary local before
    // reading the discriminant, so we check for discriminant on ANY local.
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
        "enum match should test the scrutinee discriminant"
    );

    // The payload binding projects through Downcast { variant: "Some" } then
    // Field { field: "0" }. The downcast base is the scrutinee temporary.
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
                if *dst == x_local
                    && field == "0"
                    && matches!(
                        base.as_ref(),
                        Place::Downcast { variant, .. }
                        if variant == "Some"
                    )
            )
        });
    assert!(
        has_payload_binding,
        "enum tuple pattern should bind through a downcast field projection"
    );

    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "enum tuple pattern lowering should stay NLL-clean: {:?}",
        result.errors
    );
}

#[test]
fn test_match_enum_struct_variant_binds_named_fields() {
    let source = r#"
        enum Message {
            Quit,
            Move { x: u32, y: u32 },
        }

        fn main() -> u32 {
            let msg = Message::Move { y: 7u32, x: 3u32 };
            match msg {
                Message::Move { x, y } => x + y,
                Message::Quit => 0u32,
            }
        }
    "#;

    let body = lowered_main(source);
    let msg_local = local_id(&body, "msg");
    let x_local = local_id(&body, "x");
    let y_local = local_id(&body, "y");

    let has_enum_aggregate = body.blocks.iter().flat_map(|bb| bb.statements.iter()).any(|stmt| {
        matches!(
            stmt,
            Stmt::Assign {
                place: Place::Local(dst),
                rvalue: Rvalue::Aggregate {
                    kind: AggregateKind::Adt { name, variant_index },
                    operands,
                },
            } if *dst == msg_local && name == "Message" && *variant_index == 1 && operands.len() == 2
        )
    });
    assert!(
        has_enum_aggregate,
        "struct enum constructor should lower through AggregateKind::Adt for `Message::Move`"
    );

    // The downcast base is the scrutinee temporary (not msg_local directly),
    // so we check for the variant name without constraining the base local.
    let has_x_binding = body
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
                if *dst == x_local
                    && field == "x"
                    && matches!(
                        base.as_ref(),
                        Place::Downcast { variant, .. }
                        if variant == "Move"
                    )
            )
        });
    let has_y_binding = body
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
                if *dst == y_local
                    && field == "y"
                    && matches!(
                        base.as_ref(),
                        Place::Downcast { variant, .. }
                        if variant == "Move"
                    )
            )
        });
    assert!(
        has_x_binding,
        "struct enum pattern should bind `x` from the downcast payload"
    );
    assert!(
        has_y_binding,
        "struct enum pattern should bind `y` from the downcast payload"
    );

    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "enum struct pattern lowering should stay NLL-clean: {:?}",
        result.errors
    );
}

#[test]
fn test_or_pattern_in_match_tries_alternatives() {
    let source = r#"
        fn main() -> u32 {
            let tag: u32 = 2u32;
            match tag {
                1u32 | 2u32 | 3u32 => 42u32,
                _ => 0u32,
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
        switch_count >= 3,
        "or-pattern with 3 literal alternatives should emit at least 3 SwitchInt tests, got {switch_count}"
    );

    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "or-pattern lowering should stay NLL-clean: {:?}",
        result.errors
    );
}

#[test]
fn test_range_pattern_in_match_produces_bounds_test() {
    let source = r#"
        fn main() -> u32 {
            let x: u32 = 5u32;
            match x {
                0u32..=10u32 => 1u32,
                _ => 0u32,
            }
        }
    "#;

    let body = lowered_main(source);
    let has_ge = body.blocks.iter().any(|bb| {
        bb.statements.iter().any(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    rvalue: Rvalue::BinaryOp { op: BinOp::Ge, .. },
                    ..
                }
            )
        })
    });
    assert!(
        has_ge,
        "range pattern should emit a GE comparison for the lower bound"
    );

    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "range pattern lowering should stay NLL-clean: {:?}",
        result.errors
    );
}

#[test]
fn test_unsafe_block_lowers_through_inner_block() {
    let source = r#"
        fn main() -> u32 {
            unsafe { 42u32 }
        }
    "#;

    let body = lowered_main(source);
    let has_constant = body.blocks.iter().any(|bb| {
        bb.statements.iter().any(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    place: Place::Local(0),
                    rvalue: Rvalue::Use(Operand::Constant(_)),
                }
            )
        })
    });
    assert!(
        has_constant,
        "unsafe block should lower its inner expression normally"
    );
}

#[test]
fn test_panic_expr_terminates_with_unreachable() {
    let source = r#"
        fn main() -> u32 {
            let x: u32 = 1u32;
            if x == 0u32 {
                panic!("zero");
            } else {
                x
            }
        }
    "#;

    let body = lowered_main(source);
    let unreachable_count = body
        .blocks
        .iter()
        .filter(|bb| matches!(bb.terminator, Term::Unreachable))
        .count();
    assert!(
        unreachable_count >= 1,
        "panic expression should produce at least 1 Unreachable terminator, got {unreachable_count}"
    );
}

#[test]
fn test_array_repeat_lowers_to_array_aggregate() {
    let source = r#"
        fn main() -> u32 {
            let arr: [u32; 3] = [0u32; 3];
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
        .expect("array repeat should lower through AggregateKind::Array with 3 operands");

    assert!(
        matches!(array_assign, Stmt::Assign { .. }),
        "array repeat should produce an aggregate assignment: {array_assign:?}"
    );

    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "array repeat lowering should stay NLL-clean: {:?}",
        result.errors
    );
}

#[test]
fn test_range_expr_lowers_to_adt_aggregate() {
    let source = r#"
        fn main() {
            let r = 0u32..10u32;
        }
    "#;

    let body = lowered_main(source);
    let r_local = local_id(&body, "r");

    let has_range_aggregate = body
        .blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .any(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    place: Place::Local(dst),
                    rvalue: Rvalue::Aggregate {
                        kind: AggregateKind::Adt { name, variant_index },
                        operands,
                    },
                } if *dst == r_local
                    && name == "Range"
                    && *variant_index == 0
                    && operands.len() == 2
            )
        });
    assert!(
        has_range_aggregate,
        "half-open range should lower through AggregateKind::Adt {{ name: \"Range\" }} with 2 operands"
    );
}

#[test]
fn test_inclusive_range_expr_lowers_to_range_inclusive() {
    let source = r#"
        fn main() {
            let r = 1u32..=5u32;
        }
    "#;

    let body = lowered_main(source);
    let r_local = local_id(&body, "r");

    let has_inclusive_aggregate =
        body.blocks
            .iter()
            .flat_map(|bb| bb.statements.iter())
            .any(|stmt| {
                matches!(
                    stmt,
                    Stmt::Assign {
                        place: Place::Local(dst),
                        rvalue: Rvalue::Aggregate {
                            kind: AggregateKind::Adt { name, variant_index },
                            operands,
                        },
                    } if *dst == r_local
                        && name == "RangeInclusive"
                        && *variant_index == 0
                        && operands.len() == 2
                )
            });
    assert!(
        has_inclusive_aggregate,
        "inclusive range should lower through AggregateKind::Adt {{ name: \"RangeInclusive\" }} with 2 operands"
    );
}

// --- Slice pattern tests ---

#[test]
fn test_slice_pattern_exact_emits_len_check() {
    let source = r#"
        fn main() -> u32 {
            let arr: [u32; 3] = [1u32, 2u32, 3u32];
            match arr {
                [a, _, _] => a,
                _ => 0u32,
            }
        }
    "#;

    let body = lowered_main(source);

    // Should emit Rvalue::Len to check the array length.
    let has_len = body.blocks.iter().any(|bb| {
        bb.statements.iter().any(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    rvalue: Rvalue::Len(_),
                    ..
                }
            )
        })
    });
    assert!(
        has_len,
        "slice pattern should emit Rvalue::Len for length check"
    );

    // Should emit an Eq comparison for exact-length match.
    let has_eq = body.blocks.iter().any(|bb| {
        bb.statements.iter().any(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    rvalue: Rvalue::BinaryOp { op: BinOp::Eq, .. },
                    ..
                }
            )
        })
    });
    assert!(
        has_eq,
        "exact slice pattern should emit BinOp::Eq for length equality check"
    );

    // The bound variable `a` should be assigned via Place::Index.
    let a_local = local_id(&body, "a");
    let has_index_bind = body.blocks.iter().any(|bb| {
        bb.statements.iter().any(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    place: Place::Local(dst),
                    rvalue: Rvalue::Use(
                        Operand::Copy(Place::Index { .. }) | Operand::Move(Place::Index { .. })
                    ),
                } if *dst == a_local
            )
        })
    });
    assert!(
        has_index_bind,
        "slice pattern should bind `a` via Place::Index projection"
    );

    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "exact slice pattern lowering should stay NLL-clean: {:?}",
        result.errors
    );
}

#[test]
fn test_slice_pattern_with_rest_emits_ge_check() {
    let source = r#"
        fn main() -> u32 {
            let arr: [u32; 4] = [10u32, 20u32, 30u32, 40u32];
            match arr {
                [first, .., last] => first + last,
                _ => 0u32,
            }
        }
    "#;

    let body = lowered_main(source);

    // Should emit Rvalue::Len.
    let has_len = body.blocks.iter().any(|bb| {
        bb.statements.iter().any(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    rvalue: Rvalue::Len(_),
                    ..
                }
            )
        })
    });
    assert!(has_len, "rest slice pattern should emit Rvalue::Len");

    // Should emit a Ge comparison (len >= prefix + suffix count).
    let has_ge = body.blocks.iter().any(|bb| {
        bb.statements.iter().any(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    rvalue: Rvalue::BinaryOp { op: BinOp::Ge, .. },
                    ..
                }
            )
        })
    });
    assert!(
        has_ge,
        "rest slice pattern should emit BinOp::Ge for minimum length check"
    );

    // Suffix element `last` should be bound via an index computed with Sub.
    let has_sub = body.blocks.iter().any(|bb| {
        bb.statements.iter().any(|stmt| {
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
        has_sub,
        "rest slice pattern should compute suffix indices via BinOp::Sub"
    );

    // Both `first` and `last` should be bound.
    let first_local = local_id(&body, "first");
    let last_local = local_id(&body, "last");
    let has_first = body.blocks.iter().any(|bb| {
        bb.statements.iter().any(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    place: Place::Local(dst),
                    rvalue: Rvalue::Use(
                        Operand::Copy(Place::Index { .. }) | Operand::Move(Place::Index { .. })
                    ),
                } if *dst == first_local
            )
        })
    });
    let has_last = body.blocks.iter().any(|bb| {
        bb.statements.iter().any(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    place: Place::Local(dst),
                    rvalue: Rvalue::Use(
                        Operand::Copy(Place::Index { .. }) | Operand::Move(Place::Index { .. })
                    ),
                } if *dst == last_local
            )
        })
    });
    assert!(
        has_first,
        "rest slice pattern should bind `first` via Place::Index"
    );
    assert!(
        has_last,
        "rest slice pattern should bind `last` via Place::Index"
    );

    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "rest slice pattern lowering should stay NLL-clean: {:?}",
        result.errors
    );
}

#[test]
fn test_slice_pattern_empty_match_lowers() {
    let source = r#"
        fn main() -> u32 {
            let arr: [u32; 0] = [];
            match arr {
                [] => 42u32,
                _ => 0u32,
            }
        }
    "#;

    let body = lowered_main(source);

    // Empty slice pattern should still emit a Len + Eq check.
    let has_len = body.blocks.iter().any(|bb| {
        bb.statements.iter().any(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    rvalue: Rvalue::Len(_),
                    ..
                }
            )
        })
    });
    assert!(has_len, "empty slice pattern should emit Rvalue::Len");

    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "empty slice pattern lowering should stay NLL-clean: {:?}",
        result.errors
    );
}

#[test]
fn test_slice_pattern_let_destructuring() {
    let source = r#"
        fn main() -> u32 {
            let arr: [u32; 2] = [5u32, 10u32];
            let [x, y] = arr;
            x + y
        }
    "#;

    let body = lowered_main(source);

    // Both `x` and `y` should be bound.
    let x_local = local_id(&body, "x");
    let y_local = local_id(&body, "y");
    let has_x = body.blocks.iter().any(|bb| {
        bb.statements.iter().any(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    place: Place::Local(dst),
                    rvalue: Rvalue::Use(
                        Operand::Copy(Place::Index { .. }) | Operand::Move(Place::Index { .. })
                    ),
                } if *dst == x_local
            )
        })
    });
    let has_y = body.blocks.iter().any(|bb| {
        bb.statements.iter().any(|stmt| {
            matches!(
                stmt,
                Stmt::Assign {
                    place: Place::Local(dst),
                    rvalue: Rvalue::Use(
                        Operand::Copy(Place::Index { .. }) | Operand::Move(Place::Index { .. })
                    ),
                } if *dst == y_local
            )
        })
    });
    assert!(
        has_x,
        "let slice destructuring should bind `x` via Place::Index"
    );
    assert!(
        has_y,
        "let slice destructuring should bind `y` via Place::Index"
    );

    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "let slice destructuring should stay NLL-clean: {:?}",
        result.errors
    );
}
