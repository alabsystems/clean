// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Slice pattern lowering helpers.
//!
//! Handles `[a, b, .., z]` patterns by emitting length checks and
//! element-wise sub-pattern tests via `Place::Index` projections.

use super::context::FunctionLoweringContext;
use super::VirLoweringError;
use crate::expr::Pattern;
use crate::ownership::Place;
use crate::types::{Mutability, RustType, UintType};
use crate::vir::{
    BasicBlockId, BinOp, Constant, Operand, Rvalue, ScalarValue, Stmt as VirStmt, SwitchTargets,
    Term,
};

impl<'a> FunctionLoweringContext<'a> {
    pub(super) fn lower_slice_pattern_test(
        &mut self,
        scrutinee: Place,
        patterns: &[Pattern],
        success_block: BasicBlockId,
        failure_block: BasicBlockId,
    ) -> Result<(), VirLoweringError> {
        let usize_ty = RustType::Uint(UintType::Usize);

        // Get the length of the scrutinee array/slice.
        let len_local = self.alloc_local(None, usize_ty.clone(), Mutability::Mutable);
        self.emit(VirStmt::Assign {
            place: Place::Local(len_local),
            rvalue: Rvalue::Len(scrutinee.clone()),
        });

        let rest_pos = patterns.iter().position(|p| matches!(p, Pattern::Rest));

        let (required_len, cmp_op) = match rest_pos {
            None => (patterns.len(), BinOp::Eq),
            Some(pos) => {
                let prefix_len = pos;
                let suffix_len = patterns.len() - pos - 1;
                (prefix_len + suffix_len, BinOp::Ge)
            }
        };

        // Emit length check: len == N (exact) or len >= N (rest).
        let len_ok = self.alloc_local(None, RustType::Bool, Mutability::Mutable);
        self.emit(VirStmt::Assign {
            place: Place::Local(len_ok),
            rvalue: Rvalue::BinaryOp {
                op: cmp_op,
                lhs: Operand::Copy(Place::Local(len_local)),
                rhs: Operand::Constant(Constant::Scalar(ScalarValue::Uint(required_len as u128))),
            },
        });

        let length_ok_block = self.new_block(Term::Unreachable);
        let mut targets = SwitchTargets::new(failure_block);
        targets.add(1, length_ok_block);
        self.current_block_mut().terminator = Term::SwitchInt {
            discriminant: Operand::Copy(Place::Local(len_ok)),
            targets,
        };

        // Now in length_ok_block, test each element sub-pattern.
        self.switch_to_block(length_ok_block);

        let prefix_patterns: &[Pattern];
        let suffix_patterns: &[Pattern];
        match rest_pos {
            None => {
                prefix_patterns = patterns;
                suffix_patterns = &[];
            }
            Some(pos) => {
                prefix_patterns = &patterns[..pos];
                suffix_patterns = &patterns[pos + 1..];
            }
        }

        // Collect all non-trivial (non-wildcard, non-rest) element tests.
        let mut element_tests: Vec<(Place, &Pattern)> = Vec::new();

        // Prefix elements: index 0, 1, 2, ...
        for (i, subpat) in prefix_patterns.iter().enumerate() {
            if matches!(subpat, Pattern::Wildcard | Pattern::Rest) {
                continue;
            }
            let idx_local = self.alloc_local(None, usize_ty.clone(), Mutability::Mutable);
            self.emit(VirStmt::Assign {
                place: Place::Local(idx_local),
                rvalue: Rvalue::Use(Operand::Constant(Constant::Scalar(ScalarValue::Uint(
                    i as u128,
                )))),
            });
            let elem_place = Place::Index {
                base: Box::new(scrutinee.clone()),
                index: Box::new(Place::Local(idx_local)),
            };
            element_tests.push((elem_place, subpat));
        }

        // Suffix elements: index len - reverse_offset.
        for (j, subpat) in suffix_patterns.iter().enumerate() {
            if matches!(subpat, Pattern::Wildcard | Pattern::Rest) {
                continue;
            }
            let reverse_offset = suffix_patterns.len() - j;
            let idx_local = self.alloc_local(None, usize_ty.clone(), Mutability::Mutable);
            self.emit(VirStmt::Assign {
                place: Place::Local(idx_local),
                rvalue: Rvalue::BinaryOp {
                    op: BinOp::Sub,
                    lhs: Operand::Copy(Place::Local(len_local)),
                    rhs: Operand::Constant(Constant::Scalar(ScalarValue::Uint(
                        reverse_offset as u128,
                    ))),
                },
            });
            let elem_place = Place::Index {
                base: Box::new(scrutinee.clone()),
                index: Box::new(Place::Local(idx_local)),
            };
            element_tests.push((elem_place, subpat));
        }

        if element_tests.is_empty() {
            self.current_block_mut().terminator = Term::Goto {
                target: success_block,
                args: vec![],
            };
            return Ok(());
        }

        // Chain sub-pattern tests sequentially.
        let mut current_block = self.current_block_id();
        for (i, (elem_place, subpat)) in element_tests.iter().enumerate() {
            self.switch_to_block(current_block);
            let next_success = if i + 1 == element_tests.len() {
                success_block
            } else {
                self.new_block(Term::Unreachable)
            };
            self.lower_pattern_test(elem_place.clone(), subpat, next_success, failure_block)?;
            current_block = next_success;
        }

        Ok(())
    }
}

#[cfg(test)]
mod range_slice_tests {
    //! Range-indexing (`a[1..3]`, `a[..]`, ...) lowering tests.
    //!
    //! Slicing borrows the *whole* container (the `Index::index` desugaring
    //! takes `&self`), so the sound over-approximation models the sliced place
    //! as the entire base local. These tests pin (1) that slicing now lowers
    //! without `Unsupported`, (2) that the borrow it creates targets the whole
    //! base, and (3) that a `&mut` slice borrow held live across a conflicting
    //! access is flagged.

    use crate::expr::{Expr, Stmt as AstStmt};
    use crate::nll::{check_body, NllError};
    use crate::ownership::Place;
    use crate::types::{Lifetime, Mutability, RustType, UintType};
    use crate::values::Value;
    use crate::vir::{Body, Rvalue, Stmt as VirStmt};
    use crate::vir_lowering::context::lower_function_with_closures;
    use crate::vir_lowering::ProgramSymbols;

    fn u32_ty() -> RustType {
        RustType::Uint(UintType::U32)
    }

    fn vec_u32_ty() -> RustType {
        RustType::Vec {
            element: Box::new(u32_ty()),
        }
    }

    fn shared_slice_u32_ty() -> RustType {
        RustType::Reference {
            lifetime: Lifetime::Anonymous(0),
            mutability: Mutability::Shared,
            inner: Box::new(RustType::Slice {
                elem: Box::new(u32_ty()),
            }),
        }
    }

    fn mut_slice_u32_ty() -> RustType {
        RustType::Reference {
            lifetime: Lifetime::Anonymous(0),
            mutability: Mutability::Mutable,
            inner: Box::new(RustType::Slice {
                elem: Box::new(u32_ty()),
            }),
        }
    }

    fn var(name: &str) -> Expr {
        Expr::Var {
            name: name.to_string(),
            local_idx: 0,
        }
    }

    /// `&v[start..end]` over the variable `v`, with `inclusive` controlling
    /// `..` vs `..=`. Either bound may be omitted to model open ranges.
    fn slice_borrow(
        v: &str,
        mutability: Mutability,
        start: Option<u32>,
        end: Option<u32>,
        inclusive: bool,
    ) -> Expr {
        Expr::AddrOf {
            mutability,
            expr: Box::new(Expr::Index {
                base: Box::new(var(v)),
                index: Box::new(Expr::Range {
                    start: start.map(|s| Box::new(Expr::Literal(Value::usize(s as usize)))),
                    end: end.map(|e| Box::new(Expr::Literal(Value::usize(e as usize)))),
                    inclusive,
                }),
            }),
        }
    }

    fn lower_body(params: &[(String, RustType)], body: Expr) -> Body {
        let symbols = ProgramSymbols::default();
        let (lowered, _) =
            lower_function_with_closures("test_fn", params, &RustType::Unit, &body, &symbols)
                .expect("range-slice body should lower to VIR");
        lowered
    }

    /// True if the body contains a `Rvalue::Ref` borrowing exactly `place`.
    fn borrows_place(body: &Body, place: &Place) -> bool {
        body.blocks.iter().any(|block| {
            block.statements.iter().any(|stmt| {
                matches!(
                    stmt,
                    VirStmt::Assign {
                        rvalue: Rvalue::Ref { place: borrowed, .. },
                        ..
                    } if borrowed == place
                )
            })
        })
    }

    /// `let s = &v[1..3];` lowers without `Unsupported` and the borrow targets
    /// the whole base container `v` (parameter local 1), not a single element.
    #[test]
    fn test_slice_index_borrows_whole_base() {
        let body = lower_body(
            &[("v".to_string(), vec_u32_ty())],
            Expr::Block {
                stmts: vec![AstStmt::Let {
                    pattern: crate::expr::Pattern::Binding {
                        name: "s".to_string(),
                        mutable: false,
                        subpattern: None,
                    },
                    ty: Some(shared_slice_u32_ty()),
                    init: Some(Box::new(slice_borrow(
                        "v",
                        Mutability::Shared,
                        Some(1),
                        Some(3),
                        false,
                    ))),
                    else_block: None,
                }],
                expr: None,
            },
        );

        assert!(
            borrows_place(&body, &Place::Local(1)),
            "a slice borrow `&v[1..3]` must borrow the whole base local `v`, body: {body:?}"
        );
    }

    /// Open ranges (`v[..]`, `v[2..]`, `v[..5]`, `v[1..=3]`) all lower and
    /// borrow the whole base.
    #[test]
    fn test_open_range_slices_borrow_whole_base() {
        for (start, end, inclusive) in [
            (None, None, false),      // v[..]
            (Some(2), None, false),   // v[2..]
            (None, Some(5), false),   // v[..5]
            (Some(1), Some(3), true), // v[1..=3]
        ] {
            let body = lower_body(
                &[("v".to_string(), vec_u32_ty())],
                Expr::Block {
                    stmts: vec![AstStmt::Let {
                        pattern: crate::expr::Pattern::Binding {
                            name: "s".to_string(),
                            mutable: false,
                            subpattern: None,
                        },
                        ty: Some(shared_slice_u32_ty()),
                        init: Some(Box::new(slice_borrow(
                            "v",
                            Mutability::Shared,
                            start,
                            end,
                            inclusive,
                        ))),
                        else_block: None,
                    }],
                    expr: None,
                },
            );
            assert!(
                borrows_place(&body, &Place::Local(1)),
                "open-range slice (start={start:?}, end={end:?}, inclusive={inclusive}) must borrow whole base"
            );
        }
    }

    /// A `&mut v[1..]` borrow held live across a shared borrow of `v` is a
    /// conflicting borrow: because the slice covers the whole container, the
    /// later `&v` access must be flagged (sound use-after-invalidation).
    #[test]
    fn test_mut_slice_borrow_conflicts_with_later_use() {
        // {
        //   let r = &mut v[1..];   // mut borrow of the whole v, live below
        //   let _b = &v;           // shared borrow of v while r is live -> conflict
        //   let _u = r;            // move r: keeps the mut borrow live across `_b`
        // }
        let body = lower_body(
            &[("v".to_string(), vec_u32_ty())],
            Expr::Block {
                stmts: vec![
                    AstStmt::Let {
                        pattern: crate::expr::Pattern::Binding {
                            name: "r".to_string(),
                            mutable: false,
                            subpattern: None,
                        },
                        ty: Some(mut_slice_u32_ty()),
                        init: Some(Box::new(slice_borrow(
                            "v",
                            Mutability::Mutable,
                            Some(1),
                            None,
                            false,
                        ))),
                        else_block: None,
                    },
                    AstStmt::Let {
                        pattern: crate::expr::Pattern::Binding {
                            name: "_b".to_string(),
                            mutable: false,
                            subpattern: None,
                        },
                        ty: Some(RustType::Reference {
                            lifetime: Lifetime::Anonymous(0),
                            mutability: Mutability::Shared,
                            inner: Box::new(vec_u32_ty()),
                        }),
                        init: Some(Box::new(Expr::AddrOf {
                            mutability: Mutability::Shared,
                            expr: Box::new(var("v")),
                        })),
                        else_block: None,
                    },
                    AstStmt::Let {
                        pattern: crate::expr::Pattern::Binding {
                            name: "_u".to_string(),
                            mutable: false,
                            subpattern: None,
                        },
                        ty: Some(mut_slice_u32_ty()),
                        init: Some(Box::new(var("r"))),
                        else_block: None,
                    },
                ],
                expr: None,
            },
        );

        let result = check_body(&body);
        assert!(
            result
                .errors
                .iter()
                .any(|err| matches!(err, NllError::ConflictingBorrow { .. })),
            "a `&mut v[1..]` borrow held live across `&v` must conflict, got: {:?}",
            result.errors
        );
    }

    /// A function whose body returns `&v[..]` lowers end-to-end and
    /// borrow-checks without panicking.
    #[test]
    fn test_slice_function_lowers_end_to_end() {
        let symbols = ProgramSymbols::default();
        let body_expr = Expr::Block {
            stmts: vec![],
            expr: Some(Box::new(slice_borrow(
                "v",
                Mutability::Shared,
                None,
                None,
                false,
            ))),
        };
        let (body, _) = lower_function_with_closures(
            "slice_all",
            &[("v".to_string(), vec_u32_ty())],
            &shared_slice_u32_ty(),
            &body_expr,
            &symbols,
        )
        .expect("a function returning `&v[..]` must lower end-to-end");

        // The return place (local 0) is assigned a borrow of the whole base `v`.
        assert!(
            borrows_place(&body, &Place::Local(1)),
            "the returned slice borrow must target the whole base local `v`"
        );
        // Borrow checking runs without panicking on the lowered body.
        let _ = check_body(&body);
    }
}
