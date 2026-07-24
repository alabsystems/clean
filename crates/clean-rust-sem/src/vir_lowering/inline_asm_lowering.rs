// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lowering of inline-assembly (`asm!`) expressions to VIR.
//!
//! Inline assembly is opaque to the verifier: it may read its inputs, write
//! arbitrary values into its outputs and clobbered registers, and — unless it
//! is declared `nomem` — read or write any reachable memory. To stay sound we
//! *over-approximate* every one of these effects:
//!
//! 1. **Inputs** (`in` / `inout` in-exprs) are materialized as operands so any
//!    reads/moves they perform are tracked by ownership and borrow analysis.
//! 2. **Outputs** (`out` / `lateout` / `inout` out-exprs) are *havocked*: the
//!    bound place is assigned a fresh nondeterministic value
//!    ([`Rvalue::Opaque`]). A still-live borrow of that place therefore
//!    conflicts with the write, exactly as a use-after-asm would.
//! 3. **Memory** (everything reachable, unless `options(nomem)`) is havocked by
//!    assigning a fresh nondeterministic value to every local that exists at
//!    the point of the asm. This forgets any value or borrow that downstream
//!    code might otherwise assume the asm preserved.
//!
//! Over-approximating (havocking too much) can only cost completeness — some
//! true programs become unverifiable. Under-approximating (failing to havoc
//! something the asm could change) would let the verifier assume a stale value
//! and prove a false property, which is unsound. When in doubt we havoc.

use super::context::FunctionLoweringContext;
use super::VirLoweringError;
use crate::expr::{AsmOperand, Expr, InlineAsm};
use crate::ownership::Place;
use crate::types::RustType;
use crate::vir::{LocalId, Rvalue, Stmt as VirStmt};

impl<'a> FunctionLoweringContext<'a> {
    /// Lower an `asm!` expression into VIR with a sound over-approximation of
    /// its read/write/clobber effects (see module docs).
    pub(super) fn lower_inline_asm_expr(
        &mut self,
        destination: Place,
        asm: &InlineAsm,
    ) -> Result<(), VirLoweringError> {
        // Snapshot the locals that exist *before* this asm. These are the
        // places that constitute "reachable memory" from the asm's point of
        // view; the temporaries we allocate below to hold inputs are not part
        // of that pre-existing memory and must not be confused with it.
        let preexisting_locals = self.body.locals.len() as LocalId;

        // (a) Materialize all inputs so their reads/moves are tracked. We do
        // this first: the asm conceptually reads its inputs before producing
        // any output or touching memory.
        for operand in &asm.operands {
            if self.terminated {
                return Ok(());
            }
            match operand {
                AsmOperand::In { expr, .. } => {
                    self.materialize_operand(expr)?;
                }
                AsmOperand::InOut { in_expr, .. } => {
                    self.materialize_operand(in_expr)?;
                }
                AsmOperand::Out { .. } | AsmOperand::Const(_) | AsmOperand::Sym(_) => {}
            }
        }

        // (c) Unless `nomem`, the asm may write any reachable memory. Havoc the
        // *owned* memory held by every pre-existing local so no downstream
        // value or borrow is assumed preserved across the asm.
        //
        // We deliberately skip reference- and raw-pointer-typed locals: the asm
        // clobbers the *memory a pointer refers to*, not which object a pointer
        // variable holds. That pointee memory is itself an owned local (or a
        // place reachable from one), which this loop already havocs directly —
        // so a borrow `r = &mut x` whose referent `x` is havocked here is
        // correctly invalidated, while `r` stays live (so the borrow remains
        // active at the clobber point and the conflict is reported). Havocking
        // the reference local instead would both mis-model asm semantics and
        // sever the borrow's liveness, hiding the very conflict we must report.
        if !asm.options.nomem {
            for local in 0..preexisting_locals {
                if self.terminated {
                    return Ok(());
                }
                if self.local_holds_pointer(local) {
                    continue;
                }
                self.havoc_local(local)?;
            }
        }

        // (b) Havoc every output place (`out` / `lateout` / `inout` out-expr).
        // This runs after the memory havoc so that an output place is left in a
        // havocked-but-defined state regardless of whether `nomem` was set.
        for operand in &asm.operands {
            if self.terminated {
                return Ok(());
            }
            let out_expr = match operand {
                AsmOperand::Out {
                    expr: Some(expr), ..
                }
                | AsmOperand::InOut {
                    out_expr: Some(expr),
                    ..
                } => Some(expr),
                // `inout(reg) x` (no `=> dst`) writes back into the input
                // place `x`; havoc it too.
                AsmOperand::InOut {
                    in_expr,
                    out_expr: None,
                    ..
                } => Some(in_expr),
                _ => None,
            };
            if let Some(out_expr) = out_expr {
                self.havoc_place_expr(out_expr)?;
            }
        }

        // The `asm!` expression itself evaluates to `()`.
        self.assign_unit(destination)
    }

    /// Havoc a place referred to by an output operand expression: assign it a
    /// fresh nondeterministic value of its own type.
    fn havoc_place_expr(&mut self, expr: &Expr) -> Result<(), VirLoweringError> {
        // `_` outputs (discarded) have no place to write; skip them. They are
        // represented as a missing operand expression and never reach here.
        let place = self.lower_place_or_temp(expr)?;
        if self.terminated {
            return Ok(());
        }
        let ty = self.place_type(&place)?;
        self.emit(VirStmt::Assign {
            place,
            rvalue: Rvalue::Opaque { ty },
        });
        Ok(())
    }

    /// Havoc a single local: assign it a fresh nondeterministic value of its
    /// declared type.
    fn havoc_local(&mut self, local: LocalId) -> Result<(), VirLoweringError> {
        let ty = self.local_ty(local)?;
        self.emit(VirStmt::Assign {
            place: Place::Local(local),
            rvalue: Rvalue::Opaque { ty },
        });
        Ok(())
    }

    /// True if `local` holds a reference or raw pointer (not owned data).
    fn local_holds_pointer(&self, local: LocalId) -> bool {
        matches!(
            self.local_ty(local),
            Ok(RustType::Reference { .. } | RustType::RawPtr { .. })
        )
    }
}

#[cfg(test)]
mod tests {
    use crate::expr::{AsmOperand, AsmOptions, Expr, InlineAsm, Stmt as AstStmt};
    use crate::nll::{check_body, NllError};
    use crate::ownership::Place;
    use crate::types::{Mutability, RustType, UintType};
    use crate::values::Value;
    use crate::vir::{Body, Rvalue, Stmt as VirStmt};
    use crate::vir_lowering::context::lower_function_with_closures;
    use crate::vir_lowering::ProgramSymbols;

    fn u32_ty() -> RustType {
        RustType::Uint(UintType::U32)
    }

    fn var(name: &str) -> Expr {
        Expr::Var {
            name: name.to_string(),
            local_idx: 0,
        }
    }

    /// Lower a unit-returning function body, returning the VIR body.
    fn lower_body(params: &[(String, RustType)], body: Expr) -> Body {
        let symbols = ProgramSymbols::default();
        let (lowered, _) =
            lower_function_with_closures("test_fn", params, &RustType::Unit, &body, &symbols)
                .expect("inline-asm body should lower to VIR");
        lowered
    }

    /// True if any statement in the body havocs (assigns `Rvalue::Opaque` to)
    /// the given place.
    fn havocs_place(body: &Body, place: &Place) -> bool {
        body.blocks.iter().any(|block| {
            block.statements.iter().any(|stmt| {
                matches!(
                    stmt,
                    VirStmt::Assign {
                        place: assigned,
                        rvalue: Rvalue::Opaque { .. },
                    } if assigned == place
                )
            })
        })
    }

    /// `asm!("...", out(reg) dst, in(reg) src, options(nomem))` lowers without
    /// error and havocs the output place `dst`.
    #[test]
    fn test_inline_asm_in_out_lowers_and_havocs_output() {
        let asm = Expr::InlineAsm(InlineAsm {
            template: "mov {0}, {1}".to_string(),
            operands: vec![
                AsmOperand::Out {
                    constraint: "reg".to_string(),
                    expr: Some(var("dst")),
                },
                AsmOperand::In {
                    constraint: "reg".to_string(),
                    expr: var("src"),
                },
            ],
            options: AsmOptions {
                nomem: true,
                ..AsmOptions::default()
            },
            clobbers: vec![],
        });

        let body = lower_body(
            &[("dst".to_string(), u32_ty()), ("src".to_string(), u32_ty())],
            asm,
        );

        // `dst` is parameter local 1 (local 0 is the return place).
        assert!(
            havocs_place(&body, &Place::Local(1)),
            "out(reg) dst must be havocked with a fresh nondeterministic value"
        );
    }

    /// A `&mut` borrow that survives a non-`nomem` asm is invalidated: the asm
    /// havocs the borrowed memory while the borrow is still live, so using the
    /// borrow afterwards is flagged.
    #[test]
    fn test_inline_asm_clobbering_invalidates_surviving_borrow() {
        // {
        //   let mut x = 1u32;
        //   let r = &x;              // borrow of x, live until read below
        //   asm!("nop");             // non-nomem: havocs x while r is live
        //   let _y: u32 = *r;        // read through r after the clobber
        // }
        //
        // The read of `*r` keeps `r` (and hence the borrow of `x`) live across
        // the asm. The asm havocs `x` directly while that borrow is active, so
        // the verifier must report a conflict.
        let asm = Expr::InlineAsm(InlineAsm {
            template: "nop".to_string(),
            operands: vec![],
            options: AsmOptions::default(),
            clobbers: vec![],
        });

        let body = lower_body(
            &[],
            Expr::Block {
                stmts: vec![
                    AstStmt::Let {
                        pattern: crate::expr::Pattern::Binding {
                            name: "x".to_string(),
                            mutable: true,
                            subpattern: None,
                        },
                        ty: Some(u32_ty()),
                        init: Some(Box::new(Expr::Literal(Value::u32(1)))),
                        else_block: None,
                    },
                    AstStmt::Let {
                        pattern: crate::expr::Pattern::Binding {
                            name: "r".to_string(),
                            mutable: false,
                            subpattern: None,
                        },
                        ty: None,
                        init: Some(Box::new(Expr::AddrOf {
                            mutability: Mutability::Shared,
                            expr: Box::new(var("x")),
                        })),
                        else_block: None,
                    },
                    AstStmt::Expr(asm),
                    AstStmt::Let {
                        pattern: crate::expr::Pattern::Binding {
                            name: "_y".to_string(),
                            mutable: false,
                            subpattern: None,
                        },
                        ty: Some(u32_ty()),
                        init: Some(Box::new(Expr::Deref(Box::new(var("r"))))),
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
                .any(|err| matches!(err, NllError::AssignWhileBorrowed { .. })),
            "a borrow surviving a non-nomem asm must be invalidated by the memory havoc, got: {:?}",
            result.errors
        );
    }

    /// A `nomem` asm does not havoc unrelated memory: an unrelated local is not
    /// assigned a fresh value, so a borrow surviving the asm is fine.
    #[test]
    fn test_inline_asm_nomem_preserves_unrelated_memory() {
        // Same shape as the clobbering test, but with options(nomem). The
        // borrowed place must NOT be havocked, so no conflict is reported.
        let asm = Expr::InlineAsm(InlineAsm {
            template: "nop".to_string(),
            operands: vec![],
            options: AsmOptions {
                nomem: true,
                ..AsmOptions::default()
            },
            clobbers: vec![],
        });

        let body = lower_body(
            &[],
            Expr::Block {
                stmts: vec![
                    AstStmt::Let {
                        pattern: crate::expr::Pattern::Binding {
                            name: "x".to_string(),
                            mutable: true,
                            subpattern: None,
                        },
                        ty: Some(u32_ty()),
                        init: Some(Box::new(Expr::Literal(Value::u32(1)))),
                        else_block: None,
                    },
                    AstStmt::Let {
                        pattern: crate::expr::Pattern::Binding {
                            name: "r".to_string(),
                            mutable: false,
                            subpattern: None,
                        },
                        ty: None,
                        init: Some(Box::new(Expr::AddrOf {
                            mutability: Mutability::Shared,
                            expr: Box::new(var("x")),
                        })),
                        else_block: None,
                    },
                    AstStmt::Expr(asm),
                    AstStmt::Let {
                        pattern: crate::expr::Pattern::Binding {
                            name: "_y".to_string(),
                            mutable: false,
                            subpattern: None,
                        },
                        ty: Some(u32_ty()),
                        init: Some(Box::new(Expr::Deref(Box::new(var("r"))))),
                        else_block: None,
                    },
                ],
                expr: None,
            },
        );

        // No Opaque assignment to any local: nomem suppressed the memory havoc.
        let has_opaque = body.blocks.iter().any(|block| {
            block.statements.iter().any(|stmt| {
                matches!(
                    stmt,
                    VirStmt::Assign {
                        rvalue: Rvalue::Opaque { .. },
                        ..
                    }
                )
            })
        });
        assert!(
            !has_opaque,
            "a nomem asm with no outputs must not havoc any memory"
        );

        let result = check_body(&body);
        assert!(
            !result
                .errors
                .iter()
                .any(|err| matches!(err, NllError::AssignWhileBorrowed { .. })),
            "a nomem asm must not invalidate an unrelated surviving borrow, got: {:?}",
            result.errors
        );
    }

    /// A function whose body is an `asm!` lowers end-to-end without error.
    #[test]
    fn test_inline_asm_function_lowers_end_to_end() {
        let asm = Expr::InlineAsm(InlineAsm {
            template: "add {0}, {1}".to_string(),
            operands: vec![
                AsmOperand::InOut {
                    constraint: "reg".to_string(),
                    in_expr: var("acc"),
                    out_expr: Some(var("acc")),
                },
                AsmOperand::In {
                    constraint: "reg".to_string(),
                    expr: var("addend"),
                },
            ],
            options: AsmOptions::default(),
            clobbers: vec!["rax".to_string()],
        });

        let body = lower_body(
            &[
                ("acc".to_string(), u32_ty()),
                ("addend".to_string(), u32_ty()),
            ],
            Expr::Block {
                stmts: vec![AstStmt::Expr(asm)],
                expr: None,
            },
        );

        // `acc` (the inout output, local 1) is havocked.
        assert!(
            havocs_place(&body, &Place::Local(1)),
            "inout output `acc` must be havocked"
        );
        // Borrow checking runs without panicking on the lowered body.
        let _ = check_body(&body);
    }
}
