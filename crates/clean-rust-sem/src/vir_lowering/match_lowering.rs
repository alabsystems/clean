// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Match-expression lowering helpers.

use super::context::FunctionLoweringContext;
use super::ops::constant_from_value;
use super::pattern_binding::tuple_field_place;
use super::type_helpers::{nominal_type_name, pattern_contains_binding, pattern_is_irrefutable};
use super::VirLoweringError;
use crate::expr::{Expr, MatchArm, Pattern};
use crate::ownership::Place;
use crate::types::{Lifetime, Mutability, RustType};
use crate::vir::{
    BasicBlockId, BinOp, BorrowKind, Operand, Rvalue, Stmt as VirStmt, SwitchTargets, Term,
};

impl<'a> FunctionLoweringContext<'a> {
    pub(super) fn lower_match_expr(
        &mut self,
        destination: Place,
        scrutinee: &Expr,
        arms: &[MatchArm],
    ) -> Result<(), VirLoweringError> {
        if arms.is_empty() {
            return Err(VirLoweringError::Unsupported {
                context: "match expression",
                detail: "match lowering requires at least one arm".to_string(),
            });
        }

        let scrutinee_ty = self.infer_expr_type(scrutinee)?;
        let scrutinee_local = self.alloc_local(None, scrutinee_ty.clone(), Mutability::Mutable);
        self.lower_expr_into(
            Place::Local(scrutinee_local),
            scrutinee,
            matches!(scrutinee, Expr::Block { .. }),
        )?;
        // Propagate async metadata so that pattern bindings in arms (via
        // propagate_async_output_metadata) can discover callable/future
        // output types that the scrutinee expression carries.
        if let Some(output_ty) = self.callable_future_output_type_of_expr(scrutinee) {
            self.remember_callable_future_output(scrutinee_local, output_ty);
        }
        if let Some(output_ty) = self.future_output_type_of_expr(scrutinee) {
            self.remember_future_output(scrutinee_local, output_ty);
        }
        if self.terminated {
            return Ok(());
        }

        let merge_block = self.new_block(Term::Unreachable);
        let no_match_block = self.new_block(Term::Unreachable);
        let match_exhaustive = arms
            .last()
            .is_some_and(|arm| arm.guard.is_none() && pattern_is_irrefutable(&arm.pattern));
        let mut test_block = self.current_block_id();

        for arm in arms {
            let arm_block = self.new_block(Term::Unreachable);
            let fallback_block = self.new_block(Term::Unreachable);

            self.switch_to_block(test_block);
            self.lower_pattern_test(
                Place::Local(scrutinee_local),
                &arm.pattern,
                arm_block,
                fallback_block,
            )?;

            if !builtin_try_pattern_can_match(&scrutinee_ty, &arm.pattern) {
                test_block = fallback_block;
                continue;
            }

            self.switch_to_block(arm_block);
            self.lower_match_arm(
                destination.clone(),
                Place::Local(scrutinee_local),
                arm,
                merge_block,
                fallback_block,
            )?;

            test_block = fallback_block;
        }

        if !match_exhaustive {
            self.switch_to_block(test_block);
            self.emit_drop_and_storage_dead(scrutinee_local);
            self.current_block_mut().terminator = Term::Goto {
                target: no_match_block,
                args: vec![],
            };

            self.switch_to_block(no_match_block);
            self.current_block_mut().terminator = Term::Unreachable;
        }

        if self.block_has_predecessor(merge_block) {
            self.switch_to_block(merge_block);
            self.emit_drop_and_storage_dead(scrutinee_local);
        } else {
            self.terminated = true;
        }

        Ok(())
    }

    pub(super) fn lower_pattern_test(
        &mut self,
        scrutinee: Place,
        pattern: &Pattern,
        success_block: BasicBlockId,
        failure_block: BasicBlockId,
    ) -> Result<(), VirLoweringError> {
        match pattern {
            Pattern::Wildcard
            | Pattern::Binding {
                subpattern: None, ..
            } => {
                self.current_block_mut().terminator = Term::Goto {
                    target: success_block,
                    args: vec![],
                };
                Ok(())
            }
            Pattern::Binding {
                subpattern: Some(subpattern),
                ..
            }
            | Pattern::Ref {
                pattern: subpattern,
                ..
            } => self.lower_pattern_test(scrutinee, subpattern, success_block, failure_block),
            Pattern::Tuple(patterns) => {
                let tuple_len = match self.place_type(&scrutinee)? {
                    RustType::Tuple(field_tys) => field_tys.len(),
                    other => {
                        return Err(VirLoweringError::Unsupported {
                            context: "tuple pattern",
                            detail: format!(
                                "tuple pattern requires tuple scrutinee, got `{other:?}`"
                            ),
                        });
                    }
                };
                if tuple_len != patterns.len() {
                    return Err(VirLoweringError::Unsupported {
                        context: "tuple pattern",
                        detail: format!(
                            "tuple pattern arity mismatch: scrutinee has {tuple_len} fields, pattern has {}",
                            patterns.len()
                        ),
                    });
                }
                if patterns.is_empty() {
                    self.current_block_mut().terminator = Term::Goto {
                        target: success_block,
                        args: vec![],
                    };
                    return Ok(());
                }

                let mut current_block = self.current_block_id();
                for (idx, subpattern) in patterns.iter().enumerate() {
                    self.switch_to_block(current_block);
                    let next_success = if idx + 1 == patterns.len() {
                        success_block
                    } else {
                        self.new_block(Term::Unreachable)
                    };
                    self.lower_pattern_test(
                        tuple_field_place(scrutinee.clone(), idx),
                        subpattern,
                        next_success,
                        failure_block,
                    )?;
                    current_block = next_success;
                }
                Ok(())
            }
            Pattern::Literal(value) => {
                let scrutinee_operand = self.match_test_operand(scrutinee)?;
                let test_local = self.alloc_local(None, RustType::Bool, Mutability::Mutable);
                self.emit(VirStmt::Assign {
                    place: Place::Local(test_local),
                    rvalue: Rvalue::BinaryOp {
                        op: BinOp::Eq,
                        lhs: scrutinee_operand,
                        rhs: Operand::Constant(constant_from_value(value)?),
                    },
                });

                let mut targets = SwitchTargets::new(failure_block);
                targets.add(1, success_block);
                self.current_block_mut().terminator = Term::SwitchInt {
                    discriminant: Operand::Copy(Place::Local(test_local)),
                    targets,
                };
                Ok(())
            }
            Pattern::Struct { fields, .. } => {
                // Struct patterns are irrefutable if all field sub-patterns
                // are irrefutable (the struct type itself always matches).
                // Test each field's sub-pattern sequentially.
                if fields.is_empty() {
                    self.current_block_mut().terminator = Term::Goto {
                        target: success_block,
                        args: vec![],
                    };
                    return Ok(());
                }

                let mut current_block = self.current_block_id();
                for (idx, (field_name, subpattern)) in fields.iter().enumerate() {
                    self.switch_to_block(current_block);
                    let next_success = if idx + 1 == fields.len() {
                        success_block
                    } else {
                        self.new_block(Term::Unreachable)
                    };
                    let field_place = Place::Field {
                        base: Box::new(scrutinee.clone()),
                        field: field_name.clone(),
                    };
                    self.lower_pattern_test(field_place, subpattern, next_success, failure_block)?;
                    current_block = next_success;
                }
                Ok(())
            }
            Pattern::EnumVariant {
                enum_name,
                variant,
                payload,
            } => self.lower_enum_pattern_test(
                scrutinee,
                enum_name,
                variant,
                payload,
                success_block,
                failure_block,
            ),
            Pattern::Or(alternatives) => {
                // Or-pattern: try each alternative in sequence; succeed on
                // the first match, fail only if all alternatives fail.
                if alternatives.is_empty() {
                    self.current_block_mut().terminator = Term::Goto {
                        target: failure_block,
                        args: vec![],
                    };
                    return Ok(());
                }

                let mut current_block = self.current_block_id();
                for (idx, alt) in alternatives.iter().enumerate() {
                    self.switch_to_block(current_block);
                    let next_fail = if idx + 1 == alternatives.len() {
                        failure_block
                    } else {
                        self.new_block(Term::Unreachable)
                    };
                    self.lower_pattern_test(scrutinee.clone(), alt, success_block, next_fail)?;
                    current_block = next_fail;
                }
                Ok(())
            }
            Pattern::Range {
                start,
                end,
                inclusive,
            } => {
                // Range pattern: start <= scrutinee && scrutinee <= end (inclusive)
                // or start <= scrutinee && scrutinee < end (exclusive).
                let scrutinee_operand = self.match_test_operand(scrutinee)?;
                let ge_local = self.alloc_local(None, RustType::Bool, Mutability::Mutable);
                self.emit(VirStmt::Assign {
                    place: Place::Local(ge_local),
                    rvalue: Rvalue::BinaryOp {
                        op: BinOp::Ge,
                        lhs: scrutinee_operand.clone(),
                        rhs: Operand::Constant(constant_from_value(start)?),
                    },
                });

                let upper_op = if *inclusive { BinOp::Le } else { BinOp::Lt };
                let le_local = self.alloc_local(None, RustType::Bool, Mutability::Mutable);
                self.emit(VirStmt::Assign {
                    place: Place::Local(le_local),
                    rvalue: Rvalue::BinaryOp {
                        op: upper_op,
                        lhs: scrutinee_operand,
                        rhs: Operand::Constant(constant_from_value(end)?),
                    },
                });

                // AND the two conditions: ge_local && le_local
                let combined = self.alloc_local(None, RustType::Bool, Mutability::Mutable);
                self.emit(VirStmt::Assign {
                    place: Place::Local(combined),
                    rvalue: Rvalue::BinaryOp {
                        op: BinOp::BitAnd,
                        lhs: Operand::Copy(Place::Local(ge_local)),
                        rhs: Operand::Copy(Place::Local(le_local)),
                    },
                });

                let mut targets = SwitchTargets::new(failure_block);
                targets.add(1, success_block);
                self.current_block_mut().terminator = Term::SwitchInt {
                    discriminant: Operand::Copy(Place::Local(combined)),
                    targets,
                };
                Ok(())
            }
            Pattern::Slice(patterns) => {
                self.lower_slice_pattern_test(scrutinee, patterns, success_block, failure_block)
            }
            other => Err(VirLoweringError::Unsupported {
                context: "match pattern",
                detail: format!("pattern lowering is not implemented for `{other:?}`"),
            }),
        }
    }

    fn lower_match_arm(
        &mut self,
        destination: Place,
        scrutinee: Place,
        arm: &MatchArm,
        merge_block: BasicBlockId,
        next_test_block: BasicBlockId,
    ) -> Result<(), VirLoweringError> {
        let scrutinee_ty = self.place_type(&scrutinee)?;
        // Non-Copy scrutinee with guard + bindings: bind by shared reference
        // during guard evaluation so the scrutinee is preserved for subsequent
        // arms if the guard fails.  After the guard passes, rebind by move.
        let ref_guard = arm.guard.is_some()
            && pattern_contains_binding(&arm.pattern)
            && !scrutinee_ty.is_copy();

        self.push_scope();
        if ref_guard {
            self.bind_pattern_by_ref(scrutinee.clone(), &arm.pattern)?;
        } else {
            self.bind_pattern(scrutinee.clone(), &arm.pattern)?;
        }

        if let Some(guard) = &arm.guard {
            let scope_locals = self.current_scope_locals();
            let guard_ty = self.infer_expr_type(guard)?;
            if guard_ty != RustType::Bool {
                return Err(VirLoweringError::Unsupported {
                    context: "match guard",
                    detail: format!("guard must be boolean, got `{guard_ty:?}`"),
                });
            }

            let guard_local = self.alloc_local(None, RustType::Bool, Mutability::Mutable);
            self.lower_expr_into(
                Place::Local(guard_local),
                guard,
                matches!(guard, Expr::Block { .. }),
            )?;
            if self.terminated {
                self.pop_scope();
                return Ok(());
            }

            let body_block = self.new_block(Term::Unreachable);
            let guard_false_block = self.new_block(Term::Unreachable);
            let mut targets = SwitchTargets::new(guard_false_block);
            targets.add(1, body_block);
            self.current_block_mut().terminator = Term::SwitchInt {
                discriminant: Operand::Copy(Place::Local(guard_local)),
                targets,
            };

            self.switch_to_block(body_block);

            if ref_guard {
                // Drop the ref-binding scope and rebind by move for the arm body.
                for local in scope_locals.iter().rev() {
                    self.emit_drop_and_storage_dead(*local);
                }
                self.pop_scope();
                self.push_scope();
                self.bind_pattern(scrutinee.clone(), &arm.pattern)?;
            }

            self.lower_expr_into(
                destination.clone(),
                &arm.body,
                matches!(&arm.body, Expr::Block { .. }),
            )?;
            if !self.terminated {
                self.emit_drop_and_storage_dead(guard_local);
            }
            self.finish_match_arm(merge_block);

            self.switch_to_block(guard_false_block);
            for local in scope_locals.iter().rev() {
                self.emit_drop_and_storage_dead(*local);
            }
            self.emit_drop_and_storage_dead(guard_local);
            self.current_block_mut().terminator = Term::Goto {
                target: next_test_block,
                args: vec![],
            };
            return Ok(());
        }

        self.lower_expr_into(
            destination,
            &arm.body,
            matches!(&arm.body, Expr::Block { .. }),
        )?;
        self.finish_match_arm(merge_block);
        Ok(())
    }

    fn finish_match_arm(&mut self, merge_block: BasicBlockId) {
        let arm_terminated = self.terminated;
        self.pop_scope();
        if !arm_terminated {
            self.current_block_mut().terminator = Term::Goto {
                target: merge_block,
                args: vec![],
            };
        }
    }

    fn match_test_operand(&mut self, scrutinee: Place) -> Result<Operand, VirLoweringError> {
        let scrutinee_ty = self.place_type(&scrutinee)?;
        if scrutinee_ty.is_copy() {
            return Ok(Operand::Copy(scrutinee));
        }
        // Non-Copy: create a shared borrow so the scrutinee survives across
        // multiple match arms.  The comparison operator dereferences through
        // the reference automatically.
        let ref_ty = RustType::Reference {
            inner: Box::new(scrutinee_ty),
            mutability: Mutability::Shared,
            lifetime: Lifetime::Anonymous(0),
        };
        let ref_local = self.alloc_local(None, ref_ty, Mutability::Shared);
        self.emit(VirStmt::Assign {
            place: Place::Local(ref_local),
            rvalue: Rvalue::Ref {
                borrow_kind: BorrowKind::Shared,
                place: scrutinee,
            },
        });
        Ok(Operand::Copy(Place::Local(ref_local)))
    }
}

fn builtin_try_pattern_can_match(scrutinee_ty: &RustType, pattern: &Pattern) -> bool {
    match pattern {
        Pattern::EnumVariant { enum_name, .. } => {
            let actual_enum = nominal_type_name(scrutinee_ty);
            !matches!(
                (actual_enum.as_deref(), enum_name.as_str()),
                (Some("Option"), "Result") | (Some("Result"), "Option")
            )
        }
        Pattern::Or(alternatives) => alternatives
            .iter()
            .any(|alt| builtin_try_pattern_can_match(scrutinee_ty, alt)),
        _ => true,
    }
}
