// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Loop lowering: `loop`, `while`, and `for` expressions.

use super::super::context::FunctionLoweringContext;
use super::super::loop_support::{LoopTarget, MaybeInitializedLocal};
use super::super::VirLoweringError;
use crate::expr::{Expr, Pattern};
use crate::ownership::Place;
use crate::types::{Mutability, RustType};
use crate::vir::{
    BorrowKind, Constant, MutBorrowKind, Operand, RetagKind, Rvalue, Stmt as VirStmt,
    SwitchTargets, Term,
};

impl<'a> FunctionLoweringContext<'a> {
    pub(crate) fn lower_loop_expr(
        &mut self,
        destination: Place,
        label: Option<&str>,
        body: &Expr,
    ) -> Result<(), VirLoweringError> {
        let header_block = self.new_block(Term::Unreachable);
        let body_block = self.new_block(Term::Unreachable);
        let exit_block = self.new_block(Term::Unreachable);
        let body_temp = self.alloc_local(None, self.discarded_expr_ty(body)?, Mutability::Mutable);
        let body_temp_init = self.alloc_loop_init_flag();
        self.track_maybe_initialized_local_cleanup(body_temp, body_temp_init);

        self.current_block_mut().terminator = Term::Goto {
            target: header_block,
            args: vec![],
        };
        self.loop_stack.push(LoopTarget {
            label: label.map(str::to_string),
            continue_block: header_block,
            break_block: exit_block,
            break_destination: destination,
            // body_temp is NOT in continue_cleanup: `continue` fires before the
            // body expression finishes, so body_temp is maybe-uninitialized on
            // that edge.  Needs drop-flag / init-state tracking (#2726).
            continue_cleanup: Vec::new(),
            continue_maybe_cleanup: vec![MaybeInitializedLocal {
                local: body_temp,
                init_flag: body_temp_init,
            }],
            scope_depth: self.scope_depth(),
        });

        self.switch_to_block(header_block);
        self.current_block_mut().terminator = Term::Goto {
            target: body_block,
            args: vec![],
        };

        self.switch_to_block(body_block);
        self.lower_expr_into_tracked_loop_temp(body_temp, body_temp_init, body, true)?;
        if !self.terminated {
            self.recycle_tracked_loop_temp(body_temp, body_temp_init);
            self.current_block_mut().terminator = Term::Goto {
                target: header_block,
                args: vec![],
            };
        }
        self.loop_stack.pop();

        if self.block_has_predecessor(exit_block) {
            self.switch_to_block(exit_block);
            self.emit_tracked_local_cleanup(MaybeInitializedLocal {
                local: body_temp,
                init_flag: body_temp_init,
            });
        } else {
            self.terminated = true;
        }

        Ok(())
    }

    pub(crate) fn lower_while_expr(
        &mut self,
        destination: Place,
        label: Option<&str>,
        condition: &Expr,
        body: &Expr,
    ) -> Result<(), VirLoweringError> {
        let header_block = self.new_block(Term::Unreachable);
        let body_block = self.new_block(Term::Unreachable);
        let natural_exit_block = self.new_block(Term::Unreachable);
        let break_exit_block = self.new_block(Term::Unreachable);
        let merge_block = self.new_block(Term::Unreachable);
        let cond_local = self.alloc_local(None, RustType::Bool, Mutability::Mutable);
        let body_temp = self.alloc_local(None, self.discarded_expr_ty(body)?, Mutability::Mutable);
        let body_temp_init = self.alloc_loop_init_flag();
        self.track_maybe_initialized_local_cleanup(body_temp, body_temp_init);

        self.current_block_mut().terminator = Term::Goto {
            target: header_block,
            args: vec![],
        };
        self.loop_stack.push(LoopTarget {
            label: label.map(str::to_string),
            continue_block: header_block,
            break_block: break_exit_block,
            break_destination: destination.clone(),
            // body_temp is NOT in continue_cleanup: see lower_loop_expr comment.
            continue_cleanup: Vec::new(),
            continue_maybe_cleanup: vec![MaybeInitializedLocal {
                local: body_temp,
                init_flag: body_temp_init,
            }],
            scope_depth: self.scope_depth(),
        });

        self.switch_to_block(header_block);
        self.lower_expr_into(Place::Local(cond_local), condition, false)?;
        if self.terminated {
            self.loop_stack.pop();
            return Ok(());
        }
        let mut targets = SwitchTargets::new(natural_exit_block);
        targets.add(1, body_block);
        self.current_block_mut().terminator = Term::SwitchInt {
            discriminant: Operand::Copy(Place::Local(cond_local)),
            targets,
        };

        self.switch_to_block(body_block);
        self.lower_expr_into_tracked_loop_temp(body_temp, body_temp_init, body, true)?;
        if !self.terminated {
            self.recycle_tracked_loop_temp(body_temp, body_temp_init);
            self.current_block_mut().terminator = Term::Goto {
                target: header_block,
                args: vec![],
            };
        }
        self.loop_stack.pop();

        self.switch_to_block(natural_exit_block);
        self.assign_unit(destination)?;
        self.current_block_mut().terminator = Term::Goto {
            target: merge_block,
            args: vec![],
        };

        self.switch_to_block(break_exit_block);
        self.current_block_mut().terminator = Term::Goto {
            target: merge_block,
            args: vec![],
        };

        self.switch_to_block(merge_block);
        self.emit_tracked_local_cleanup(MaybeInitializedLocal {
            local: body_temp,
            init_flag: body_temp_init,
        });
        self.emit_drop_and_storage_dead(cond_local);
        Ok(())
    }

    /// Lower `for pattern in iter_expr { body }` into the standard MIR desugaring:
    ///
    /// ```text
    /// let mut iter = IntoIterator::into_iter(iter_expr);
    /// loop {
    ///     let next = Iterator::next(&mut iter);
    ///     match next {
    ///         Option::Some(val) => { let pattern = val; body },
    ///         Option::None => break,
    ///     }
    /// }
    /// ```
    ///
    /// In VIR this becomes:
    ///   entry → call into_iter → header → call next → switch(discriminant)
    ///     → [Some] body_block (bind pattern, run body, goto header)
    ///     → [None] exit_block (assign unit)
    pub(crate) fn lower_for_expr(
        &mut self,
        destination: Place,
        label: Option<&str>,
        pattern: &Pattern,
        iter_expr: &Expr,
        body: &Expr,
    ) -> Result<(), VirLoweringError> {
        // Infer the element type from the iterator expression.
        let iter_ty = self.infer_expr_type(iter_expr)?;
        let elem_ty = for_loop_element_type(&iter_ty)?;

        // Allocate the iterator local and evaluate the iter expression into it.
        let iter_local = self.alloc_local(None, iter_ty.clone(), Mutability::Mutable);
        self.lower_expr_into(Place::Local(iter_local), iter_expr, false)?;
        if self.terminated {
            return Ok(());
        }

        // Option<elem_ty> for the `next()` result.
        let option_ty = RustType::Named {
            name: "Option".to_string(),
            type_args: vec![elem_ty.clone()],
            lifetime_args: Vec::new(),
            const_args: Vec::new(),
        };

        let header_block = self.new_block(Term::Unreachable);
        let body_block = self.new_block(Term::Unreachable);
        let exit_block = self.new_block(Term::Unreachable);
        let break_exit_block = self.new_block(Term::Unreachable);
        let merge_block = self.new_block(Term::Unreachable);

        let next_result = self.alloc_local(None, option_ty, Mutability::Mutable);
        let body_temp = self.alloc_local(None, self.discarded_expr_ty(body)?, Mutability::Mutable);
        let body_temp_init = self.alloc_loop_init_flag();
        self.track_maybe_initialized_local_cleanup(body_temp, body_temp_init);

        // Jump from entry to header.
        self.current_block_mut().terminator = Term::Goto {
            target: header_block,
            args: vec![],
        };

        // Push loop target for break/continue inside the body.
        self.loop_stack.push(LoopTarget {
            label: label.map(str::to_string),
            continue_block: header_block,
            break_block: break_exit_block,
            break_destination: destination.clone(),
            // next_result is definitely initialized (written by Iterator::next
            // before body entry).  body_temp is NOT: see lower_loop_expr comment.
            continue_cleanup: vec![next_result],
            continue_maybe_cleanup: vec![MaybeInitializedLocal {
                local: body_temp,
                init_flag: body_temp_init,
            }],
            scope_depth: self.scope_depth(),
        });

        // Header block: call Iterator::next(&mut iter).
        self.switch_to_block(header_block);
        let (iter_ref, next_cont) = {
            // Create &mut iter reference.
            let iter_ref_ty = RustType::Reference {
                lifetime: crate::types::Lifetime::Anonymous(0),
                mutability: Mutability::Mutable,
                inner: Box::new(iter_ty.clone()),
            };
            let iter_ref = self.alloc_local(None, iter_ref_ty, Mutability::Mutable);
            self.emit_ref_and_retag(
                Place::Local(iter_ref),
                BorrowKind::Mut {
                    kind: MutBorrowKind::Default,
                },
                Place::Local(iter_local),
                RetagKind::Default,
            );

            // Call next — modelled as a Term::Call to `Iterator::next`.
            let next_cont = self.new_block(Term::Unreachable);
            self.current_block_mut().terminator = Term::Call {
                func: Operand::Constant(Constant::FnDef {
                    name: "Iterator::next".to_string(),
                    substs: vec![],
                }),
                args: vec![Operand::Move(Place::Local(iter_ref))],
                destination: Place::Local(next_result),
                target: Some(next_cont),
                target_args: vec![],
                unwind: self.call_unwind_action(&Place::Local(next_result)),
            };
            (iter_ref, next_cont)
        };
        self.switch_to_block(next_cont);
        self.emit_drop_and_storage_dead(iter_ref);

        // Discriminant switch: Some (discriminant=1) → body, None (0) → exit.
        let discrim_local = self.alloc_local(None, RustType::Bool, Mutability::Mutable);
        self.emit(VirStmt::Assign {
            place: Place::Local(discrim_local),
            rvalue: Rvalue::Discriminant(Place::Local(next_result)),
        });
        let mut targets = SwitchTargets::new(exit_block);
        targets.add(1, body_block);
        self.current_block_mut().terminator = Term::SwitchInt {
            discriminant: Operand::Copy(Place::Local(discrim_local)),
            targets,
        };

        // Body block: downcast to Some, bind pattern, execute body.
        // Retire the discriminant local immediately — it was consumed by the
        // switch and must not survive into the body or the backedge (which
        // would otherwise cause double-StorageLive on the next iteration).
        self.switch_to_block(body_block);
        self.emit_drop_and_storage_dead(discrim_local);
        self.push_scope();
        {
            // Extract the inner value from Option::Some.
            let elem_local = self.alloc_local(None, elem_ty, Mutability::Mutable);
            let some_place = Place::Downcast {
                base: Box::new(Place::Local(next_result)),
                variant: "Some".to_string(),
            };
            self.emit(VirStmt::Assign {
                place: Place::Local(elem_local),
                rvalue: Rvalue::Use(Operand::Move(some_place)),
            });

            // Bind the for-loop pattern from the extracted element.
            self.bind_pattern(Place::Local(elem_local), pattern)?;

            // Execute the loop body.
            self.lower_expr_into_tracked_loop_temp(body_temp, body_temp_init, body, true)?;
        }
        if !self.terminated {
            self.pop_scope();
            self.recycle_tracked_loop_temp(body_temp, body_temp_init);
            self.recycle_loop_temps(&[next_result]);
            self.current_block_mut().terminator = Term::Goto {
                target: header_block,
                args: vec![],
            };
        } else {
            self.pop_scope();
        }
        self.loop_stack.pop();

        // Natural exit: None branch → assign unit.
        self.switch_to_block(exit_block);
        // Retire discriminant on the exit path too (already retired from scope
        // cleanup during body_block lowering; this emits the StorageDead).
        self.emit(VirStmt::StorageDead(discrim_local));
        self.assign_unit(destination)?;
        self.current_block_mut().terminator = Term::Goto {
            target: merge_block,
            args: vec![],
        };

        // Break exit → merge.
        self.switch_to_block(break_exit_block);
        self.current_block_mut().terminator = Term::Goto {
            target: merge_block,
            args: vec![],
        };

        // Merge block: clean up temporaries (drop non-Copy before StorageDead).
        self.switch_to_block(merge_block);
        self.emit_tracked_local_cleanup(MaybeInitializedLocal {
            local: body_temp,
            init_flag: body_temp_init,
        });
        self.emit_drop_and_storage_dead(next_result);
        self.emit_drop_and_storage_dead(iter_local);
        Ok(())
    }

    fn discarded_expr_ty(&self, expr: &Expr) -> Result<RustType, VirLoweringError> {
        match self.infer_expr_type(expr)? {
            RustType::Never => Ok(RustType::Unit),
            ty => Ok(ty),
        }
    }
}

/// Extract the element type from an iterator/range type for a for-loop.
///
/// Range types carry their element type in `type_args[0]`. Arrays and slices
/// yield their element type directly. Fails closed on unrecognized iterator
/// types rather than silently producing `Unit`.
fn for_loop_element_type(iter_ty: &RustType) -> Result<RustType, VirLoweringError> {
    match iter_ty {
        RustType::Named { type_args, .. } if !type_args.is_empty() => Ok(type_args[0].clone()),
        RustType::Array { element, .. } => Ok(*element.clone()),
        RustType::Slice { elem } => Ok(*elem.clone()),
        RustType::Reference { inner, .. } => for_loop_element_type(inner),
        _ => Err(VirLoweringError::MissingType {
            context: format!(
                "for-loop iterator element type: cannot extract element from `{iter_ty:?}`"
            ),
        }),
    }
}
