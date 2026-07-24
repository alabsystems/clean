// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared loop-target and maybe-initialized cleanup support.

use super::context::FunctionLoweringContext;
use super::VirLoweringError;
use crate::ownership::Place;
use crate::vir::{BasicBlockId, LocalId, Operand, Stmt as VirStmt, SwitchTargets, Term};

#[derive(Debug, Clone)]
pub(super) struct LoopTarget {
    pub(super) label: Option<String>,
    pub(super) continue_block: BasicBlockId,
    pub(super) break_block: BasicBlockId,
    pub(super) break_destination: Place,
    pub(super) continue_cleanup: Vec<LocalId>,
    pub(super) continue_maybe_cleanup: Vec<MaybeInitializedLocal>,
    pub(super) scope_depth: usize,
}

#[derive(Debug, Clone, Copy)]
pub(super) struct MaybeInitializedLocal {
    pub(super) local: LocalId,
    pub(super) init_flag: LocalId,
}

#[derive(Debug, Clone, Copy)]
pub(super) enum CleanupLocal {
    Plain(LocalId),
    MaybeInitialized(MaybeInitializedLocal),
}

impl CleanupLocal {
    pub(super) fn tracks(self, local: LocalId) -> bool {
        match self {
            Self::Plain(tracked) => tracked == local,
            Self::MaybeInitialized(tracked) => tracked.local == local || tracked.init_flag == local,
        }
    }
}

impl<'a> FunctionLoweringContext<'a> {
    pub(super) fn emit_maybe_initialized_local_cleanup(&mut self, tracked: MaybeInitializedLocal) {
        let unwind_entries = self.cleanup_entries_excluding_local(tracked.local);
        self.emit_maybe_initialized_local_cleanup_with_unwind_entries(tracked, &unwind_entries);
    }

    pub(super) fn emit_maybe_initialized_local_cleanup_with_unwind_entries(
        &mut self,
        tracked: MaybeInitializedLocal,
        unwind_entries: &[CleanupLocal],
    ) {
        if self.terminated {
            return;
        }

        let needs_drop = self.local_needs_drop(tracked.local);

        if needs_drop {
            let cleanup_block = self.new_block(Term::Unreachable);
            let skip_drop_block = self.new_block(Term::Unreachable);
            let after_cleanup_block = self.new_block(Term::Unreachable);
            let mut targets = SwitchTargets::new(skip_drop_block);
            targets.add(1, cleanup_block);
            self.current_block_mut().terminator = Term::SwitchInt {
                discriminant: Operand::Copy(Place::Local(tracked.init_flag)),
                targets,
            };

            self.switch_to_block(cleanup_block);
            self.emit_local_cleanup_with_unwind_entries(tracked.local, unwind_entries);
            self.current_block_mut().terminator = Term::Goto {
                target: after_cleanup_block,
                args: vec![],
            };

            self.switch_to_block(skip_drop_block);
            self.emit(VirStmt::StorageDead(tracked.local));
            self.current_block_mut().terminator = Term::Goto {
                target: after_cleanup_block,
                args: vec![],
            };

            self.switch_to_block(after_cleanup_block);
        } else {
            self.emit(VirStmt::StorageDead(tracked.local));
        }

        self.emit(VirStmt::StorageDead(tracked.init_flag));
    }

    pub(super) fn emit_tracked_local_cleanup(&mut self, tracked: MaybeInitializedLocal) {
        self.retire_cleanup_local(tracked.local);
        self.emit_maybe_initialized_local_cleanup(tracked);
    }

    pub(super) fn loop_target(
        &self,
        label: Option<&str>,
        context: &'static str,
    ) -> Result<LoopTarget, VirLoweringError> {
        self.loop_stack
            .iter()
            .rev()
            .find(|target| match label {
                Some(label) => target.label.as_deref() == Some(label),
                None => true,
            })
            .cloned()
            .ok_or_else(|| VirLoweringError::Unsupported {
                context,
                detail: match label {
                    Some(label) => format!("loop label `{label}` is not in scope"),
                    None => format!("`{context}` used outside of a loop"),
                },
            })
    }

    pub(super) fn block_has_predecessor(&self, target: BasicBlockId) -> bool {
        self.body
            .blocks
            .iter()
            .any(|block| block.terminator.successors().contains(&target))
    }

    pub(super) fn recycle_maybe_initialized_loop_temps(
        &mut self,
        locals: &[MaybeInitializedLocal],
    ) {
        for tracked in locals {
            let cleanup_block = self.new_block(Term::Unreachable);
            let after_cleanup_block = self.new_block(Term::Unreachable);
            let mut targets = SwitchTargets::new(after_cleanup_block);
            targets.add(1, cleanup_block);
            self.current_block_mut().terminator = Term::SwitchInt {
                discriminant: Operand::Copy(Place::Local(tracked.init_flag)),
                targets,
            };

            self.switch_to_block(cleanup_block);
            self.recycle_tracked_loop_temp(tracked.local, tracked.init_flag);
            self.current_block_mut().terminator = Term::Goto {
                target: after_cleanup_block,
                args: vec![],
            };

            self.switch_to_block(after_cleanup_block);
            self.set_bool_local(tracked.init_flag, false);
        }
    }
}
