// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unwind-cleanup CFG synthesis for VIR lowering.

use super::context::FunctionLoweringContext;
use super::loop_support::CleanupLocal;
use crate::ownership::Place;
use crate::vir::{LocalId, Stmt as VirStmt, Term, UnwindAction};

impl<'a> FunctionLoweringContext<'a> {
    pub(super) fn collect_cleanup_entries(&self, keep_depth: usize) -> Vec<CleanupLocal> {
        self.scopes
            .iter()
            .skip(keep_depth)
            .rev()
            .flat_map(|scope| scope.cleanup.iter().rev().copied())
            .collect()
    }

    pub(super) fn current_cleanup_entries(&self) -> Vec<CleanupLocal> {
        self.collect_cleanup_entries(0)
    }

    pub(super) fn cleanup_entries_excluding_local(&self, local: LocalId) -> Vec<CleanupLocal> {
        self.current_cleanup_entries()
            .into_iter()
            .filter(|cleanup| !cleanup.tracks(local))
            .collect()
    }

    pub(super) fn local_needs_drop(&self, local: LocalId) -> bool {
        self.body
            .local(local)
            .map(|decl| !decl.ty.is_copy())
            .unwrap_or(false)
    }

    fn cleanup_entry_needs_drop(&self, cleanup: CleanupLocal) -> bool {
        match cleanup {
            CleanupLocal::Plain(local) => self.local_needs_drop(local),
            CleanupLocal::MaybeInitialized(tracked) => self.local_needs_drop(tracked.local),
        }
    }

    fn build_unwind_action(&mut self, cleanup_entries: &[CleanupLocal]) -> UnwindAction {
        if self.building_cleanup_blocks {
            return UnwindAction::Terminate;
        }
        if !cleanup_entries
            .iter()
            .copied()
            .any(|cleanup| self.cleanup_entry_needs_drop(cleanup))
        {
            return UnwindAction::Continue;
        }

        let saved_block = self.current_block;
        let saved_terminated = self.terminated;
        self.building_cleanup_blocks = true;

        let cleanup_entry = self.new_block(Term::Unreachable);
        self.switch_to_block(cleanup_entry);
        for (idx, cleanup) in cleanup_entries.iter().copied().enumerate() {
            self.emit_cleanup_entry_with_unwind_entries(cleanup, &cleanup_entries[(idx + 1)..]);
        }
        self.current_block_mut().terminator = Term::UnwindResume;

        self.building_cleanup_blocks = false;
        self.current_block = saved_block;
        self.terminated = saved_terminated;
        UnwindAction::Cleanup(cleanup_entry)
    }

    pub(super) fn call_unwind_action(&mut self, destination: &Place) -> UnwindAction {
        let cleanup_entries = match destination {
            Place::Local(local) if !self.local_has_prior_def(*local) => {
                self.cleanup_entries_excluding_local(*local)
            }
            _ => self.current_cleanup_entries(),
        };
        self.build_unwind_action(&cleanup_entries)
    }

    pub(super) fn emit_scope_cleanup(&mut self, keep_depth: usize) {
        let full_entries = self.current_cleanup_entries();
        let active_entries = self.collect_cleanup_entries(keep_depth);
        for (idx, cleanup) in active_entries.iter().copied().enumerate() {
            self.emit_cleanup_entry_with_unwind_entries(cleanup, &full_entries[(idx + 1)..]);
        }
    }

    pub(super) fn pop_scope(&mut self) {
        let Some(scope) = self.scopes.last().cloned() else {
            return;
        };
        if self.terminated {
            self.scopes.pop();
            return;
        }
        let full_entries = self.current_cleanup_entries();
        let active_entries: Vec<_> = scope.cleanup.iter().rev().copied().collect();
        for (idx, cleanup) in active_entries.iter().copied().enumerate() {
            self.emit_cleanup_entry_with_unwind_entries(cleanup, &full_entries[(idx + 1)..]);
        }
        self.scopes.pop();
    }

    /// Emit a drop terminator for non-Copy locals, then `StorageDead`.
    ///
    /// For Copy types, only `StorageDead` is emitted (no destructor needed).
    /// For non-Copy types, `Term::Drop` terminates the current block and a
    /// continuation block receives `StorageDead`. This models the destructor
    /// call point, enabling NLL to detect borrow-vs-drop conflicts.
    pub(super) fn emit_drop_and_storage_dead(&mut self, local: LocalId) {
        if self.terminated {
            return;
        }
        self.retire_cleanup_local(local);
        let unwind_entries = self.current_cleanup_entries();
        self.emit_local_cleanup_with_unwind_entries(local, &unwind_entries);
    }

    pub(super) fn emit_local_cleanup(&mut self, local: LocalId) {
        let unwind_entries = self.cleanup_entries_excluding_local(local);
        self.emit_local_cleanup_with_unwind_entries(local, &unwind_entries);
    }

    pub(super) fn emit_local_cleanup_with_unwind_entries(
        &mut self,
        local: LocalId,
        unwind_entries: &[CleanupLocal],
    ) {
        let needs_drop = self.local_needs_drop(local);
        if needs_drop {
            let continuation = self.new_block(Term::Unreachable);
            self.current_block_mut().terminator = Term::Drop {
                place: Place::Local(local),
                target: continuation,
                target_args: vec![],
                unwind: self.build_unwind_action(unwind_entries),
            };
            self.switch_to_block(continuation);
        }
        self.emit(VirStmt::StorageDead(local));
    }

    pub(super) fn emit_cleanup_entry_with_unwind_entries(
        &mut self,
        cleanup: CleanupLocal,
        unwind_entries: &[CleanupLocal],
    ) {
        match cleanup {
            CleanupLocal::Plain(local) => {
                self.emit_local_cleanup_with_unwind_entries(local, unwind_entries);
            }
            CleanupLocal::MaybeInitialized(tracked) => {
                self.emit_maybe_initialized_local_cleanup_with_unwind_entries(
                    tracked,
                    unwind_entries,
                );
            }
        }
    }
}
