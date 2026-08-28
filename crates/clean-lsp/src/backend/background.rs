// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Per-URI background elaboration tasks (unfreeze plan, deferred item C).
//!
//! `didOpen`/`didChange` handlers publish parse diagnostics inline
//! (parse-first) and then hand the compute+commit half of a document check
//! to a `tokio::spawn`ed task, so a keystroke's notification handler no
//! longer awaits its own full elaboration. Three mechanisms keep that safe:
//!
//! 1. **Version check at commit** (pre-existing): `commit_elaboration`
//!    discards a result computed against a superseded document version.
//! 2. **Per-URI generation counter** (this module): every scheduled check
//!    bumps the URI's generation; a task whose generation is no longer
//!    current skips its terminal `$/lean/fileProgress` and final diagnostics
//!    publish — the newer run owns them.
//! 3. **Task-handle tracking** (this module): the bump that supersedes a
//!    generation aborts its in-flight task. The abort lands at the task's
//!    next await point — the blocking elaboration itself runs to completion
//!    on the blocking pool — and mechanisms 1–2 cover the window an abort
//!    cannot reach.
//!
//! Requests racing the background task (hover, plainGoal, plainTermGoal,
//! inlay hints, ...) answer from the last committed snapshot:
//! `Document::apply_change` preserves `elaborated` across edits precisely so
//! that window serves data instead of going dark.
//!
//! tower-lsp gives notification handlers no response and no cross-handler
//! ordering guarantee, so every method here tolerates a concurrent bump or
//! `didClose` between its steps: registration re-checks the generation, and
//! a missing slot always means "superseded — do nothing and abort".

use super::CleanBackend;
use std::sync::Arc;
use tower_lsp::lsp_types::Url;

/// Background-elaboration bookkeeping for one URI.
#[derive(Debug)]
pub(crate) struct ElaborationSlot {
    /// Generation of the most recently scheduled check for this URI.
    /// Monotonically increasing per URI; a task holding an older generation
    /// is superseded.
    pub(crate) generation: u64,
    /// The in-flight background task, if any. Taken (and aborted) by the
    /// bump that supersedes it; cleared by the task itself on completion.
    pub(crate) task: Option<tokio::task::JoinHandle<()>>,
}

impl CleanBackend {
    /// Schedule a full document check with the elaboration phase in a
    /// per-URI background task.
    ///
    /// The parse phase (parse + parse-only diagnostics + leading
    /// `$/lean/fileProgress`) runs inline, so it completes before the
    /// calling notification handler returns — parse-first ordering is
    /// preserved. The elaboration phase (compute + version-gated commit +
    /// terminal notification + full diagnostics publish) is spawned and
    /// tracked so a newer check supersedes it.
    pub(crate) async fn spawn_check_document(&self, uri: &Url) {
        let generation = self.bump_elaboration_generation(uri);
        let announced_version = self.check_document_parse_phase(uri).await;

        let backend = self.background_handle();
        let task_uri = uri.clone();
        let task = tokio::spawn(async move {
            backend
                .check_document_elaboration_phase(&task_uri, generation, announced_version)
                .await;
        });
        self.register_elaboration_task(uri, generation, task);
    }

    /// Bump `uri`'s elaboration generation, aborting any superseded
    /// in-flight task, and return the new generation.
    ///
    /// Called by every scheduled check (inline or spawned) before its parse
    /// phase, so the returned generation stays current until the next check
    /// of the same URI is scheduled.
    pub(crate) fn bump_elaboration_generation(&self, uri: &Url) -> u64 {
        let mut slot = self
            .elaboration_tasks
            .entry(uri.clone())
            .or_insert_with(|| ElaborationSlot {
                generation: 0,
                task: None,
            });
        slot.generation += 1;
        // Abort the superseded task. The abort lands at its next await
        // point; if it is already past its last one, the version check in
        // `commit_elaboration` and the generation gate in
        // `check_document_elaboration_phase` discard its effects instead.
        if let Some(task) = slot.task.take() {
            task.abort();
        }
        slot.generation
    }

    /// Whether `generation` is still the latest scheduled check for `uri`.
    ///
    /// `false` for a closed document (`discard_elaboration_task` removed the
    /// slot): a task that outlived its document must not publish either.
    pub(crate) fn elaboration_generation_is_current(&self, uri: &Url, generation: u64) -> bool {
        self.elaboration_tasks
            .get(uri)
            .is_some_and(|slot| slot.generation == generation)
    }

    /// Track the spawned task for `generation` so a later bump can abort it.
    ///
    /// tower-lsp runs notification handlers concurrently, so a newer
    /// `didChange` may have bumped the generation between our bump and this
    /// registration; the task is then already superseded and is aborted
    /// instead of stored (its commit and publishes are version- and
    /// generation-gated regardless — the abort just ends it early). A
    /// `didClose` may likewise have discarded the slot entirely.
    pub(crate) fn register_elaboration_task(
        &self,
        uri: &Url,
        generation: u64,
        task: tokio::task::JoinHandle<()>,
    ) {
        let Some(mut slot) = self.elaboration_tasks.get_mut(uri) else {
            task.abort();
            return;
        };
        if slot.generation == generation {
            // The bump that returned `generation` emptied the slot, and each
            // generation registers at most one task, so nothing is clobbered.
            slot.task = Some(task);
        } else {
            task.abort();
        }
    }

    /// Drop the stored handle once the task for `generation` has finished
    /// its publishes. Dropping a `JoinHandle` detaches rather than cancels,
    /// so the (already ending) task is unaffected; this only keeps the slot
    /// from accumulating finished handles.
    pub(crate) fn finish_elaboration_task(&self, uri: &Url, generation: u64) {
        if let Some(mut slot) = self.elaboration_tasks.get_mut(uri) {
            if slot.generation == generation {
                slot.task = None;
            }
        }
    }

    /// `didClose`: abort any in-flight task and remove the URI's slot. With
    /// the slot gone, `elaboration_generation_is_current` reports `false` to
    /// any still-running task, so nothing re-publishes diagnostics after the
    /// close handler's clearing publish.
    pub(crate) fn discard_elaboration_task(&self, uri: &Url) {
        if let Some((_, slot)) = self.elaboration_tasks.remove(uri) {
            if let Some(task) = slot.task {
                task.abort();
            }
        }
    }

    /// A second `CleanBackend` view over the same shared state, for moving
    /// into a spawned task (`tokio::spawn` needs an owned `'static` value).
    /// Every stateful field is `Arc`-shared — this is a handle, never a
    /// copy: state written through one view is visible through the other.
    fn background_handle(&self) -> Self {
        Self {
            client: self.client.clone(),
            documents: Arc::clone(&self.documents),
            env: Arc::clone(&self.env),
            definitions: Arc::clone(&self.definitions),
            rpc_sessions: Arc::clone(&self.rpc_sessions),
            tactic_goal_snapshots: Arc::clone(&self.tactic_goal_snapshots),
            tactic_patterns: self.tactic_patterns.clone(),
            config: Arc::clone(&self.config),
            elaboration_tasks: Arc::clone(&self.elaboration_tasks),
        }
    }

    /// Join the in-flight background task for `uri`, if any. Test-only:
    /// production code must never block on a background elaboration — that
    /// would recreate the inline await this module exists to remove.
    #[cfg(test)]
    pub(crate) async fn wait_for_elaboration(&self, uri: &Url) {
        // Take the handle out under the guard, await outside it: holding a
        // DashMap guard across the await would block every other accessor
        // of the shard for the whole elaboration.
        let task = self
            .elaboration_tasks
            .get_mut(uri)
            .and_then(|mut slot| slot.task.take());
        if let Some(task) = task {
            // Err means the task was aborted (or panicked); both count as
            // finished for a joiner.
            let _ = task.await;
        }
    }
}
