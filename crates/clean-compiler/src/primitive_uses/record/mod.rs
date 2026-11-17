// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::measure::Meter;
use super::*;
use std::sync::Mutex;

#[derive(Clone, Debug)]
pub(crate) struct ObservationRecorder {
    shared: Arc<Mutex<State>>,
}
#[derive(Debug)]
struct State {
    data: PrimitiveUseObservations,
    stopped: bool,
    sealed: bool,
    event_count: usize,
}

/// Explicit producer frame; never ambient thread-local or environment state.
#[derive(Clone, Debug)]
pub(crate) struct ObservationFrame {
    recorder: ObservationRecorder,
    role: InvocationRole,
    occurrence: usize,
    iteration: usize,
    parent: Option<ArtifactId>,
}

impl ObservationRecorder {
    pub(crate) fn new(limits: ObservationLimits) -> Self {
        Self {
            shared: Arc::new(Mutex::new(State {
                data: PrimitiveUseObservations {
                    run: Arc::new(()),
                    artifacts: Vec::new(),
                    decisions: Vec::new(),
                    diagnostics: Vec::new(),
                    gaps: Vec::new(),
                    limits,
                    retained_bytes: 0,
                    contexts: 0,
                    work: 0,
                },
                stopped: false,
                sealed: false,
                event_count: 0,
            })),
        }
    }
    pub(crate) fn input_context(&self) -> bool {
        self.context::<ObservedCompilerInput<'_>>()
    }
    pub(crate) fn context<T>(&self) -> bool {
        self.context_bytes(size_of::<T>())
    }
    #[cfg(feature = "trust-ir-backend")]
    pub(crate) fn shared_context<T>(&self) -> bool {
        self.context_bytes(size_of::<T>().saturating_add(2 * size_of::<usize>()))
    }
    fn context_bytes(&self, bytes: usize) -> bool {
        let mut state = self
            .shared
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if state.data.contexts == state.data.limits.context_limit() {
            state.gap(ObservationGap::Truncated(ObservationLimit::Contexts));
            false
        } else if bytes
            > state
                .data
                .limits
                .byte_limit()
                .saturating_sub(state.data.retained_bytes)
        {
            state.gap(ObservationGap::Truncated(ObservationLimit::Bytes));
            false
        } else if state.data.work == state.data.limits.work_limit() {
            state.gap(ObservationGap::Truncated(ObservationLimit::Work));
            false
        } else {
            state.data.contexts += 1;
            state.data.retained_bytes += bytes;
            state.data.work += 1;
            true
        }
    }
    pub(crate) fn frame(
        &self,
        role: InvocationRole,
        occurrence: usize,
        iteration: usize,
    ) -> ObservationFrame {
        ObservationFrame {
            recorder: self.clone(),
            role,
            occurrence,
            iteration,
            parent: None,
        }
    }
    pub(crate) fn gap(&self, gap: ObservationGap) {
        // Recording must not replace a compiler result with a poisoned-lock
        // panic. Poison remains an explicit missing-observation condition.
        let mut state = self
            .shared
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        state.gap(gap);
    }
    pub(crate) fn finish(self) -> PrimitiveUseObservations {
        let mut state = self
            .shared
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if self.shared.is_poisoned() {
            state.gap(ObservationGap::Unobserved {
                owner: "recorder",
                reason: "recording lock poisoned",
            });
        }
        state.sealed = true;
        let data = &mut state.data;
        PrimitiveUseObservations {
            run: Arc::clone(&data.run),
            artifacts: std::mem::take(&mut data.artifacts),
            decisions: std::mem::take(&mut data.decisions),
            diagnostics: std::mem::take(&mut data.diagnostics),
            gaps: std::mem::take(&mut data.gaps),
            limits: data.limits,
            retained_bytes: data.retained_bytes,
            contexts: data.contexts,
            work: data.work,
        }
    }
}

impl State {
    fn gap(&mut self, gap: ObservationGap) {
        if self.sealed || self.stopped {
            return;
        }
        if matches!(gap, ObservationGap::Truncated(_)) {
            self.stopped = true;
            // Exactly one fixed terminal status is outside payload accounting.
            // It exists even when the caller permits only one retained byte.
            self.data.gaps.push(gap);
            return;
        }
        if self.event_count == self.data.limits.event_limit() {
            return self.gap(ObservationGap::Truncated(ObservationLimit::Events));
        }
        if self.data.work == self.data.limits.work_limit() {
            return self.gap(ObservationGap::Truncated(ObservationLimit::Work));
        }
        let bytes = size_of::<ObservationGap>();
        if bytes
            > self
                .data
                .limits
                .byte_limit()
                .saturating_sub(self.data.retained_bytes)
        {
            return self.gap(ObservationGap::Truncated(ObservationLimit::Bytes));
        }
        self.event_count += 1;
        self.data.work += 1;
        self.data.retained_bytes += bytes;
        self.data.gaps.push(gap);
    }
    fn reserve_artifact(&mut self) -> bool {
        if self.stopped || self.sealed {
            return false;
        }
        if self.data.artifacts.len() == self.data.limits.artifact_limit() {
            self.gap(ObservationGap::Truncated(ObservationLimit::Artifacts));
            return false;
        }
        let bytes = size_of::<RecordedArtifact>() + 2 * size_of::<usize>();
        if bytes
            > self
                .data
                .limits
                .byte_limit()
                .saturating_sub(self.data.retained_bytes)
        {
            self.gap(ObservationGap::Truncated(ObservationLimit::Bytes));
            return false;
        }
        self.data.retained_bytes += bytes;
        true
    }
    fn measured(&mut self, meter: Meter, result: Result<(), ObservationGap>) -> bool {
        self.data.work = self.data.work.saturating_add(meter.work);
        match result {
            Ok(()) => {
                self.data.retained_bytes += meter.bytes;
                true
            }
            Err(gap) => {
                self.gap(gap);
                false
            }
        }
    }
    fn store(
        &mut self,
        owner: &'static str,
        payload: ArtifactPayload,
        parent: Option<ArtifactId>,
    ) -> ArtifactId {
        let id = ArtifactId {
            run: Arc::clone(&self.data.run),
            ordinal: self.data.artifacts.len(),
        };
        self.data.artifacts.push(RecordedArtifact {
            id: id.clone(),
            owner,
            parent,
            payload,
        });
        id
    }
    fn event(
        &mut self,
        frame: &ObservationFrame,
        owner: &'static str,
        before: ArtifactId,
        after: Option<ArtifactId>,
        note: &'static str,
    ) {
        if self.sealed || self.stopped {
            return;
        }
        if self.event_count == self.data.limits.event_limit() {
            self.gap(ObservationGap::Truncated(ObservationLimit::Events));
            return;
        }
        if self.data.work == self.data.limits.work_limit() {
            self.gap(ObservationGap::Truncated(ObservationLimit::Work));
            return;
        }
        let bytes = size_of::<PrimitiveDecision>();
        if bytes
            > self
                .data
                .limits
                .byte_limit()
                .saturating_sub(self.data.retained_bytes)
        {
            self.gap(ObservationGap::Truncated(ObservationLimit::Bytes));
            return;
        }
        self.data.work += 1;
        self.data.retained_bytes += bytes;
        self.event_count += 1;
        let event = PrimitiveDecision {
            owner,
            occurrence: frame.occurrence,
            iteration: frame.iteration,
            before,
            after,
            note,
        };
        if frame.role == InvocationRole::Consumed {
            self.data.decisions.push(event);
        } else if let Some(run) = self
            .data
            .diagnostics
            .iter_mut()
            .find(|run| run.role == frame.role)
        {
            run.decisions.push(event);
        } else {
            self.data.diagnostics.push(DiagnosticRun {
                role: frame.role.clone(),
                decisions: vec![event],
            });
        }
    }
}

impl ObservationFrame {
    pub(crate) fn parent(&self, parent: Option<ArtifactId>) -> Self {
        Self {
            parent,
            ..self.clone()
        }
    }
    pub(crate) fn declaration(&self, owner: &'static str, decl: &Decl) -> Self {
        let parent = self.declarations(owner, std::slice::from_ref(decl));
        self.parent(parent)
    }

    pub(crate) fn occurrence(&self, occurrence: usize) -> Self {
        Self {
            occurrence,
            ..self.clone()
        }
    }
    pub(crate) fn iteration(&self, iteration: usize) -> Self {
        Self {
            iteration,
            ..self.clone()
        }
    }
    pub(crate) fn gap(&self, gap: ObservationGap) {
        self.recorder.gap(gap);
    }
    pub(crate) fn code(&self, owner: &'static str, value: &Code) -> Option<ArtifactId> {
        let Ok(mut state) = self.recorder.shared.lock() else {
            return None;
        };
        if !state.reserve_artifact() {
            return None;
        }
        let mut meter = Meter::new(
            state.data.limits,
            state.data.retained_bytes,
            state.data.work,
        );
        let result = meter.code(value);
        if !state.measured(meter, result) {
            return None;
        }
        Some(state.store(
            owner,
            ArtifactPayload::LcnfCode(Arc::new(value.clone())),
            self.parent.clone(),
        ))
    }
    pub(crate) fn value(&self, owner: &'static str, value: &LetValue) -> Option<ArtifactId> {
        let Ok(mut state) = self.recorder.shared.lock() else {
            return None;
        };
        if !state.reserve_artifact() {
            return None;
        }
        let mut meter = Meter::new(
            state.data.limits,
            state.data.retained_bytes,
            state.data.work,
        );
        let result = meter.value(value);
        if !state.measured(meter, result) {
            return None;
        }
        Some(state.store(
            owner,
            ArtifactPayload::LcnfValue(Arc::new(value.clone())),
            self.parent.clone(),
        ))
    }
    pub(crate) fn declarations(&self, owner: &'static str, decls: &[Decl]) -> Option<ArtifactId> {
        let Ok(mut state) = self.recorder.shared.lock() else {
            return None;
        };
        if !state.reserve_artifact() {
            return None;
        }
        let mut meter = Meter::new(
            state.data.limits,
            state.data.retained_bytes,
            state.data.work,
        );
        let result = meter.declarations(decls);
        if !state.measured(meter, result) {
            return None;
        }
        Some(state.store(
            owner,
            ArtifactPayload::LcnfDeclarations(decls.to_vec().into()),
            self.parent.clone(),
        ))
    }
    pub(crate) fn decision(
        &self,
        owner: &'static str,
        before: Option<ArtifactId>,
        after: Option<ArtifactId>,
        note: &'static str,
    ) {
        let Some(before) = before else {
            return;
        };
        let Ok(mut state) = self.recorder.shared.lock() else {
            return;
        };
        state.event(self, owner, before, after, note);
    }
}

mod emitter;
