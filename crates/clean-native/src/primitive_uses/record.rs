// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
use clean_compiler::primitive_uses::ObservationLimit;
#[cfg(feature = "trust-ir-backend")]
use std::process::Command;
use std::sync::{Mutex, MutexGuard};

#[derive(Clone)]
pub(crate) struct NativeRecorder {
    pub(super) state: Arc<Mutex<State>>,
}
pub(super) struct State {
    pub(super) data: NativePrimitiveUseObservations,
    pub(super) stopped: bool,
    pub(super) sealed: bool,
    source: Option<NativeArtifactId>,
    inline: Option<NativeArtifactId>,
    #[cfg(feature = "trust-ir-backend")]
    emission_error:
        Option<Box<clean_compiler::primitive_uses::OwnedObservedPipelineFailure<anyhow::Error>>>,
}
impl NativeRecorder {
    #[cfg(feature = "trust-ir-backend")]
    pub(crate) fn new(limits: NativeObservationLimits) -> Self {
        Self {
            state: Arc::new(Mutex::new(State {
                data: NativePrimitiveUseObservations {
                    run: Arc::new(()),
                    limits,
                    artifacts: vec![],
                    decisions: vec![],
                    gaps: vec![],
                    bytes: 0,
                    work: 0,
                    contexts: 0,
                    compiler: None,
                },
                stopped: false,
                sealed: false,
                source: None,
                inline: None,
                emission_error: None,
            })),
        }
    }
    pub(crate) fn gap(&self, gap: ObservationGap) {
        let mut state = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        state.gap(gap);
    }
    #[cfg(feature = "trust-ir-backend")]
    pub(crate) fn environment(
        &self,
        owner: &'static str,
        environment: Arc<Environment>,
    ) -> Option<NativeArtifactId> {
        let mut state = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if environment.has_constant_source() {
            state.gap(ObservationGap::Unobserved {
                owner: "lazy native source context",
                reason: "owned environment Arc is not a snapshot of callback results",
            });
        }
        if !state.reserve_context(0) {
            return None;
        }
        let id = state.store(owner, NativeArtifactPayload::Environment(environment));
        if state.source.is_none() {
            state.source = Some(id.clone());
        }
        Some(id)
    }
    pub(crate) fn context<T>(&self) -> Option<NativeContextPermit<'_>> {
        let mut state = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if !state.reserve_context(size_of::<T>()) {
            return None;
        }
        Some(NativeContextPermit { state })
    }
    pub(crate) fn decision(
        &self,
        role: NativeInvocationRole,
        owner: &'static str,
        name: Option<&Name>,
        target: Option<&Name>,
        outcome: &'static str,
    ) {
        let mut state = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if !state.reserve(size_of::<NativeDecision>()) {
            return;
        }
        let context = state.source.clone();
        state.data.decisions.push(NativeDecision {
            role,
            owner,
            name: name.cloned(),
            target: target.cloned(),
            context,
            artifact: None,
            outcome,
        });
    }
    #[cfg(feature = "trust-ir-backend")]
    pub(crate) fn compiler_limits(&self) -> ObservationLimits {
        self.state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .data
            .limits
            .compiler
    }
    #[cfg(feature = "trust-ir-backend")]
    pub(crate) fn finish(self) -> NativePrimitiveUseObservations {
        let mut state = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if self.state.is_poisoned() {
            state.gap(ObservationGap::Unobserved {
                owner: "native recorder",
                reason: "recording mutex poisoned",
            });
        }
        state.sealed = true;
        let data = &mut state.data;
        NativePrimitiveUseObservations {
            run: Arc::clone(&data.run),
            limits: data.limits,
            artifacts: std::mem::take(&mut data.artifacts),
            decisions: std::mem::take(&mut data.decisions),
            gaps: std::mem::take(&mut data.gaps),
            bytes: data.bytes,
            work: data.work,
            contexts: data.contexts,
            compiler: data.compiler.take(),
        }
    }
    #[cfg(feature = "trust-ir-backend")]
    pub(crate) fn emission_error(
        &self,
        error: clean_compiler::primitive_uses::OwnedObservedPipelineFailure<anyhow::Error>,
    ) {
        // This is the mandatory actual returned error, independent of optional
        // recording limits. Never reduce typed consumer E to only a string.
        self.state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .emission_error = Some(Box::new(error));
    }
    #[cfg(feature = "trust-ir-backend")]
    pub(crate) fn take_emission_error(
        &self,
    ) -> Option<Box<clean_compiler::primitive_uses::OwnedObservedPipelineFailure<anyhow::Error>>>
    {
        self.state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .emission_error
            .take()
    }
    #[cfg(feature = "trust-ir-backend")]
    pub(crate) fn compiler(
        &self,
        output: clean_compiler::primitive_uses::OwnedObservedCompilerOutput,
    ) {
        let mut state = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        // The compiler result itself is the normal actual artifact, and its
        // retained snapshots have their own explicit compiler budget. It is
        // never relabeled as a native capability or inferred backend input.
        if state.reserve_context(0) {
            state.data.compiler = Some(Arc::new(output));
        }
    }
    #[cfg(feature = "trust-ir-backend")]
    pub(crate) fn bytes(
        &self,
        owner: &'static str,
        label: &'static str,
        path: &std::path::Path,
        bytes: Vec<u8>,
    ) -> Option<NativeArtifactId> {
        let mut state = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if !state.reserve_artifact(bytes.capacity().saturating_add(path.as_os_str().len())) {
            return None;
        }
        Some(state.store(
            owner,
            NativeArtifactPayload::Bytes {
                label,
                path: path.to_owned(),
                bytes,
            },
        ))
    }
    #[cfg(feature = "trust-ir-backend")]
    pub(crate) fn command(&self, command: &Command) -> Option<NativeArtifactId> {
        let mut state = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let mut bytes = command.get_program().len();
        for arg in command.get_args() {
            // Bound traversal before walking another actual argument.
            if !state.step() {
                return None;
            }
            bytes = bytes
                .saturating_add(arg.len())
                .saturating_add(size_of::<OsString>());
            if bytes > state.remaining() {
                state.gap(ObservationGap::Truncated(ObservationLimit::Bytes));
                return None;
            }
        }
        if !state.reserve_artifact(bytes) {
            return None;
        }
        Some(state.store(
            "actual backend command",
            NativeArtifactPayload::Command {
                program: command.get_program().to_owned(),
                arguments: command.get_args().map(ToOwned::to_owned).collect(),
            },
        ))
    }
}
impl State {
    pub(super) fn remaining(&self) -> usize {
        self.data
            .limits
            .native
            .byte_limit()
            .saturating_sub(self.data.bytes)
    }
    pub(super) fn gap(&mut self, gap: ObservationGap) {
        if self.stopped || self.sealed {
            return;
        }
        if matches!(gap, ObservationGap::Truncated(_)) {
            self.stopped = true;
            self.data.gaps.push(gap);
            return;
        }
        if self.reserve(size_of::<ObservationGap>()) {
            self.data.gaps.push(gap);
        }
    }
    pub(super) fn step(&mut self) -> bool {
        if self.stopped || self.sealed {
            return false;
        }
        if self.data.work == self.data.limits.native.work_limit() {
            self.gap(ObservationGap::Truncated(ObservationLimit::Work));
            return false;
        }
        self.data.work += 1;
        true
    }
    pub(super) fn reserve(&mut self, bytes: usize) -> bool {
        if self.stopped || self.sealed {
            return false;
        }
        if self.data.decisions.len() + self.data.gaps.len() == self.data.limits.native.event_limit()
        {
            self.gap(ObservationGap::Truncated(ObservationLimit::Events));
            return false;
        }
        if bytes > self.remaining() {
            self.gap(ObservationGap::Truncated(ObservationLimit::Bytes));
            return false;
        }
        if !self.step() {
            return false;
        }
        self.data.bytes += bytes;
        true
    }
    pub(super) fn reserve_artifact(&mut self, bytes: usize) -> bool {
        if self.data.artifacts.len() == self.data.limits.native.artifact_limit() {
            self.gap(ObservationGap::Truncated(ObservationLimit::Artifacts));
            return false;
        }
        self.reserve(bytes.saturating_add(size_of::<NativeRecordedArtifact>()))
    }
    fn reserve_context(&mut self, header: usize) -> bool {
        if self.data.contexts == self.data.limits.native.context_limit() {
            self.gap(ObservationGap::Truncated(ObservationLimit::Contexts));
            return false;
        }
        if !self.reserve_artifact(header.saturating_add(2 * size_of::<usize>())) {
            return false;
        }
        self.data.contexts += 1;
        true
    }
    pub(super) fn store(
        &mut self,
        owner: &'static str,
        payload: NativeArtifactPayload,
    ) -> NativeArtifactId {
        let id = NativeArtifactId {
            run: Arc::clone(&self.data.run),
            ordinal: self.data.artifacts.len(),
        };
        self.data.artifacts.push(NativeRecordedArtifact {
            id: id.clone(),
            owner,
            parent: self.source.clone(),
            inline: self.inline.clone(),
            payload,
        });
        id
    }
}

/// A reservation is consumed immediately by the actual owner. Payload movement
/// happens after metadata/context/work reservation, never via a second lookup.
pub(crate) struct NativeContextPermit<'a> {
    state: MutexGuard<'a, State>,
}
impl NativeContextPermit<'_> {
    pub(crate) fn prepared(mut self, info: ConstantInfo) -> Arc<ConstantInfo> {
        let info = Arc::new(info);
        let artifact = self.state.store(
            "actual prepared constant",
            NativeArtifactPayload::PreparedConstant(Arc::clone(&info)),
        );
        if self.state.reserve(size_of::<NativeDecision>()) {
            let context = self.state.source.clone();
            self.state.data.decisions.push(NativeDecision {
                role: NativeInvocationRole::Selection,
                owner: "prepare_native_constant",
                name: Some(info.name.clone()),
                target: None,
                context,
                artifact: Some(artifact),
                outcome: "actual prepared input moved and consumed",
            });
        }
        info
    }
    pub(crate) fn borrowed_environment(mut self, env: &Environment) {
        let source = self.state.source.clone();
        let actual=source.as_ref().is_some_and(|source|matches!(&self.state.data.artifacts[source.ordinal].payload,NativeArtifactPayload::Environment(original) if std::ptr::eq(env,original.as_ref())));
        if actual {
            if let Some(source) = source {
                let id = self.state.store(
                    "actual borrowed native inline environment",
                    NativeArtifactPayload::ContextAlias(source),
                );
                self.state.inline = Some(id);
            }
        } else {
            self.state.gap(ObservationGap::Unobserved {
                owner: "borrowed native inline environment",
                reason: "actual borrowed environment is not the retained source frame",
            });
        }
    }
    pub(crate) fn environment(mut self, env: Environment) -> Arc<Environment> {
        let env = Arc::new(env);
        let id = self.state.store(
            "actual native inline environment",
            NativeArtifactPayload::Environment(Arc::clone(&env)),
        );
        self.state.inline = Some(id);
        env
    }
}
