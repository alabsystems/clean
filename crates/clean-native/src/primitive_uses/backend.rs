// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Data from the actual invoked backend. No module is decoded/imported here.
use super::*;
use clean_compiler::primitive_uses::{ObservationGap, ObservationLimit};
use std::io::Read;
use std::path::Path;
use std::process::{Command, Output};

impl NativeRecorder {
    pub(crate) fn license(&self, census: &clean_compiler::emit_trust_ir_lane::LicenseCensus) {
        let mut state = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let mut bytes = 0usize;
        for authority in census.kept.keys() {
            if !state.step() {
                return;
            }
            bytes = bytes
                .saturating_add(authority.len())
                .saturating_add(size_of::<(String, usize)>() + 4 * size_of::<usize>());
            if bytes > state.remaining() {
                state.gap(ObservationGap::Truncated(ObservationLimit::Bytes));
                return;
            }
        }
        if !state.reserve_artifact(bytes) {
            return;
        }
        let id = state.store(
            "actual native license census",
            NativeArtifactPayload::LicenseCensus(census.clone()),
        );
        drop(state);
        self.edge(
            NativeInvocationRole::ConsumedCompilation,
            "actual native license mutation",
            None,
            Some(&id),
            "result of existing checked private license; data grants no authority",
        );
    }

    pub(crate) fn runtime(&self, runtime: &crate::native_runtime::RuntimeArchive) {
        let mut state = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let mut bytes = runtime.cc.len().saturating_add(runtime.ar.len());
        for (_, path) in &runtime.objects {
            if !state.step() {
                return;
            }
            bytes = bytes
                .saturating_add(size_of::<(crate::native_runtime::RuntimeMember, PathBuf)>())
                .saturating_add(path.as_os_str().len());
            if bytes > state.remaining() {
                state.gap(ObservationGap::Truncated(ObservationLimit::Bytes));
                return;
            }
        }
        if !state.reserve_artifact(bytes) {
            return;
        }
        let id = state.store(
            "actual built C runtime",
            NativeArtifactPayload::RuntimeArchive {
                compiler: runtime.cc.clone(),
                archiver: runtime.ar.clone(),
                members: runtime
                    .objects
                    .iter()
                    .map(|(member, path)| RuntimeMemberObservation {
                        member: *member,
                        path: path.clone(),
                    })
                    .collect(),
            },
        );
        drop(state);
        for (_, path) in &runtime.objects {
            self.file("actual C runtime member", path, Some(&id));
        }
    }

    pub(crate) fn shim_demand(
        &self,
        context: Option<&NativeArtifactId>,
        signature: &clean_compiler::emit_trust_ir_lane::LinkSignature,
        definition: Option<&'static str>,
        mismatch: Option<&str>,
    ) {
        use clean_compiler::emit_trust_ir_lane::AbiSlot;
        let mut state = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let mut bytes = signature
            .symbol
            .len()
            .saturating_add(mismatch.map_or(0, str::len));
        for slot in signature.params.iter().chain(&signature.returns) {
            if !state.step() {
                return;
            }
            bytes = bytes
                .saturating_add(size_of::<AbiSlot>())
                .saturating_add(match slot {
                    AbiSlot::Ptr => 0,
                    AbiSlot::Other(text) => text.len(),
                });
            if bytes > state.remaining() {
                state.gap(ObservationGap::Truncated(ObservationLimit::Bytes));
                return;
            }
        }
        if !state.reserve_artifact(bytes) {
            return;
        }
        let id = state.store(
            "actual prelude shim demand",
            NativeArtifactPayload::ShimDemand {
                signature: signature.clone(),
                definition,
                mismatch: mismatch.map(ToOwned::to_owned),
            },
        );
        drop(state);
        self.edge(
            NativeInvocationRole::ConsumedCompilation,
            "actual prelude shim selection",
            context,
            Some(&id),
            if definition.is_none() {
                "actual absent shim"
            } else if mismatch.is_some() {
                "actual shim ABI refusal"
            } else {
                "actual shim ABI match; no primitive permission"
            },
        );
    }

    pub(crate) fn edge(
        &self,
        role: NativeInvocationRole,
        owner: &'static str,
        context: Option<&NativeArtifactId>,
        artifact: Option<&NativeArtifactId>,
        outcome: &'static str,
    ) {
        let mut state = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if context
            .into_iter()
            .chain(artifact)
            .any(|id| !Arc::ptr_eq(&id.run, &state.data.run))
        {
            state.gap(ObservationGap::Unobserved {
                owner: "native event affinity",
                reason: "foreign run artifact was refused",
            });
            return;
        }
        if !state.reserve(size_of::<NativeDecision>()) {
            return;
        }
        state.data.decisions.push(NativeDecision {
            role,
            owner,
            name: None,
            target: None,
            context: context.cloned(),
            artifact: artifact.cloned(),
            outcome,
        });
    }
    pub(crate) fn before_backend(
        &self,
        command: &Command,
        input: &Path,
        bytes: Vec<u8>,
    ) -> Option<NativeArtifactId> {
        let image = self.bytes(
            "actual post-license backend module",
            "TMBC input written",
            input,
            bytes,
        );
        let invocation = self.command(command);
        self.edge(
            NativeInvocationRole::Backend,
            "actual backend invocation",
            image.as_ref(),
            invocation.as_ref(),
            "exact produced input bytes and consumed Command arguments",
        );
        self.gap(ObservationGap::Unobserved{owner:"backend inherited process context",reason:"explicit program/arguments recorded; inherited environment/cwd are not an owned snapshot"});
        invocation
    }
    fn byte_copy(
        &self,
        owner: &'static str,
        label: &'static str,
        path: &Path,
        bytes: &[u8],
    ) -> Option<NativeArtifactId> {
        let mut state = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if !state.reserve_artifact(bytes.len().saturating_add(path.as_os_str().len())) {
            return None;
        }
        Some(state.store(
            owner,
            NativeArtifactPayload::Bytes {
                label,
                path: path.to_owned(),
                bytes: bytes.to_vec(),
            },
        ))
    }
    pub(crate) fn after_backend(
        &self,
        invocation: Option<&NativeArtifactId>,
        object: &Path,
        output: &Output,
    ) -> Option<NativeArtifactId> {
        let stdout = self.byte_copy("actual backend output", "stdout", object, &output.stdout);
        self.edge(
            NativeInvocationRole::Backend,
            "actual backend stdout",
            invocation,
            stdout.as_ref(),
            "actual completed process output",
        );
        let stderr = self.byte_copy("actual backend output", "stderr", object, &output.stderr);
        self.edge(
            NativeInvocationRole::Backend,
            "actual backend stderr",
            invocation,
            stderr.as_ref(),
            if output.status.success() {
                "actual backend exited successfully"
            } else {
                "actual backend refusal"
            },
        );
        let status = {
            let mut state = self
                .state
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            state.reserve_artifact(0).then(|| {
                state.store(
                    "actual backend status",
                    NativeArtifactPayload::ProcessStatus {
                        success: output.status.success(),
                        code: output.status.code(),
                    },
                )
            })
        };
        self.edge(
            NativeInvocationRole::Backend,
            "actual backend process status",
            invocation,
            status.as_ref(),
            "observed process exit only; no permission",
        );
        self.file("actual backend object", object, invocation)
    }
    pub(crate) fn file(
        &self,
        owner: &'static str,
        path: &Path,
        parent: Option<&NativeArtifactId>,
    ) -> Option<NativeArtifactId> {
        let mut state = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if state.stopped || state.sealed {
            return None;
        }
        let available = state
            .remaining()
            .saturating_sub(size_of::<NativeRecordedArtifact>())
            .saturating_sub(path.as_os_str().len());
        if !state.step() {
            return None;
        }
        let metadata = match std::fs::metadata(path) {
            Ok(metadata) => metadata,
            Err(_) => {
                state.gap(ObservationGap::Unobserved {
                    owner,
                    reason: "actual artifact unavailable for bounded retention",
                });
                return None;
            }
        };
        if metadata.len() > available as u64 {
            state.gap(ObservationGap::Truncated(ObservationLimit::Bytes));
            return None;
        }
        let file = match std::fs::File::open(path) {
            Ok(file) => file,
            Err(_) => {
                state.gap(ObservationGap::Unobserved {
                    owner,
                    reason: "actual artifact could not be opened",
                });
                return None;
            }
        };
        let mut bytes = Vec::new();
        if file
            .take(available.saturating_add(1) as u64)
            .read_to_end(&mut bytes)
            .is_err()
        {
            state.gap(ObservationGap::Unobserved {
                owner,
                reason: "bounded artifact read failed",
            });
            return None;
        }
        if bytes.capacity() > available {
            state.gap(ObservationGap::Truncated(ObservationLimit::Bytes));
            return None;
        }
        if !state.reserve_artifact(bytes.capacity().saturating_add(path.as_os_str().len())) {
            return None;
        }
        let id = state.store(
            owner,
            NativeArtifactPayload::Bytes {
                label: "actual output artifact",
                path: path.to_owned(),
                bytes,
            },
        );
        drop(state);
        self.edge(
            NativeInvocationRole::Backend,
            owner,
            parent,
            Some(&id),
            "actual retained file bytes",
        );
        Some(id)
    }
}
