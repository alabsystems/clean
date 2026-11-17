// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Non-admitting observations at actual native selection and backend owners.
//! Source/ABI/prototype/license/thread guards are unchanged. Identity data and
//! success statuses are never primitive permission or binary proof.
#[cfg(feature = "trust-ir-backend")]
mod backend;
#[cfg(feature = "trust-ir-backend")]
mod owned;
#[cfg(feature = "trust-ir-backend")]
pub(crate) use owned::NativeOwnedInputs;
mod record;
use clean_compiler::primitive_uses::{ObservationGap, ObservationLimits};
use clean_kernel::{ConstantInfo, Environment, Name};
pub(crate) use record::NativeRecorder;
use std::ffi::OsString;
use std::path::PathBuf;
use std::sync::Arc;

/// Separate finite allowances for native routing/backend records and the
/// maintained compiler's records. Dynamic retention is bounded by their SUM.
/// Actual pre-existing input payload Arcs extend source/intermediate lifetimes;
/// this does not bound their total memory or the ordinary compiler's artifacts.
#[derive(Debug, Clone, Copy)]
pub struct NativeObservationLimits {
    native: ObservationLimits,
    compiler: ObservationLimits,
}
impl NativeObservationLimits {
    pub fn new(native: ObservationLimits, compiler: ObservationLimits) -> Self {
        Self { native, compiler }
    }
    pub fn native(self) -> ObservationLimits {
        self.native
    }
    pub fn compiler(self) -> ObservationLimits {
        self.compiler
    }
}
impl Default for NativeObservationLimits {
    fn default() -> Self {
        Self::new(ObservationLimits::default(), ObservationLimits::default())
    }
}

#[derive(Clone)]
pub struct NativeArtifactId {
    run: Arc<()>,
    ordinal: usize,
}
impl NativeArtifactId {
    pub fn ordinal(&self) -> usize {
        self.ordinal
    }
}
impl PartialEq for NativeArtifactId {
    fn eq(&self, other: &Self) -> bool {
        self.ordinal == other.ordinal && Arc::ptr_eq(&self.run, &other.run)
    }
}
impl Eq for NativeArtifactId {}
impl std::fmt::Debug for NativeArtifactId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NativeArtifactId")
            .field("ordinal", &self.ordinal)
            .finish_non_exhaustive()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum NativeInvocationRole {
    Selection,
    DependencyProbe,
    ConsumedCompilation,
    Backend,
}

/// Actual member of the existing runtime build, not a statement it was used.
#[cfg(feature = "trust-ir-backend")]
#[derive(Debug)]
pub struct RuntimeMemberObservation {
    pub(super) member: crate::native_runtime::RuntimeMember,
    pub(super) path: PathBuf,
}
#[cfg(feature = "trust-ir-backend")]
impl RuntimeMemberObservation {
    pub fn object_name(&self) -> &'static str {
        self.member.object_name()
    }
    pub fn source_name(&self) -> &'static str {
        self.member.source_name()
    }
    pub fn path(&self) -> &std::path::Path {
        &self.path
    }
}

/// Actual values created/consumed by native selection. These are immutable
/// source/intermediate inputs, never imported-source or runtime capability.
#[derive(Debug)]
#[non_exhaustive]
pub enum NativeArtifactPayload {
    Environment(Arc<Environment>),
    ContextAlias(NativeArtifactId),
    PreparedConstant(Arc<ConstantInfo>),
    Bytes {
        label: &'static str,
        path: PathBuf,
        bytes: Vec<u8>,
    },
    #[cfg(feature = "trust-ir-backend")]
    ShimDemand {
        signature: clean_compiler::emit_trust_ir_lane::LinkSignature,
        definition: Option<&'static str>,
        mismatch: Option<String>,
    },
    #[cfg(feature = "trust-ir-backend")]
    RuntimeArchive {
        compiler: String,
        archiver: String,
        members: Vec<RuntimeMemberObservation>,
    },
    #[cfg(feature = "trust-ir-backend")]
    LicenseCensus(clean_compiler::emit_trust_ir_lane::LicenseCensus),
    ProcessStatus {
        success: bool,
        code: Option<i32>,
    },
    Command {
        program: OsString,
        arguments: Vec<OsString>,
    },
}
#[derive(Debug)]
pub struct NativeRecordedArtifact {
    id: NativeArtifactId,
    owner: &'static str,
    parent: Option<NativeArtifactId>,
    inline: Option<NativeArtifactId>,
    payload: NativeArtifactPayload,
}
impl NativeRecordedArtifact {
    pub fn parent(&self) -> Option<&NativeArtifactId> {
        self.parent.as_ref()
    }
    pub fn inline_context(&self) -> Option<&NativeArtifactId> {
        self.inline.as_ref()
    }
    pub fn id(&self) -> &NativeArtifactId {
        &self.id
    }
    pub fn owner(&self) -> &'static str {
        self.owner
    }
    pub fn payload(&self) -> &NativeArtifactPayload {
        &self.payload
    }
}
/// An actual owner-branch outcome; labels are site facts, not a classifier.
#[derive(Debug)]
pub struct NativeDecision {
    role: NativeInvocationRole,
    owner: &'static str,
    name: Option<Name>,
    target: Option<Name>,
    context: Option<NativeArtifactId>,
    artifact: Option<NativeArtifactId>,
    outcome: &'static str,
}
impl NativeDecision {
    pub fn role(&self) -> NativeInvocationRole {
        self.role
    }
    pub fn owner(&self) -> &'static str {
        self.owner
    }
    pub fn name(&self) -> Option<&Name> {
        self.name.as_ref()
    }
    pub fn target(&self) -> Option<&Name> {
        self.target.as_ref()
    }
    pub fn context(&self) -> Option<&NativeArtifactId> {
        self.context.as_ref()
    }
    pub fn artifact(&self) -> Option<&NativeArtifactId> {
        self.artifact.as_ref()
    }
    pub fn outcome(&self) -> &'static str {
        self.outcome
    }
}

#[derive(Debug)]
pub struct NativePrimitiveUseObservations {
    run: Arc<()>,
    limits: NativeObservationLimits,
    artifacts: Vec<NativeRecordedArtifact>,
    decisions: Vec<NativeDecision>,
    gaps: Vec<ObservationGap>,
    bytes: usize,
    work: usize,
    contexts: usize,
    #[cfg(feature = "trust-ir-backend")]
    compiler: Option<Arc<clean_compiler::primitive_uses::OwnedObservedCompilerOutput>>,
}
impl NativePrimitiveUseObservations {
    pub fn limits(&self) -> NativeObservationLimits {
        self.limits
    }
    pub fn artifacts(&self) -> &[NativeRecordedArtifact] {
        &self.artifacts
    }
    pub fn decisions(&self) -> &[NativeDecision] {
        &self.decisions
    }
    pub fn gaps(&self) -> &[ObservationGap] {
        &self.gaps
    }
    pub fn native_retained_bytes(&self) -> usize {
        self.bytes
    }
    pub fn native_recording_work(&self) -> usize {
        self.work
    }
    pub fn retained_contexts(&self) -> usize {
        self.contexts
    }
    pub fn artifact(&self, id: &NativeArtifactId) -> Option<&NativeRecordedArtifact> {
        Arc::ptr_eq(&self.run, &id.run)
            .then(|| self.artifacts.get(id.ordinal))
            .flatten()
    }
    #[cfg(feature = "trust-ir-backend")]
    pub fn compiler(&self) -> Option<&clean_compiler::primitive_uses::OwnedObservedCompilerOutput> {
        self.compiler.as_deref()
    }
}

#[cfg(all(test, feature = "trust-ir-backend"))]
mod tests;
