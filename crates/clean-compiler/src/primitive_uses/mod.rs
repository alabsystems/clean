// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Non-admitting observations made by the maintained compiler invocation.
//! Data here is not primitive permission, source ownership, ABI or proof.
//! Private producers bind actual inputs/artifacts; exported data cannot mint
//! another observed invocation. Missing or truncated recording stays explicit.

mod measure;
#[cfg(feature = "trust-ir-backend")]
mod owned;
mod pipeline;
#[cfg(feature = "trust-ir-backend")]
pub use owned::{
    compile_lcnf_to_trust_ir_owned_observed, OwnedCompilerInput, OwnedObservedCompilerOutput,
    OwnedObservedPipelineFailure, OwnedPipelineError,
};
mod record;
#[cfg(feature = "trust-ir-backend")]
mod serialized;

use crate::ir::{IRDecl, IRExpr, IRType};
use crate::lcnf::{Code, Decl, LetValue};
use crate::pass_manager::Phase;
use std::num::NonZeroUsize;
use std::sync::Arc;

pub use pipeline::{
    compile_lcnf_decls_observed_for, ObservedCompilerInput, ObservedPipelineFailure,
};
#[cfg(feature = "trust-ir-backend")]
pub use pipeline::{
    compile_lcnf_to_trust_ir_in_runtime_closure_observed, compile_lcnf_to_trust_ir_observed_for,
};
pub(crate) use record::{ObservationFrame, ObservationRecorder};

/// Additional recording limits, separate from compiler/capture policy.
/// Every budget is positive. They bound retained structural payload accounting and
/// recording traversal; the ordinary compiler output/work is unchanged.
#[derive(Clone, Copy, Debug)]
pub struct ObservationLimits {
    events: NonZeroUsize,
    artifacts: NonZeroUsize,
    contexts: NonZeroUsize,
    bytes: NonZeroUsize,
    work: NonZeroUsize,
}

#[derive(Clone, Copy, Debug, thiserror::Error)]
#[error("observation budgets must all be positive")]
pub struct InvalidObservationLimits;

impl ObservationLimits {
    pub fn new(
        events: usize,
        artifacts: usize,
        contexts: usize,
        bytes: usize,
        work: usize,
    ) -> Result<Self, InvalidObservationLimits> {
        Ok(Self {
            events: NonZeroUsize::new(events).ok_or(InvalidObservationLimits)?,
            artifacts: NonZeroUsize::new(artifacts).ok_or(InvalidObservationLimits)?,
            contexts: NonZeroUsize::new(contexts).ok_or(InvalidObservationLimits)?,
            bytes: NonZeroUsize::new(bytes).ok_or(InvalidObservationLimits)?,
            work: NonZeroUsize::new(work).ok_or(InvalidObservationLimits)?,
        })
    }
    pub fn event_limit(self) -> usize {
        self.events.get()
    }
    pub fn artifact_limit(self) -> usize {
        self.artifacts.get()
    }
    pub fn context_limit(self) -> usize {
        self.contexts.get()
    }
    pub fn byte_limit(self) -> usize {
        self.bytes.get()
    }
    pub fn work_limit(self) -> usize {
        self.work.get()
    }
    /// Recording clones no recursive syntax deeper than this finite ceiling.
    pub fn depth_limit(self) -> usize {
        self.work.get().min(256)
    }
}

impl Default for ObservationLimits {
    fn default() -> Self {
        Self {
            events: NonZeroUsize::new(100_000).expect("positive constant"),
            artifacts: NonZeroUsize::new(10_000).expect("positive constant"),
            contexts: NonZeroUsize::new(10_000).expect("positive constant"),
            bytes: NonZeroUsize::new(64 * 1024 * 1024).expect("positive constant"),
            work: NonZeroUsize::new(1_000_000).expect("positive constant"),
        }
    }
}

/// A local artifact identity, not a hash/permission certificate.
#[derive(Clone)]
pub struct ArtifactId {
    run: Arc<()>,
    ordinal: usize,
}
impl ArtifactId {
    pub fn ordinal(&self) -> usize {
        self.ordinal
    }
    pub fn same_run(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.run, &other.run)
    }
}
impl PartialEq for ArtifactId {
    fn eq(&self, other: &Self) -> bool {
        self.ordinal == other.ordinal && self.same_run(other)
    }
}
impl Eq for ArtifactId {}
impl std::fmt::Debug for ArtifactId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ArtifactId")
            .field("ordinal", &self.ordinal)
            .finish_non_exhaustive()
    }
}

/// Why this invocation ran. Only Consumed decisions populate `decisions`.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum InvocationRole {
    Consumed,
    PrefixReplay(Phase),
    DependencyProbe,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum ObservationLimit {
    Events,
    Artifacts,
    Contexts,
    Bytes,
    Work,
    Depth,
}

/// Status facts only. No variant authorizes compilation or source semantics.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub enum ObservationGap {
    Truncated(ObservationLimit),
    Unobserved {
        owner: &'static str,
        reason: &'static str,
    },
    Failed {
        owner: &'static str,
        error: &'static str,
    },
}

/// Actual emitter operations selected by existing owner branches. These reuse
/// TrustIR's operator/type vocabulary; a recorded route is never permission.
#[cfg(feature = "trust-ir-backend")]
#[derive(Clone, Debug)]
#[non_exhaustive]
pub enum EmissionOperation {
    BinOp {
        op: trust_ir::inst::BinOp,
        ty: trust_ir::Ty,
        lhs: trust_ir::ValueId,
        rhs: trust_ir::ValueId,
    },
    Comparison {
        op: trust_ir::inst::ICmpOp,
        ty: trust_ir::Ty,
        lhs: trust_ir::ValueId,
        rhs: trust_ir::ValueId,
    },
    Cast {
        op: trust_ir::inst::CastOp,
        from: trust_ir::Ty,
        to: trust_ir::Ty,
        input: trust_ir::ValueId,
    },
    Call {
        callee: trust_ir::FuncId,
        arguments: Arc<[trust_ir::ValueId]>,
    },
    Route(&'static str),
    Value(trust_ir::ValueId),
}

/// Reuses the actual existing input/output operation grammar.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub enum ArtifactPayload {
    LcnfDeclarations(Arc<[Decl]>),
    LcnfCode(Arc<Code>),
    LcnfValue(Arc<LetValue>),
    IrDeclarations(Arc<[IRDecl]>),
    IrExpression {
        value: Arc<IRExpr>,
        ty: IRType,
    },
    #[cfg(feature = "trust-ir-backend")]
    TrustIrModule(Arc<trust_ir::Module>),
    #[cfg(feature = "trust-ir-backend")]
    EmissionOperation(EmissionOperation),
    #[cfg(feature = "trust-ir-backend")]
    EmitterInput {
        value: Arc<IRExpr>,
        ty: IRType,
        operands: Arc<[(crate::ir::VarId, Option<IRType>, Option<trust_ir::ValueId>)]>,
    },
}

#[derive(Clone, Debug)]
pub struct RecordedArtifact {
    id: ArtifactId,
    owner: &'static str,
    parent: Option<ArtifactId>,
    payload: ArtifactPayload,
}
impl RecordedArtifact {
    pub fn parent(&self) -> Option<&ArtifactId> {
        self.parent.as_ref()
    }
    pub fn id(&self) -> &ArtifactId {
        &self.id
    }
    pub fn owner(&self) -> &'static str {
        self.owner
    }
    pub fn payload(&self) -> &ArtifactPayload {
        &self.payload
    }
}

/// One actual invocation/dispatch decision, retaining pre-erasure evidence.
#[derive(Clone, Debug)]
pub struct PrimitiveDecision {
    owner: &'static str,
    occurrence: usize,
    iteration: usize,
    before: ArtifactId,
    after: Option<ArtifactId>,
    note: &'static str,
}
impl PrimitiveDecision {
    pub fn owner(&self) -> &'static str {
        self.owner
    }
    pub fn occurrence(&self) -> usize {
        self.occurrence
    }
    pub fn iteration(&self) -> usize {
        self.iteration
    }
    pub fn before(&self) -> &ArtifactId {
        &self.before
    }
    pub fn after(&self) -> Option<&ArtifactId> {
        self.after.as_ref()
    }
    pub fn note(&self) -> &'static str {
        self.note
    }
}

#[derive(Clone, Debug)]
pub struct DiagnosticRun {
    role: InvocationRole,
    decisions: Vec<PrimitiveDecision>,
}
impl DiagnosticRun {
    pub fn role(&self) -> &InvocationRole {
        &self.role
    }
    pub fn decisions(&self) -> &[PrimitiveDecision] {
        &self.decisions
    }
}

/// Immutable data from one actual compiler run, never an admission token.
#[derive(Clone, Debug)]
pub struct PrimitiveUseObservations {
    run: Arc<()>,
    artifacts: Vec<RecordedArtifact>,
    decisions: Vec<PrimitiveDecision>,
    diagnostics: Vec<DiagnosticRun>,
    gaps: Vec<ObservationGap>,
    limits: ObservationLimits,
    retained_bytes: usize,
    contexts: usize,
    work: usize,
}
impl PrimitiveUseObservations {
    pub fn artifacts(&self) -> &[RecordedArtifact] {
        &self.artifacts
    }
    pub fn decisions(&self) -> &[PrimitiveDecision] {
        &self.decisions
    }
    pub fn diagnostic_runs(&self) -> &[DiagnosticRun] {
        &self.diagnostics
    }
    pub fn gaps(&self) -> &[ObservationGap] {
        &self.gaps
    }
    pub fn limits(&self) -> ObservationLimits {
        self.limits
    }
    pub fn retained_contexts(&self) -> usize {
        self.contexts
    }
    pub fn retained_bytes(&self) -> usize {
        self.retained_bytes
    }
    pub fn recording_work(&self) -> usize {
        self.work
    }
    pub fn artifact(&self, id: &ArtifactId) -> Option<&RecordedArtifact> {
        if !Arc::ptr_eq(&self.run, &id.run) {
            return None;
        }
        self.artifacts.get(id.ordinal)
    }
}

/// Actual immutable artifact plus observations. No public constructor or
/// mutable artifact access can attach data to a caller's different artifact.
#[derive(Debug)]
pub struct ObservedCompilerOutput<'a, T> {
    input: Option<ObservedCompilerInput<'a>>,
    artifact: T,
    observations: PrimitiveUseObservations,
}
impl<T> ObservedCompilerOutput<'_, T> {
    pub fn input(&self) -> Option<&ObservedCompilerInput<'_>> {
        self.input.as_ref()
    }
    pub fn artifact(&self) -> &T {
        &self.artifact
    }
    pub fn observations(&self) -> &PrimitiveUseObservations {
        &self.observations
    }
}

#[cfg(test)]
mod tests;

#[cfg(all(test, feature = "trust-ir-backend"))]
mod dispatch_tests;

#[cfg(all(test, feature = "trust-ir-backend"))]
mod owned_tests;

#[cfg(all(test, feature = "trust-ir-backend"))]
mod data_dispatch_tests;

#[cfg(all(test, feature = "trust-ir-backend"))]
mod retention_tests;
