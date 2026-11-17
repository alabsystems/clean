// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Actual owned invocation frames and explicit opaque consumers; no admission.
use super::*;
use crate::implemented_by::CodeMeaning;
use crate::pass_manager::{PipelineConfig, PipelineError, TrustIrPipelineData};
use clean_kernel::Environment;

/// Exact actual owned invocation inputs. These Arcs extend the lifetime of
/// potentially large pre-existing inputs; frame size is NOT a total memory bound.
#[derive(Debug)]
pub struct OwnedCompilerInput {
    declarations: Arc<[Decl]>,
    environment: Arc<Environment>,
    config: Arc<PipelineConfig>,
    emit_config: crate::emit_trust_ir::TrustIrConfig,
    meaning: CodeMeaning,
    closure: Option<Arc<crate::RuntimeBindingClosure>>,
}
impl OwnedCompilerInput {
    pub fn declarations(&self) -> &[Decl] {
        &self.declarations
    }
    pub fn environment(&self) -> &Environment {
        &self.environment
    }
    pub fn config(&self) -> &PipelineConfig {
        &self.config
    }
    pub fn emit_config(&self) -> &crate::emit_trust_ir::TrustIrConfig {
        &self.emit_config
    }
    pub fn meaning(&self) -> CodeMeaning {
        self.meaning
    }
    pub fn runtime_closure(&self) -> Option<&crate::RuntimeBindingClosure> {
        self.closure.as_deref()
    }
}
#[derive(Debug)]
pub struct OwnedObservedCompilerOutput {
    input: Option<Arc<OwnedCompilerInput>>,
    artifact: TrustIrPipelineData,
    observations: PrimitiveUseObservations,
}
impl OwnedObservedCompilerOutput {
    pub fn input(&self) -> Option<&OwnedCompilerInput> {
        self.input.as_deref()
    }
    pub fn artifact(&self) -> &TrustIrPipelineData {
        &self.artifact
    }
    pub fn observations(&self) -> &PrimitiveUseObservations {
        &self.observations
    }
}
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum OwnedPipelineError<E> {
    #[error(transparent)]
    Compiler(PipelineError),
    #[error("{0}")]
    Consumer(E),
}
#[derive(Debug, thiserror::Error)]
#[error("{error}")]
pub struct OwnedObservedPipelineFailure<E> {
    input: Option<Arc<OwnedCompilerInput>>,
    error: OwnedPipelineError<E>,
    observations: PrimitiveUseObservations,
}
impl<E> OwnedObservedPipelineFailure<E> {
    pub fn input(&self) -> Option<&OwnedCompilerInput> {
        self.input.as_deref()
    }
    pub fn error(&self) -> &OwnedPipelineError<E> {
        &self.error
    }
    pub fn observations(&self) -> &PrimitiveUseObservations {
        &self.observations
    }
}

/// Always executes the same compiler and explicit continuation. The continuation
/// is opaque even when it succeeds; no name/bool/hash asserts coverage or rights.
#[allow(clippy::too_many_arguments)]
pub fn compile_lcnf_to_trust_ir_owned_observed<E>(
    declarations: Arc<[Decl]>,
    environment: Arc<Environment>,
    config: Arc<PipelineConfig>,
    emit_config: crate::emit_trust_ir::TrustIrConfig,
    meaning: CodeMeaning,
    closure: Option<Arc<crate::RuntimeBindingClosure>>,
    limits: ObservationLimits,
    consumer: impl FnOnce(&mut trust_ir::Module) -> Result<(), E>,
) -> Result<OwnedObservedCompilerOutput, OwnedObservedPipelineFailure<E>> {
    let input = Arc::new(OwnedCompilerInput {
        declarations,
        environment,
        config,
        emit_config,
        meaning,
        closure,
    });
    let recorder = ObservationRecorder::new(limits);
    let keep_context = recorder.shared_context::<OwnedCompilerInput>();
    let frame = recorder.frame(InvocationRole::Consumed, 0, 0);
    if input.environment.has_constant_source() {
        frame.gap(ObservationGap::Unobserved {
            owner: "lazy environment source",
            reason: "owned environment Arc is not an owned snapshot of callback results",
        });
    }
    let before = frame.declarations("actual owned invocation input", &input.declarations);
    frame.decision(
        "actual owned invocation",
        before,
        None,
        "same owned immutable input frame actually compiled",
    );
    let result = crate::pass_manager::pipeline::compile_lcnf_to_trust_ir_recording(
        &input.declarations,
        &input.environment,
        &input.config,
        &input.emit_config,
        input.meaning,
        input.closure.as_deref(),
        Some(&frame),
    );
    let result = match result {
        Err(error) => Err(OwnedPipelineError::Compiler(error)),
        Ok(mut data) => {
            let before = frame.module("actual module before opaque consumer", &data.module);
            frame.gap(ObservationGap::Unobserved {
                owner: "external consumer continuation",
                reason: "arbitrary code is opaque regardless of name or success",
            });
            let consumed = consumer(&mut data.module);
            let after = frame.module("actual module after opaque consumer", &data.module);
            frame.decision(
                "external consumer continuation",
                before,
                after,
                "actual mutable consumer invocation; no coverage/permission",
            );
            match consumed {
                Ok(()) => Ok(data),
                Err(error) => Err(OwnedPipelineError::Consumer(error)),
            }
        }
    };
    if result.is_err() {
        frame.gap(ObservationGap::Failed {
            owner: "owned pipeline",
            error: "actual typed compiler/consumer refusal retained",
        });
    }
    let observations = recorder.finish();
    let input = keep_context.then_some(input);
    match result {
        Ok(artifact) => Ok(OwnedObservedCompilerOutput {
            input,
            artifact,
            observations,
        }),
        Err(error) => Err(OwnedObservedPipelineFailure {
            input,
            error,
            observations,
        }),
    }
}
