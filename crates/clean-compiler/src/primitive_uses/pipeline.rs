// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::implemented_by::CodeMeaning;
use crate::pass_manager::{PipelineArtifacts, PipelineConfig, PipelineError};
use clean_kernel::Environment;

/// The actual inputs retained as one immutable borrow for this run. This is
/// not an owned environment snapshot, and invokes no additional lazy lookup.
#[derive(Debug)]
pub struct ObservedCompilerInput<'a> {
    declarations: &'a [Decl],
    environment: &'a Environment,
    config: &'a PipelineConfig,
    meaning: CodeMeaning,
    closure: Option<&'a crate::RuntimeBindingClosure>,
    #[cfg(feature = "trust-ir-backend")]
    emit_config: Option<&'a crate::emit_trust_ir::TrustIrConfig>,
}
impl ObservedCompilerInput<'_> {
    pub fn declarations(&self) -> &[Decl] {
        self.declarations
    }
    pub fn environment(&self) -> &Environment {
        self.environment
    }
    pub fn config(&self) -> &PipelineConfig {
        self.config
    }
    pub fn meaning(&self) -> CodeMeaning {
        self.meaning
    }
    pub fn runtime_closure(&self) -> Option<&crate::RuntimeBindingClosure> {
        self.closure
    }
    #[cfg(feature = "trust-ir-backend")]
    pub fn emit_config(&self) -> Option<&crate::emit_trust_ir::TrustIrConfig> {
        self.emit_config
    }
}

/// The original compiler refusal and the actual bounded observations made
/// before it. Observation incompleteness never replaces a compiler result.
#[derive(Debug)]
pub struct ObservedPipelineFailure<'a> {
    input: Option<ObservedCompilerInput<'a>>,
    error: PipelineError,
    observations: PrimitiveUseObservations,
}
impl ObservedPipelineFailure<'_> {
    pub fn input(&self) -> Option<&ObservedCompilerInput<'_>> {
        self.input.as_ref()
    }
    pub fn error(&self) -> &PipelineError {
        &self.error
    }
    pub fn observations(&self) -> &PrimitiveUseObservations {
        &self.observations
    }
}

/// Run the maintained compiler with non-admitting bounded recording. Inputs
/// remain immutably borrowed; no public detach/rebind constructor exists.
pub fn compile_lcnf_decls_observed_for<'a>(
    decls: &'a [Decl],
    env: &'a Environment,
    config: &'a PipelineConfig,
    meaning: CodeMeaning,
    limits: ObservationLimits,
) -> Result<ObservedCompilerOutput<'a, PipelineArtifacts>, ObservedPipelineFailure<'a>> {
    let input = ObservedCompilerInput {
        declarations: decls,
        environment: env,
        config,
        meaning,
        closure: None,
        #[cfg(feature = "trust-ir-backend")]
        emit_config: None,
    };
    observe(input, limits, |frame| {
        crate::pass_manager::pipeline::compile_lcnf_decls_recording(
            decls,
            env,
            config,
            crate::rc_repair::RcRepairMode::Enabled,
            meaning,
            None,
            Some(frame),
        )
    })
}

fn observe<'a, T>(
    input: ObservedCompilerInput<'a>,
    limits: ObservationLimits,
    run: impl FnOnce(&ObservationFrame) -> Result<T, PipelineError>,
) -> Result<ObservedCompilerOutput<'a, T>, ObservedPipelineFailure<'a>> {
    let recorder = ObservationRecorder::new(limits);
    let keep_context = recorder.input_context();
    let frame = recorder.frame(InvocationRole::Consumed, 0, 0);
    if input.environment.has_constant_source() {
        frame.gap(ObservationGap::Unobserved {
            owner: "lazy environment source",
            reason: "immutable environment borrow is not an owned snapshot of callback results",
        });
    }
    let before = frame.declarations("actual invocation input", input.declarations);
    frame.decision(
        "actual invocation",
        before,
        None,
        "shared immutable input/environment/config borrow",
    );
    let result = run(&frame);
    if result.is_err() {
        frame.gap(ObservationGap::Failed {
            owner: "pipeline",
            error: "actual compiler refusal retained in error",
        });
    }
    let observations = recorder.finish();
    let input = keep_context.then_some(input);
    match result {
        Ok(artifact) => Ok(ObservedCompilerOutput {
            input,
            artifact,
            observations,
        }),
        Err(error) => Err(ObservedPipelineFailure {
            input,
            error,
            observations,
        }),
    }
}

#[cfg(feature = "trust-ir-backend")]
#[allow(clippy::too_many_arguments)]
fn trust_ir<'a>(
    decls: &'a [Decl],
    env: &'a Environment,
    config: &'a PipelineConfig,
    emit: &'a crate::emit_trust_ir::TrustIrConfig,
    meaning: CodeMeaning,
    closure: Option<&'a crate::RuntimeBindingClosure>,
    limits: ObservationLimits,
) -> Result<
    ObservedCompilerOutput<'a, crate::pass_manager::TrustIrPipelineData>,
    ObservedPipelineFailure<'a>,
> {
    let input = ObservedCompilerInput {
        declarations: decls,
        environment: env,
        config,
        meaning,
        closure,
        emit_config: Some(emit),
    };
    observe(input, limits, |frame| {
        crate::pass_manager::pipeline::compile_lcnf_to_trust_ir_recording(
            decls,
            env,
            config,
            emit,
            meaning,
            closure,
            Some(frame),
        )
    })
}

#[cfg(feature = "trust-ir-backend")]
pub fn compile_lcnf_to_trust_ir_observed_for<'a>(
    decls: &'a [Decl],
    env: &'a Environment,
    config: &'a PipelineConfig,
    emit: &'a crate::emit_trust_ir::TrustIrConfig,
    meaning: CodeMeaning,
    limits: ObservationLimits,
) -> Result<
    ObservedCompilerOutput<'a, crate::pass_manager::TrustIrPipelineData>,
    ObservedPipelineFailure<'a>,
> {
    trust_ir(decls, env, config, emit, meaning, None, limits)
}

#[cfg(feature = "trust-ir-backend")]
pub fn compile_lcnf_to_trust_ir_in_runtime_closure_observed<'a>(
    decls: &'a [Decl],
    env: &'a Environment,
    config: &'a PipelineConfig,
    emit: &'a crate::emit_trust_ir::TrustIrConfig,
    closure: &'a crate::RuntimeBindingClosure,
    limits: ObservationLimits,
) -> Result<
    ObservedCompilerOutput<'a, crate::pass_manager::TrustIrPipelineData>,
    ObservedPipelineFailure<'a>,
> {
    trust_ir(
        decls,
        env,
        config,
        emit,
        CodeMeaning::LeanCompiled,
        Some(closure),
        limits,
    )
}
