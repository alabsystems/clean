// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Source-only observed constructor. No ABI/admission condition is supplied by
//! observations; the same existing scalar constructor checks every input.
use super::*;
use crate::primitive_uses::{
    NativeObservationLimits, NativeOwnedInputs, NativePrimitiveUseObservations, NativeRecorder,
};
use clean_compiler::primitive_uses::{ObservationGap, OwnedObservedPipelineFailure};

#[derive(Clone, Copy)]
pub(super) enum ScalarSelectedInput<'a> {
    Borrowed {
        decls: &'a [Decl],
        env: &'a Environment,
        pipeline: &'a PipelineConfig,
        closure: Option<&'a clean_compiler::RuntimeBindingClosure>,
    },
    Observed {
        input: &'a NativeOwnedInputs,
        observer: &'a NativeRecorder,
    },
}
impl<'a> ScalarSelectedInput<'a> {
    pub(super) fn parts(
        self,
    ) -> (
        &'a [Decl],
        &'a Environment,
        &'a PipelineConfig,
        Option<&'a clean_compiler::RuntimeBindingClosure>,
    ) {
        match self {
            Self::Borrowed {
                decls,
                env,
                pipeline,
                closure,
            } => (decls, env, pipeline, closure),
            Self::Observed { input, .. } => (
                &input.decls,
                &input.env,
                &input.pipeline,
                input.closure.as_deref(),
            ),
        }
    }
}

/// Thread-confined actual ScalarCall and immutable non-admitting build data.
/// There is no code pointer, detach, mutable artifact, or raw-input constructor.
pub struct ObservedScalarCall {
    callable: ScalarCall,
    observations: NativePrimitiveUseObservations,
}
impl ObservedScalarCall {
    pub fn call(&mut self, a: u32, b: u32, c: u64, d: u64) -> u64 {
        self.callable.call(a, b, c, d)
    }
    pub fn declaration(&self) -> &Name {
        self.callable.declaration()
    }
    pub fn observations(&self) -> &NativePrimitiveUseObservations {
        &self.observations
    }
}
#[derive(Debug, thiserror::Error)]
#[error("{error}")]
pub struct ObservedScalarCallFailure {
    error: anyhow::Error,
    compiler_failure: Option<Box<OwnedObservedPipelineFailure<anyhow::Error>>>,
    observations: NativePrimitiveUseObservations,
}
impl ObservedScalarCallFailure {
    pub fn error(&self) -> &anyhow::Error {
        &self.error
    }
    pub fn compiler_failure(&self) -> Option<&OwnedObservedPipelineFailure<anyhow::Error>> {
        self.compiler_failure.as_deref()
    }
    pub fn observations(&self) -> &NativePrimitiveUseObservations {
        &self.observations
    }
}
impl ScalarCall {
    /// Execute the maintained source/selection/scalar/object/runtime route with
    /// explicit bounded observations. Recording truncation does not change the
    /// existing prototype, layout, provenance, licensing or runtime guards.
    pub fn from_source_observed(
        file: &Path,
        declaration: &str,
        opt_level: u8,
        limits: NativeObservationLimits,
    ) -> Result<ObservedScalarCall, ObservedScalarCallFailure> {
        let observer = NativeRecorder::new(limits);
        let result = (|| {
            host()?;
            let args = CompileArgs {
                file: Some(file.to_path_buf()),
                decl: Some(declaration.to_owned()),
                emit: EmitFormat::Obj,
                opt_level,
                output: None,
                link_artifact: vec![],
            };
            let (decls, env, pipeline) =
                crate::compile::select_lcnf_decl_recording(&args, &observer)?;
            let root = crate::compile::parse_compile_decl_name(declaration)?;
            let input = NativeOwnedInputs {
                decls,
                env,
                pipeline,
                closure: None,
            };
            Self::from_selected_input(
                ScalarSelectedInput::Observed {
                    input: &input,
                    observer: &observer,
                },
                &root,
                Some(file),
                None,
            )
        })();
        let compiler_failure = observer.take_emission_error();
        if result.is_err() {
            observer.gap(ObservationGap::Failed {
                owner: "scalar source/native route",
                error: "actual original refusal retained",
            });
        }
        let observations = observer.finish();
        match result {
            Ok(callable) => Ok(ObservedScalarCall {
                callable,
                observations,
            }),
            Err(error) => Err(ObservedScalarCallFailure {
                error,
                compiler_failure,
                observations,
            }),
        }
    }
}
