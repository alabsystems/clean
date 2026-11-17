// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Exact selected inputs moved once into the actual observed compiler frame.
use super::*;
use clean_compiler::pass_manager::PipelineConfig;
use clean_compiler::{Decl, RuntimeBindingClosure};

pub(crate) struct NativeOwnedInputs {
    pub(crate) decls: Arc<[Decl]>,
    pub(crate) env: Arc<Environment>,
    pub(crate) pipeline: Arc<PipelineConfig>,
    pub(crate) closure: Option<Arc<RuntimeBindingClosure>>,
}
