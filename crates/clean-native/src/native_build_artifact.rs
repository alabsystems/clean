// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Keep the checked source layout attached to the exact emitted C.

use super::*;
use crate::native_string_layout_policy::StringLayoutPolicy;

/// Emitted C and its source-derived native carrier policy.
///
/// Its fields are private so an unrelated C string cannot reuse the policy.
#[derive(Debug)]
pub struct NativeCArtifact {
    decl: String,
    emitted_c: String,
    decl_type: Option<Expr>,
    policy: StringLayoutPolicy,
}

impl NativeCArtifact {
    /// Build the exact emitted artifact with its checked source policy.
    ///
    /// # Errors
    /// Refuses an unsupported entry, uncovered extern, or failed native link.
    pub fn build_in_scratch(&self, nat_strict_guard: bool) -> anyhow::Result<BuiltBinary> {
        build_native_binary_with_policy(
            &self.decl,
            &self.emitted_c,
            self.decl_type.as_ref(),
            nat_strict_guard,
            self.policy,
        )
    }

    pub(super) fn render(&self) -> anyhow::Result<String> {
        render_native_translation_unit_with_policy(
            &self.decl,
            &self.emitted_c,
            self.decl_type.as_ref(),
            self.policy,
        )
    }
}

/// Elaborate and emit a native C artifact without discarding its source policy.
///
/// # Errors
/// Preserves the production elaboration, fidelity-audit and emitter refusals.
pub fn emit_native_c_artifact(
    file: &Path,
    decl: &str,
    opt_level: u8,
) -> anyhow::Result<NativeCArtifact> {
    let args = CompileArgs {
        file: Some(file.to_path_buf()),
        decl: Some(decl.to_owned()),
        emit: EmitFormat::C,
        opt_level,
        output: None,
        link_artifact: Vec::new(),
    };
    let (decls, env, pipeline) = crate::compile::select_lcnf_decl(&args)?;
    let root = crate::compile::parse_compile_decl_name(decl)?;
    let decl_type = env.get_const(&root).map(|info| info.type_.clone());
    let emitted_c = crate::compile::emit_decls(
        &decls,
        &env,
        EmitFormat::C,
        &pipeline,
        Some(file),
        clean_compiler::CodeMeaning::LeanCompiled,
    )?;
    Ok(NativeCArtifact {
        decl: decl.to_owned(),
        emitted_c,
        decl_type,
        policy: StringLayoutPolicy::from_env(&env),
    })
}
