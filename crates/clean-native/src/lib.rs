// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Clean's native core: from a Lean source file and a declaration to a linked
//! executable.
//!
//! One implementation, shared by every front door (LX0(b) of
//! `designs/2026-09-30-clean-trust-unified-vision.md`): `clean run`,
//! `clean compile`, `clean lake build`, `clean extract` and
//! `clean native-runtime` in clean-cli, and Trust's `targo trust build` at
//! LX1. It owns elaboration and declaration selection ([`compile`]), every
//! fidelity audit a native build must pass (the placeholder-opaque refusal,
//! the eager-IO rewrite and its check, the string-carrier and recursion-split
//! audits), the emitters, the C lane's shim selection, entry driver and link
//! ([`native_build`]), the linkable runtime archive an emitted object links
//! against ([`native_runtime`]), and, under the `trust-ir-backend` feature,
//! the experimental trust-ir -> trust-cg lane ([`native_trustcg`]). A front
//! door adds argument parsing, output and process exit; it never
//! re-implements a step here.

pub mod compile;
pub mod external_lean;
pub mod native_build;
mod native_c_toolchain;
mod native_eager_io;
mod native_eager_io_check;
mod native_ffi_audit;
mod native_kernel_bool;
mod native_monad_inline;
mod native_opaque_audit;
mod native_rec_split_audit;
// The linkable runtime archive `clean native-runtime` writes (WS6.13).
pub mod native_runtime;
mod native_string_carrier_audit;
mod native_string_layout_policy;
#[cfg(test)]
mod native_string_source_bridge_tests;
// EXPERIMENTAL trust-ir -> trust-cg lane (LX0); feature-gated, no default path
// reaches it.
#[cfg(feature = "trust-ir-backend")]
pub mod native_trustcg;
/// Experimental, source-bound scalar calls through the checked object lane.
#[cfg(feature = "trust-ir-backend")]
pub mod scalar_call;

/// [`compile::select_lcnf_decl`] for a build that promises the KERNEL value of
/// every constant it compiles (`clean extract`'s C, wasm and TV lanes): the
/// closure is lowered under [`clean_compiler::CodeMeaning::KernelValue`], so
/// no reference is substituted by an `@[implemented_by]` implementation and
/// each reached constant, an `@[implemented_by]` one included, compiles its
/// own logical value (`docs/DECISIONS.md` R149). Emit and compile the result
/// at the same meaning ([`compile::emit_decls`],
/// `clean_compiler::pass_manager::compile_lcnf_decls_for`).
///
/// # Errors
///
/// Every refusal of [`compile::select_lcnf_decl`] except the
/// `@[implemented_by]` ones: neither a reached or root `@[implemented_by]`
/// declaration nor the environment's order record
/// (`native-implemented-by-order`) is refused, since neither changes the
/// kernel value. A reached `@[extern]` declaration is still refused.
pub fn select_lcnf_decl_kernel_meaning(
    args: &clean_compiler::cli::CompileArgs,
) -> anyhow::Result<(
    Vec<clean_compiler::Decl>,
    clean_kernel::Environment,
    clean_compiler::pass_manager::PipelineConfig,
)> {
    compile::select_lcnf_decl_with_meaning(
        args,
        &native_build::is_primitive_denylisted,
        native_ffi_audit::CodeMeaning::KernelValue,
    )
}
