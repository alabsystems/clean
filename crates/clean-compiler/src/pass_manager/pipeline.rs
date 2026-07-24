// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Batch compiler pipeline orchestration helpers.
//!
//! These helpers compose the [`super::PassManager`] for L5CNF-level stages
//! (lambda_lift, to_mono, optimize, RC) with the L5IR-level stages
//! (to_ir, boxing, emission) that operate on a different representation.
//!
//! ```text
//! PassManager (L5CNF):  lambda_lift -> to_mono -> optimize -> rc
//!                                                              |
//! L5IR pipeline:                     to_ir -> explicit_boxing -> emit_{c,rust}
//! ```

use super::{PassError, PassManager, Phase};
use crate::boxing::{explicit_boxing_with_config, BoxingConfig};
use crate::emit_c::{emit_c_with_config, CEmitConfig};
use crate::emit_rust::{emit_rust_with_config, RustEmitConfig};
use crate::error::CompilerError;
use crate::ffi_verify::verify_extern_signature;
use crate::ir::IRDecl;
use crate::ir_checker::IRError;
use crate::lcnf::{Decl, DeclValue};
use crate::opt::OptConfig;
use crate::rc::RCConfig;
use crate::to_ir::{to_ir_with_env, ToIROutput};
use clean_kernel::Environment;
use thiserror::Error;

/// Configuration for the batch L5CNF compilation pipeline.
#[derive(Debug, Clone, Default)]
pub struct PipelineConfig {
    /// Batch optimization configuration.
    pub opt: OptConfig,
    /// Reference-counting pipeline configuration.
    pub rc: RCConfig,
    /// Explicit boxing configuration.
    pub boxing: BoxingConfig,
}

/// Stage outputs from batch L5CNF compilation.
#[derive(Debug, Clone)]
pub struct PipelineArtifacts {
    /// Declarations after monomorphization (end of Base phase).
    pub mono_decls: Vec<Decl>,
    /// Declarations after batch optimization (end of Mono phase).
    pub optimized_decls: Vec<Decl>,
    /// Declarations after RC transformation (end of Impure phase).
    pub rc_decls: Vec<Decl>,
    /// Lowered IR before boxing.
    pub ir_decls: Vec<IRDecl>,
    /// Lowered IR after explicit boxing.
    pub boxed_ir_decls: Vec<IRDecl>,
    /// Non-fatal IR-lowering diagnostics.
    pub warnings: Vec<String>,
}

impl PipelineArtifacts {
    /// Emit C from the boxed IR produced by this pipeline.
    pub fn emit_c(&self, config: CEmitConfig) -> Result<String, PipelineError> {
        Ok(emit_c_with_config(&self.boxed_ir_decls, config)?)
    }

    /// Emit Rust from the boxed IR produced by this pipeline.
    pub fn emit_rust(&self, config: RustEmitConfig) -> Result<String, PipelineError> {
        Ok(emit_rust_with_config(&self.boxed_ir_decls, config)?)
    }

    /// Lower the boxed IR produced by this pipeline into an experimental
    /// `trust_ir::Module`.
    ///
    /// This routes through the unverified, non-TCB trust-ir backend; see
    /// [`crate::emit_trust_ir`] for the trust caveats. Only available under the
    /// `trust-ir-backend` feature.
    #[cfg(feature = "trust-ir-backend")]
    pub fn emit_trust_ir(
        &self,
        config: &crate::emit_trust_ir::TrustIrConfig,
    ) -> Result<trust_ir::Module, crate::emit_trust_ir::TrustIrError> {
        crate::emit_trust_ir::emit_trust_ir_with_config(&self.boxed_ir_decls, config)
    }
}

/// Errors surfaced by the batch L5CNF pipeline.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum PipelineError {
    /// Lowering from L5CNF into typed IR failed.
    #[error(transparent)]
    Compiler(#[from] CompilerError),
    /// IR validation or backend emission failed.
    #[error(transparent)]
    Ir(#[from] IRError),
    /// A PassManager pass failed.
    #[error(transparent)]
    Pass(#[from] PassError),
    /// The experimental trust-ir backend rejected or failed to lower the IR.
    #[cfg(feature = "trust-ir-backend")]
    #[error(transparent)]
    TrustIr(#[from] crate::emit_trust_ir::TrustIrError),
}

/// Compile L5CNF declarations through the full pipeline.
///
/// Uses [`PassManager::default_pipeline_with_config`] for the Decl-level stages
/// (lambda_lift -> to_mono -> optimize -> rc), then continues with the L5IR-level
/// stages (to_ir -> explicit_boxing) which operate on a different representation.
///
/// Intermediate artifacts are captured at each phase boundary for diagnostics.
pub fn compile_lcnf_decls(
    decls: &[Decl],
    env: &Environment,
    config: &PipelineConfig,
) -> Result<PipelineArtifacts, PipelineError> {
    verify_extern_decls(decls)?;

    // Build the PassManager with all L5CNF passes registered
    let manager = PassManager::default_pipeline_with_config(&config.opt, &config.rc);

    // Run Base phase (lambda_lift + to_mono) — captures mono snapshot
    let mono_decls = manager.run_batch_until_phase(decls, env, Phase::Base)?;

    // Run through Mono phase (optimize) — captures optimized snapshot
    let optimized_decls = manager.run_batch_until_phase(decls, env, Phase::Mono)?;

    // Run through Impure phase (RC) — captures RC snapshot
    let rc_decls = manager.run_batch(decls, env)?;

    // L5IR stages (different representation — not expressible as PassManager passes)
    let ToIROutput {
        decls: ir_decls,
        warnings,
    } = to_ir_with_env(&rc_decls, env)?;
    let boxed_ir_decls = explicit_boxing_with_config(&ir_decls, &config.boxing);

    verify_recursor_calls_certifiable(&boxed_ir_decls, env)?;

    Ok(PipelineArtifacts {
        mono_decls,
        optimized_decls,
        rc_decls,
        ir_decls,
        boxed_ir_decls,
        warnings,
    })
}

/// Fail-closed guard (C5a, tightened for link-honesty): refuse any compiled
/// declaration whose FINAL (post-optimization, post-boxing) IR references a
/// VALUELESS kernel recursor (`Nat.rec`, `Int.rec`, `Char.rec`, `BEq.rec`,
/// `Acc.rec`, `Eq.rec`, …) at all.
///
/// A valueless recursor can never be compiled from source, and NOTHING
/// implements its mangled symbol: the runtime's implemented callable surface
/// is (a) declarations compiled from source in-slice, (b) the
/// `PRIMITIVE_DENYLIST` runtime shims (`clean-cli`'s
/// `native_build::ALL_PRELUDE_SHIM_TABLES` — Nat/Bool arithmetic, typeclass
/// plumbing, IO; it contains NO `<Ind>.rec` symbol), and (c) `casesOn` /
/// `recOn`-style DEFINITIONS with stored values, which are exempt below
/// precisely because they have a value. An earlier revision allowed
/// "all-`Ptr`-certifiable" recursor call sites to survive as boxed extern
/// fallbacks (`emit_trust_ir::declare_extern_fallbacks`); the emitted module
/// was syntactically valid but could NEVER LINK — `l_Nat_rec` /
/// `l_Int_rec` / `l_Char_rec` / `l_BEq_rec` imports counted as wins in the
/// compile census while being unrunnable. The guard now refuses every such
/// reference so the per-declaration relaxed-#14 probe demotes the REFERRING
/// declaration to an extern boundary (an honest boundary: that declaration
/// has a value and could be won by future compiler work; a valueless
/// recursor cannot).
///
/// Still deliberately scoped:
/// * checked on the FINAL IR — recursor applications that are erased or
///   dead-code-eliminated (e.g. `Prop`-motive eliminations like
///   `Acc.recOn`'s) never reach this guard;
/// * only VALUELESS recursor callees — `<Ind>.casesOn` / `<Ind>.recOn` are
///   ALSO registered in the kernel's recursor map but are definitions with
///   stored values (compilable from source, and legitimate extern boundaries
///   when dropped), so they are exempt.
fn verify_recursor_calls_certifiable(
    decls: &[IRDecl],
    env: &Environment,
) -> Result<(), CompilerError> {
    use crate::ir::{IRBody, IRExpr};

    for decl in decls {
        let mut stack: Vec<&IRBody> = vec![&decl.body];
        while let Some(body) = stack.pop() {
            match body {
                IRBody::VDecl { value, rest, .. } => {
                    let callee = match value {
                        IRExpr::Apply { fn_id, .. } | IRExpr::PartialApply { fn_id, .. } => {
                            Some(&fn_id.0)
                        }
                        _ => None,
                    };
                    if let Some(name) = callee {
                        let valueless = env.get_const(name).is_none_or(|info| info.value.is_none());
                        if valueless && env.get_recursor(name).is_some() {
                            return Err(CompilerError::Unsupported(format!(
                                "declaration `{}` references kernel recursor `{name}`, \
                                 which has no runtime value and no runtime shim (nothing \
                                 can ever provide its symbol); the declaration must stay \
                                 an extern boundary",
                                decl.name
                            )));
                        }
                    }
                    stack.push(rest);
                }
                IRBody::JDecl {
                    body: jp_body,
                    rest,
                    ..
                } => {
                    stack.push(jp_body);
                    stack.push(rest);
                }
                IRBody::Inc { rest, .. }
                | IRBody::Dec { rest, .. }
                | IRBody::Set { rest, .. }
                | IRBody::SetTag { rest, .. }
                | IRBody::USet { rest, .. }
                | IRBody::SSet { rest, .. } => stack.push(rest),
                IRBody::Case { alts, default, .. } => {
                    for alt in alts {
                        stack.push(&alt.body);
                    }
                    if let Some(default) = default {
                        stack.push(default);
                    }
                }
                IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
            }
        }
    }
    Ok(())
}

fn verify_extern_decls(decls: &[Decl]) -> Result<(), CompilerError> {
    for decl in decls {
        let DeclValue::Extern(extern_data) = &decl.body else {
            continue;
        };
        verify_extern_signature(&decl.name, &decl.params, &decl.ty, extern_data)?;
    }
    Ok(())
}

/// Compile existing L5CNF declarations and emit C.
pub fn compile_lcnf_to_c(
    decls: &[Decl],
    env: &Environment,
    pipeline_config: &PipelineConfig,
    emit_config: CEmitConfig,
) -> Result<String, PipelineError> {
    compile_lcnf_decls(decls, env, pipeline_config)?.emit_c(emit_config)
}

/// Compile existing L5CNF declarations and emit Rust.
pub fn compile_lcnf_to_rust(
    decls: &[Decl],
    env: &Environment,
    pipeline_config: &PipelineConfig,
    emit_config: RustEmitConfig,
) -> Result<String, PipelineError> {
    compile_lcnf_decls(decls, env, pipeline_config)?.emit_rust(emit_config)
}

/// Compile existing L5CNF declarations and lower to experimental trust-ir.
///
/// Runs the full L5CNF -> L5IR pipeline and then the unverified, non-TCB
/// trust-ir backend. The returned `trust_ir::Module` is only guaranteed to be
/// syntactically valid — EXCEPT for decls covered by the
/// [`TrustIrConfig::certify_translation`](crate::emit_trust_ir::TrustIrConfig::certify_translation)
/// pass (DEFAULT-ON since 2026-07-21): every in-fragment decl gets a
/// kernel-decided `TranslationValidation` obligation + `CleanCic` certificate
/// attached post-finalize ([`crate::emit_trust_ir_tv`]; the ORIGINAL kernel
/// definition `Expr` comes from this `env`, the source of truth), a kernel
/// REFUSAL (a detected miscompile) aborts the compile fail-closed, and
/// out-of-fragment decls are silently skipped (no obligation — never a fake
/// cert; the skip walk is the cheap common case). Available only under the
/// `trust-ir-backend` feature.
#[cfg(feature = "trust-ir-backend")]
pub fn compile_lcnf_to_trust_ir(
    decls: &[Decl],
    env: &Environment,
    pipeline_config: &PipelineConfig,
    emit_config: &crate::emit_trust_ir::TrustIrConfig,
) -> Result<trust_ir::Module, PipelineError> {
    let mut module = compile_lcnf_decls(decls, env, pipeline_config)?.emit_trust_ir(emit_config)?;
    if emit_config.certify_translation {
        // The comparand source of truth: each compiled decl's ORIGINAL kernel
        // definition Expr, straight from the environment (never re-derived
        // from any lowered form). Decls without a stored value (axioms,
        // externs, …) simply have nothing to certify against.
        let originals: Vec<(String, clean_kernel::Expr)> = decls
            .iter()
            .filter_map(|d| {
                env.get_const(&d.name)
                    .and_then(|ci| ci.value.clone())
                    .map(|v| (d.name.to_string(), v))
            })
            .collect();
        let report = crate::emit_trust_ir_tv::certify_backend_translation(&mut module, &originals);
        if !report.refused.is_empty() {
            return Err(
                crate::emit_trust_ir::TrustIrError::TranslationRefused(report.refused).into(),
            );
        }
    }
    Ok(module)
}
