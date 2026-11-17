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
//! L5IR pipeline:  to_ir -> explicit_boxing -> rc_repair_boxed -> verify_rc_linearity -> emit_{c,rust}
//! ```

use super::{PassError, PassManager, Phase};
use crate::boxing::BoxingConfig;
use crate::emit_c::{emit_c_with_config, CEmitConfig};
use crate::emit_rust::{emit_rust_with_config, RustEmitConfig};
use crate::error::CompilerError;
use crate::ffi_verify::verify_extern_signature;
use crate::implemented_by::CodeMeaning;
use crate::ir::IRDecl;
use crate::ir_checker::IRError;
use crate::lcnf::{Decl, DeclValue};
use crate::opt::OptConfig;
use crate::rc::RCConfig;
use crate::rc_repair::{rc_repair_boxed, verify_rc_linearity, RcRepairMode};
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
    /// Lowered IR after explicit boxing and the post-boxing RC repair
    /// (`rc_repair::rc_repair_boxed`); every object variable of it passed the
    /// `rc_repair::verify_rc_linearity` gate (WS6.2).
    pub boxed_ir_decls: Vec<IRDecl>,
    /// Non-fatal IR-lowering diagnostics.
    pub warnings: Vec<String>,
    #[cfg(feature = "trust-ir-backend")]
    /// The batch's Rust callees (Trust plan step 3.2, C2); empty outside
    /// the Rust-ABI pipeline's inputs.
    pub(crate) rust_externs: Vec<crate::rust_abi::RustExternSig>,
    #[cfg(feature = "trust-ir-backend")]
    /// Whether `Nat` is carried by the pinned `trust_bignum::Nat` handle
    /// (Trust plan step 3.2, C3) — set only by the Rust-ABI pipeline.
    pub(crate) nat_handles: bool,
}

/// DATA returned by one complete maintained TrustIR pipeline invocation.
///
/// This is the exact artifact record from the full invocation. Its boxed IR
/// directly emits `module`; mono/optimized fields retain the maintained
/// pipeline's prefix-replay observations. The accessor repeats no full run.
/// Existing IR, ownership, emission and TV refusals apply.
/// These public data fields are not a source, runtime, ABI or artifact token.
#[cfg(feature = "trust-ir-backend")]
#[derive(Debug, Clone)]
pub struct TrustIrPipelineData {
    /// Every actual maintained stage, including all boxed/lifted declarations.
    pub artifacts: PipelineArtifacts,
    /// Final emitted module, including the existing TV pass's mutations.
    pub module: trust_ir::Module,
    /// The actual full-entry TV outcome; no record is synthesized by the accessor.
    pub tv_report: crate::emit_trust_ir_tv::TvMintReport,
    /// Actual emitter-synthesized native wrappers from this invocation only.
    /// DATA, never an extern owner, semantic certificate or codegen token.
    pub native_arithmetic_supplies: Vec<crate::emit_trust_ir::NativeArithmeticSupplyData>,
    /// Actual function-value and boxed-call associations from that same emitter.
    pub native_arithmetic_uses: Vec<crate::emit_trust_ir::NativeArithmeticUseData>,
}

#[cfg(all(test, feature = "trust-ir-backend"))]
mod transport_tests;

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
        self.emit_trust_ir_with_supply_data(config)
            .map(|data| data.module)
    }

    /// The same ordinary emission and entry guards, retaining actual native
    /// wrapper inputs/identities as untrusted producer DATA. No proof token.
    #[cfg(feature = "trust-ir-backend")]
    pub fn emit_trust_ir_with_supply_data(
        &self,
        config: &crate::emit_trust_ir::TrustIrConfig,
    ) -> Result<crate::emit_trust_ir::TrustIrEmissionData, crate::emit_trust_ir::TrustIrError> {
        self.emit_trust_ir_with_supply_data_recording(config, None)
    }

    #[cfg(feature = "trust-ir-backend")]
    fn emit_trust_ir_with_supply_data_recording(
        &self,
        config: &crate::emit_trust_ir::TrustIrConfig,
        observation: Option<&crate::primitive_uses::ObservationFrame>,
    ) -> Result<crate::emit_trust_ir::TrustIrEmissionData, crate::emit_trust_ir::TrustIrError> {
        let data = match observation {
            Some(_) => crate::emit_trust_ir::emit_trust_ir_recording_data(
                &self.boxed_ir_decls,
                config,
                observation,
            )?,
            None => {
                crate::emit_trust_ir::emit_trust_ir_with_supply_data(&self.boxed_ir_decls, config)?
            }
        };
        if config.runtime_lowering == crate::emit_trust_ir::RuntimeLowering::ExternCalls {
            crate::boxing::entry_check::check_generated_uint32_entries(
                &data.module,
                &self.ir_decls,
            )?;
        }
        Ok(data)
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
///
/// After boxing, the RC operations LCNF RC could not insert (variables whose
/// source type is scalar but whose final representation is an object, and
/// boxing's own temporaries) are added by `rc_repair::rc_repair_boxed`, and
/// every object variable of every declaration must then pass
/// `rc_repair::verify_rc_linearity` — a non-linear body is a compile error
/// ([`CompilerError::RcLinearity`]), never an emitted double release or leak
/// (WS6.2).
///
/// Every legacy `compile_lcnf_*` entry runs through here, and it first
/// refuses an environment whose `@[implemented_by]` ORDER record is not
/// empty ([`CompilerError::ImplementedByOrder`],
/// `crate::implemented_by::refuse_order`), as the lowering entries do and as
/// the Rust ABI's batch (`compile_lcnf_decls_at_rust_abi`) does:
/// declarations lowered before an `attribute [implemented_by]` command and
/// compiled after it are refused too. A declaration with a body whose name
/// is `@[extern]` is refused ([`CompilerError::ExternWithBody`]): compiled
/// Lean calls the symbol and never that body.
pub fn compile_lcnf_decls(
    decls: &[Decl],
    env: &Environment,
    config: &PipelineConfig,
) -> Result<PipelineArtifacts, PipelineError> {
    compile_lcnf_decls_for(decls, env, config, CodeMeaning::LeanCompiled)
}

/// [`compile_lcnf_decls`] for declarations lowered under `meaning`
/// (`crate::to_lcnf::constant_to_decl_with_meaning`). `meaning` must be the
/// one `decls` were lowered under. Under [`CodeMeaning::KernelValue`] the
/// order refusal does not apply: it is about which body Lean's compiled code
/// runs, and kernel-value declarations substitute no reference. No pass of
/// the pipeline substitutes one either: instance and carrier-primitive
/// resolution decline on an attributed constant
/// (`crate::implemented_by::has_compiler_attr`).
pub fn compile_lcnf_decls_for(
    decls: &[Decl],
    env: &Environment,
    config: &PipelineConfig,
    meaning: CodeMeaning,
) -> Result<PipelineArtifacts, PipelineError> {
    compile_lcnf_decls_inner(decls, env, config, RcRepairMode::Enabled, meaning, None)
}

/// [`compile_lcnf_decls`] with the post-boxing RC repair explicitly selected.
///
/// `RcRepairMode::Disabled` (test builds only) exists for the mutation
/// control: the linearity verifier still runs, so disabling the repair can
/// only turn a build into a refusal, never into a looser artifact.
#[cfg(test)]
pub(crate) fn compile_lcnf_decls_with_rc_repair(
    decls: &[Decl],
    env: &Environment,
    config: &PipelineConfig,
    rc_repair: RcRepairMode,
) -> Result<PipelineArtifacts, PipelineError> {
    compile_lcnf_decls_inner(
        decls,
        env,
        config,
        rc_repair,
        CodeMeaning::LeanCompiled,
        None,
    )
}

/// Run the maintained batch pipeline under an explicit checked runtime
/// binding closure; every submitted declaration/reference is checked too.
pub fn compile_lcnf_decls_in_runtime_closure(
    decls: &[Decl],
    env: &Environment,
    config: &PipelineConfig,
    closure: &crate::RuntimeBindingClosure,
) -> Result<PipelineArtifacts, PipelineError> {
    compile_lcnf_decls_inner(
        decls,
        env,
        config,
        RcRepairMode::Enabled,
        CodeMeaning::LeanCompiled,
        Some(closure),
    )
}

fn compile_lcnf_decls_inner(
    decls: &[Decl],
    env: &Environment,
    config: &PipelineConfig,
    rc_repair: RcRepairMode,
    meaning: CodeMeaning,
    closure: Option<&crate::RuntimeBindingClosure>,
) -> Result<PipelineArtifacts, PipelineError> {
    compile_lcnf_decls_recording(decls, env, config, rc_repair, meaning, closure, None)
}

pub(crate) fn compile_lcnf_decls_recording(
    decls: &[Decl],
    env: &Environment,
    config: &PipelineConfig,
    rc_repair: RcRepairMode,
    meaning: CodeMeaning,
    closure: Option<&crate::RuntimeBindingClosure>,
    observation: Option<&crate::primitive_uses::ObservationFrame>,
) -> Result<PipelineArtifacts, PipelineError> {
    match closure {
        Some(closure) => closure.declarations(env, decls)?,
        None => crate::implemented_by::refuse_order_for(env, meaning)?,
    }
    refuse_extern_bodies(decls, env, meaning)?;
    verify_extern_decls(decls)?;

    // Build the PassManager with all L5CNF passes registered
    let manager = |role| {
        PassManager::default_pipeline_recording(
            &config.opt,
            &config.rc,
            observation.map(|frame| frame.role(role)),
        )
    };
    let manager_base = manager(crate::primitive_uses::InvocationRole::PrefixReplay(
        Phase::Base,
    ));
    let manager_mono = manager(crate::primitive_uses::InvocationRole::PrefixReplay(
        Phase::Mono,
    ));
    let manager_full = manager(crate::primitive_uses::InvocationRole::Consumed);

    // Run Base phase (lambda_lift + to_mono) — captures mono snapshot
    let mono_decls = manager_base.run_batch_until_phase(decls, env, Phase::Base)?;
    if let Some(closure) = closure {
        closure.transformed_declarations(env, &mono_decls)?;
    }

    // Run through Mono phase (optimize) — captures optimized snapshot
    let optimized_decls = manager_mono.run_batch_until_phase(decls, env, Phase::Mono)?;
    if let Some(closure) = closure {
        closure.transformed_declarations(env, &optimized_decls)?;
    }

    // Run through Impure phase (RC) — captures RC snapshot
    let rc_decls = manager_full.run_batch(decls, env)?;
    if let Some(closure) = closure {
        closure.transformed_declarations(env, &rc_decls)?;
    }

    // L5IR stages (different representation — not expressible as PassManager passes)
    let ToIROutput {
        decls: ir_decls,
        warnings,
        rc_unmanaged,
        ..
    } = to_ir_with_env(&rc_decls, env)?;
    if let Some(closure) = closure {
        closure.ir_declarations(env, &ir_decls)?;
    }
    let observed_ir =
        observation.and_then(|frame| frame.ir_declarations("to_ir actual output", &ir_decls));
    if let Some(frame) = observation {
        let before = frame.declarations("to_ir actual input", &rc_decls);
        frame.decision(
            "to_ir",
            before,
            observed_ir.clone(),
            "actual full invocation lowering",
        );
    }
    let boxed_ir_decls =
        crate::boxing::explicit_boxing_with_kernel_env(&ir_decls, env, &config.boxing);
    let boxed_ir_decls = match rc_repair {
        RcRepairMode::Enabled => rc_repair_boxed(&ir_decls, boxed_ir_decls, &rc_unmanaged),
        #[cfg(test)]
        RcRepairMode::Disabled => boxed_ir_decls,
    };

    if let Some(closure) = closure {
        closure.ir_declarations(env, &boxed_ir_decls)?;
    }
    if let Some(frame) = observation {
        let after = frame.ir_declarations("boxing and RC repair actual output", &boxed_ir_decls);
        frame.decision(
            "boxing and RC repair",
            observed_ir,
            after,
            "actual boxing and repaired output; inner uninstrumented dispatch stays unobserved",
        );
        frame.gap(crate::primitive_uses::ObservationGap::Unobserved {
            owner: "boxing inner decisions",
            reason: "stage artifacts retained; inner choices not yet instrumented",
        });
    }
    verify_recursor_calls_certifiable(&boxed_ir_decls, env)?;
    verify_rc_linearity(&boxed_ir_decls)?;

    Ok(PipelineArtifacts {
        mono_decls,
        optimized_decls,
        rc_decls,
        ir_decls,
        boxed_ir_decls,
        warnings,
        #[cfg(feature = "trust-ir-backend")]
        rust_externs: Vec::new(),
        #[cfg(feature = "trust-ir-backend")]
        nat_handles: false,
    })
}

#[cfg(feature = "trust-ir-backend")]
/// The Rust-ABI pipeline (Trust plan step 3.2): [`compile_lcnf_decls`] with
/// the carrier boundary switched on.
///
/// * Instance resolution and carrier-primitive resolution run at every
///   optimization level ([`PassManager::rust_abi_pipeline`]).
/// * Boxing resolves call sites against the batch's Rust callees and the
///   native carrier primitives as well as its own declarations, so a scalar
///   argument of `inc` or `UInt64.add` is passed unboxed and the result is
///   scalar. Neither has a body here: a Rust callee is a call to Rust, a
///   primitive is one machine operation.
/// * No boxed closure-ABI wrappers and no boxed-constant helpers are made:
///   nothing at the carrier boundary takes a function's address, and every
///   constant is a machine literal.
/// * Reset/reuse is off: a carrier closure allocates no constructor.
pub(crate) fn compile_lcnf_decls_at_rust_abi(
    decls: &[Decl],
    env: &Environment,
    config: &PipelineConfig,
    nat_handles: bool,
) -> Result<PipelineArtifacts, PipelineError> {
    // `compile_rust_abi` refuses such an environment first, with its own
    // tag; this keeps every batch entry of the pipeline refusing it.
    crate::implemented_by::refuse_order(env)?;
    refuse_extern_bodies(decls, env, CodeMeaning::LeanCompiled)?;
    verify_extern_decls(decls)?;
    let rc_config = RCConfig::minimal();
    let manager = PassManager::rust_abi_pipeline(&config.opt, &rc_config, nat_handles);
    let mono_decls = manager.run_batch_until_phase(decls, env, Phase::Base)?;
    let optimized_decls = manager.run_batch_until_phase(decls, env, Phase::Mono)?;
    let rc_decls = manager.run_batch(decls, env)?;
    let ToIROutput {
        decls: ir_decls,
        warnings,
        rc_unmanaged,
        rust_externs,
    } = to_ir_with_env(&rc_decls, env)?;
    let signatures = carrier_signature_decls(&ir_decls, &rust_externs, nat_handles);
    let boxed_ir_decls = crate::boxing::explicit_boxing_with_signatures(
        &ir_decls,
        &signatures,
        &BoxingConfig::minimal(),
    );
    let boxed_ir_decls = rc_repair_boxed(&ir_decls, boxed_ir_decls, &rc_unmanaged);
    verify_recursor_calls_certifiable(&boxed_ir_decls, env)?;
    verify_rc_linearity(&boxed_ir_decls)?;
    Ok(PipelineArtifacts {
        mono_decls,
        optimized_decls,
        rc_decls,
        ir_decls,
        boxed_ir_decls,
        warnings,
        rust_externs,
        nat_handles,
    })
}

#[cfg(feature = "trust-ir-backend")]
/// Signature-only declarations (body `Unreachable`, never emitted) for the
/// Rust callees and for every native carrier primitive a body of `decls`
/// calls without defining it: what boxing resolves those call sites against.
fn carrier_signature_decls(
    decls: &[IRDecl],
    rust_externs: &[crate::rust_abi::RustExternSig],
    nat_handles: bool,
) -> Vec<IRDecl> {
    use crate::ir::{IRBody, VarId};
    let defined: std::collections::HashSet<&clean_kernel::Name> =
        decls.iter().map(|d| &d.name).collect();
    let signature = |name: clean_kernel::Name, params: Vec<crate::ir::IRType>, ret| IRDecl {
        name,
        params: params
            .into_iter()
            .enumerate()
            .map(|(i, t)| (VarId(i as u32), t))
            .collect(),
        return_type: ret,
        body: IRBody::Unreachable,
    };
    let mut out: Vec<IRDecl> = rust_externs
        .iter()
        .filter(|e| !defined.contains(&e.name))
        .map(|e| signature(e.name.clone(), e.params.clone(), e.ret.clone()))
        .collect();
    let mut seen: std::collections::BTreeSet<String> =
        out.iter().map(|d| d.name.to_string()).collect();
    for decl in decls {
        let mut callees = Vec::new();
        apply_callees(&decl.body, &mut callees);
        for callee in callees {
            if defined.contains(&callee) || !seen.insert(callee.to_string()) {
                continue;
            }
            if let Some(prim) = crate::carrier_prims::carrier_prim(&callee, nat_handles) {
                out.push(signature(callee, prim.params(), prim.ret()));
            }
        }
    }
    out
}

#[cfg(feature = "trust-ir-backend")]
/// Every saturated-call (`Apply`) callee of `body`, in body order.
fn apply_callees(body: &crate::ir::IRBody, out: &mut Vec<clean_kernel::Name>) {
    use crate::ir::{IRBody, IRExpr};
    match body {
        IRBody::VDecl { value, rest, .. } => {
            if let IRExpr::Apply { fn_id, .. } = value {
                out.push(fn_id.0.clone());
            }
            apply_callees(rest, out);
        }
        IRBody::JDecl { body, rest, .. } => {
            apply_callees(body, out);
            apply_callees(rest, out);
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => apply_callees(rest, out),
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                apply_callees(&alt.body, out);
            }
            if let Some(d) = default {
                apply_callees(d, out);
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
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

/// Each of `decls` with a body (not an extern declaration) whose name is
/// `@[extern]` in `env`, refused under `meaning`
/// (`crate::implemented_by::refuse_extern_body`).
fn refuse_extern_bodies(
    decls: &[Decl],
    env: &Environment,
    meaning: CodeMeaning,
) -> Result<(), CompilerError> {
    decls
        .iter()
        .filter(|decl| !matches!(decl.body, DeclValue::Extern(_)))
        .try_for_each(|decl| crate::implemented_by::refuse_extern_body(env, &decl.name, meaning))
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
    compile_lcnf_to_trust_ir_with_report(decls, env, pipeline_config, emit_config)
        .map(|(module, _)| module)
}

/// [`compile_lcnf_to_trust_ir`], additionally returning the per-decl TV mint
/// report (certified / skipped names) so a caller — `clean extract`'s TV
/// manifest leg — can say WHICH decls carry a kernel-decided certificate and
/// which were out-of-fragment skips. The fail-closed contract is identical:
/// a kernel REFUSAL (a detected miscompile) is an `Err`, never a report row.
/// With `certify_translation` off, the report is empty.
#[cfg(feature = "trust-ir-backend")]
pub fn compile_lcnf_to_trust_ir_with_report(
    decls: &[Decl],
    env: &Environment,
    pipeline_config: &PipelineConfig,
    emit_config: &crate::emit_trust_ir::TrustIrConfig,
) -> Result<(trust_ir::Module, crate::emit_trust_ir_tv::TvMintReport), PipelineError> {
    compile_lcnf_to_trust_ir_with_report_for(
        decls,
        env,
        pipeline_config,
        emit_config,
        CodeMeaning::LeanCompiled,
    )
}

/// [`compile_lcnf_to_trust_ir_with_report`] for declarations lowered under
/// `meaning` (as [`compile_lcnf_decls_for`]). The translation-validation
/// pass compares each declaration with its KERNEL definition, so it can
/// certify a [`CodeMeaning::KernelValue`] build's declarations, never a
/// substituted one.
#[cfg(feature = "trust-ir-backend")]
pub fn compile_lcnf_to_trust_ir_with_report_for(
    decls: &[Decl],
    env: &Environment,
    pipeline_config: &PipelineConfig,
    emit_config: &crate::emit_trust_ir::TrustIrConfig,
    meaning: CodeMeaning,
) -> Result<(trust_ir::Module, crate::emit_trust_ir_tv::TvMintReport), PipelineError> {
    compile_lcnf_to_trust_ir_ordered(decls, env, pipeline_config, emit_config, meaning, None)
}

/// The maintained TrustIR pipeline with an explicit checked runtime closure.
/// Existing TV, IR verification and backend licensing policies still apply.
#[cfg(feature = "trust-ir-backend")]
pub fn compile_lcnf_to_trust_ir_in_runtime_closure(
    decls: &[Decl],
    env: &Environment,
    pipeline_config: &PipelineConfig,
    emit_config: &crate::emit_trust_ir::TrustIrConfig,
    closure: &crate::RuntimeBindingClosure,
) -> Result<trust_ir::Module, PipelineError> {
    compile_lcnf_to_trust_ir_ordered(
        decls,
        env,
        pipeline_config,
        emit_config,
        CodeMeaning::LeanCompiled,
        Some(closure),
    )
    .map(|(module, _)| module)
}

/// Retain the actual stage DATA and TV report from the same full invocation.
/// Every ordinary full-entry guard and refusal remains in the common path.
#[cfg(feature = "trust-ir-backend")]
pub fn compile_lcnf_to_trust_ir_in_runtime_closure_with_artifacts(
    decls: &[Decl],
    env: &Environment,
    pipeline_config: &PipelineConfig,
    emit_config: &crate::emit_trust_ir::TrustIrConfig,
    closure: &crate::RuntimeBindingClosure,
) -> Result<TrustIrPipelineData, PipelineError> {
    compile_lcnf_to_trust_ir_ordered_data(
        decls,
        env,
        pipeline_config,
        emit_config,
        CodeMeaning::LeanCompiled,
        Some(closure),
    )
}

#[cfg(feature = "trust-ir-backend")]
fn compile_lcnf_to_trust_ir_ordered(
    decls: &[Decl],
    env: &Environment,
    pipeline_config: &PipelineConfig,
    emit_config: &crate::emit_trust_ir::TrustIrConfig,
    meaning: CodeMeaning,
    closure: Option<&crate::RuntimeBindingClosure>,
) -> Result<(trust_ir::Module, crate::emit_trust_ir_tv::TvMintReport), PipelineError> {
    let data = compile_lcnf_to_trust_ir_ordered_data(
        decls,
        env,
        pipeline_config,
        emit_config,
        meaning,
        closure,
    )?;
    Ok((data.module, data.tv_report))
}

#[cfg(feature = "trust-ir-backend")]
pub(crate) fn compile_lcnf_to_trust_ir_ordered_data(
    decls: &[Decl],
    env: &Environment,
    pipeline_config: &PipelineConfig,
    emit_config: &crate::emit_trust_ir::TrustIrConfig,
    meaning: CodeMeaning,
    closure: Option<&crate::RuntimeBindingClosure>,
) -> Result<TrustIrPipelineData, PipelineError> {
    compile_lcnf_to_trust_ir_recording(
        decls,
        env,
        pipeline_config,
        emit_config,
        meaning,
        closure,
        None,
    )
}

#[cfg(feature = "trust-ir-backend")]
pub(crate) fn compile_lcnf_to_trust_ir_recording(
    decls: &[Decl],
    env: &Environment,
    pipeline_config: &PipelineConfig,
    emit_config: &crate::emit_trust_ir::TrustIrConfig,
    meaning: CodeMeaning,
    closure: Option<&crate::RuntimeBindingClosure>,
    observation: Option<&crate::primitive_uses::ObservationFrame>,
) -> Result<TrustIrPipelineData, PipelineError> {
    let artifacts = compile_lcnf_decls_recording(
        decls,
        env,
        pipeline_config,
        RcRepairMode::Enabled,
        meaning,
        closure,
        observation,
    )?;
    // The L5IR checker, as the C and Rust lanes run it (`check_ir`): a shape
    // it refuses (e.g. a constructor the runtime header cannot hold) is
    // refused here at build time, never emitted for a runtime panic to catch.
    crate::ir_checker::check_decls(&artifacts.boxed_ir_decls)?;
    let emitted = artifacts.emit_trust_ir_with_supply_data_recording(emit_config, observation)?;
    let pre_tv = observation.and_then(|frame| {
        frame.module(
            "actual module before translation validation",
            &emitted.module,
        )
    });
    let (module, tv_report) = certify_trust_ir(emitted.module, decls, env, emit_config)?;
    if let Some(frame) = observation {
        let after = frame.module("actual module after translation validation", &module);
        frame.decision(
            "translation validation",
            pre_tv,
            after,
            "actual module mutation; ordinary licensing unchanged",
        );
    }
    Ok(TrustIrPipelineData {
        artifacts,
        module,
        tv_report,
        native_arithmetic_supplies: emitted.native_arithmetic_supplies,
        native_arithmetic_uses: emitted.native_arithmetic_uses,
    })
}

/// [`compile_lcnf_to_trust_ir_with_report`] with typed BOUNDARY carriers for
/// the named exports (two-language roadmap WS6.9, F-102; DG-70 option (a)).
///
/// Every export keeps its boxed body under its existing symbol and gains a
/// by-value wrapper under [`CarrierExport::symbol`](crate::emit_trust_ir::boundary::CarrierExport::symbol)
/// whose structure / inductive parameters are `Ty::Struct` / `Ty::Enum` with a
/// normative layout. The allocating half of the marshaller is a set of
/// kernel-checked helper definitions compiled by THIS pipeline (so the RC
/// linearity gate and the C back end see them); the wrapper only dispatches
/// and projects. An export with no total carrier is refused as
/// [`TrustIrError::NoTotalCarrier`](crate::emit_trust_ir::TrustIrError::NoTotalCarrier).
/// With no exports this is exactly [`compile_lcnf_to_trust_ir_with_report`].
#[cfg(feature = "trust-ir-backend")]
pub fn compile_lcnf_to_trust_ir_with_carrier_exports(
    decls: &[Decl],
    env: &Environment,
    pipeline_config: &PipelineConfig,
    emit_config: &crate::emit_trust_ir::TrustIrConfig,
    exports: &[clean_kernel::Name],
) -> Result<
    (
        trust_ir::Module,
        crate::emit_trust_ir_tv::TvMintReport,
        Vec<crate::emit_trust_ir::boundary::CarrierExport>,
    ),
    PipelineError,
> {
    if exports.is_empty() {
        let (module, report) =
            compile_lcnf_to_trust_ir_with_report(decls, env, pipeline_config, emit_config)?;
        return Ok((module, report, Vec::new()));
    }
    let plan = crate::emit_trust_ir::boundary::plan_carrier_exports(env, decls, exports)?;
    let artifacts = compile_lcnf_decls(&plan.decls, &plan.env, pipeline_config)?;
    crate::ir_checker::check_decls(&artifacts.boxed_ir_decls)?;
    let module = crate::emit_trust_ir::emit_trust_ir_with_carriers(
        &artifacts.boxed_ir_decls,
        emit_config,
        &plan.exports,
    )?;
    let (module, report) = certify_trust_ir(module, &plan.decls, &plan.env, emit_config)?;
    Ok((module, report, plan.exports))
}

/// The translation-validation pass shared by the trust-ir entry points.
#[cfg(feature = "trust-ir-backend")]
fn certify_trust_ir(
    mut module: trust_ir::Module,
    decls: &[Decl],
    env: &Environment,
    emit_config: &crate::emit_trust_ir::TrustIrConfig,
) -> Result<(trust_ir::Module, crate::emit_trust_ir_tv::TvMintReport), PipelineError> {
    let mut report = crate::emit_trust_ir_tv::TvMintReport::default();
    if emit_config.certify_translation {
        let mut identity_skips = Vec::new();
        // The comparand source of truth: each compiled decl's ORIGINAL kernel
        // definition Expr, straight from the environment (never re-derived
        // from any lowered form). Decls without a stored value (axioms,
        // externs, …) simply have nothing to certify against.
        // A BOUND mint (WS6.7(b)) also names each comparand's source: the
        // declaration and the closure digest of THIS environment, the one the
        // comparand is read from. The minter asks for it only once the kernel
        // has certified the decl (`source_of` below), so no closure is digested
        // for a decl that is skipped or refused first. A closure that cannot
        // be digested yields the reason instead: the decl was still JUDGED (a
        // miscompile is refused, never skipped) and is then skipped with that
        // reason, never bound partially.
        let mut source_decls: std::collections::BTreeMap<String, clean_kernel::Name> =
            std::collections::BTreeMap::new();
        let originals: Vec<(String, clean_kernel::Expr)> = decls
            .iter()
            .filter_map(|d| {
                let label = crate::emit_trust_ir::names::wire_name(&d.name);
                // An IMPORTED callee (WS6.8) is a body-less declaration here;
                // its translation was validated — or not — in the artifact
                // that defines it, and the import producer decides from THAT
                // certificate what the client may inherit. Nothing to mint.
                if emit_config.imported_callees.contains_key(&label) {
                    return None;
                }
                if !d
                    .level_params
                    .iter()
                    .all(crate::emit_trust_ir::names::is_legacy_name)
                    || !crate::emit_trust_ir::names::legacy_source_identity_supported(&d.ty)
                    || d.params.iter().any(|p| {
                        !crate::emit_trust_ir::names::legacy_source_identity_supported(&p.ty)
                    })
                {
                    identity_skips.push((
                        label,
                        "legacy TV declaration signature identity is unmeasured".to_owned(),
                    ));
                    return None;
                }
                let value = env.get_const(&d.name).and_then(|ci| ci.value.clone())?;
                source_decls.insert(label.clone(), d.name.clone());
                Some((label, value))
            })
            .collect();
        report = if emit_config.bind_certificates {
            let source_of = |label: &str| {
                let decl = source_decls.get(label)?;
                Some(
                    env.closure_digest(decl)
                        .map(|bytes| trust_ir::proof::SourceDefinitionRef {
                            decl: decl.to_string(),
                            closure_digest: trust_ir::proof::ProofDigest {
                                algorithm: trust_ir::proof::ProofDigestAlgorithm::Sha256,
                                bytes,
                            },
                        })
                        .map_err(|reason| reason.to_string()),
                )
            };
            crate::emit_trust_ir_tv::certify_backend_translation_bound_in_environment(
                &mut module,
                &originals,
                &source_of,
                env,
            )
        } else {
            crate::emit_trust_ir_tv::certify_backend_translation_in_environment(
                &mut module,
                &originals,
                env,
            )
        };
        report.skipped.extend(identity_skips);
        if !report.refused.is_empty() {
            return Err(
                crate::emit_trust_ir::TrustIrError::TranslationRefused(std::mem::take(
                    &mut report.refused,
                ))
                .into(),
            );
        }
    }
    Ok((module, report))
}
