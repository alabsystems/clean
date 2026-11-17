// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! EXPERIMENTAL `clean run --backend trust-cg`: the one-backend path, measured
//! (LX0(a) of `designs/2026-09-30-clean-trust-unified-vision.md`).
//!
//! Compiled only under the non-default `trust-ir-backend` feature. It changes
//! no default: `clean run` without `--backend trust-cg` and the default compile
//! format behave exactly as before. Explicit `clean compile --emit obj` uses
//! the same checked object license and external backend invocation.
//!
//! # The path
//!
//! 1. **Core.** The same elaboration, entry selection and fidelity audits as
//!    the C lane and `clean compile --emit obj` ([`select_lcnf_decl`]: the
//!    placeholder-opaque refusal, the eager-IO rewrite and its check, the
//!    string-carrier audit, the recursion-split audit), then LCNF → L5IR, the
//!    L5IR checker (the C lane's `check_ir`), and the `--emit obj` lowering
//!    ([`object_emit_config`]: `ExternCalls`, `validate_module`, the
//!    lowering-target subset, the kernel TV pass).
//! 2. **Module self-checks** ([`checks`]): the C lane's post-emission audits,
//!    read off the module instead of off emitted C — no source-lowered
//!    `String` body, every bodyless `l_*` declaration defined by a prelude shim
//!    at the arity the module calls it, and Lean's entry contract.
//! 3. **License.** Only a module every check accepted reaches this step, and
//!    only through [`checks::ModuleSelfChecks`], which nothing else
//!    constructs. Each `Ungated` body is re-stamped
//!    `Gated { clean-compiler-unvalidated }`
//!    (`clean_compiler::emit_trust_ir_lane`); a `clean-kernel-tv` body keeps its
//!    claim; a claim-less body is refused. Nothing is ever set to `None`.
//! 4. **trust-cg** compiles the module with
//!    `--recognize-authority clean-compiler-unvalidated --refuse-unlicensed`:
//!    the authority is recognized for this invocation only, and a body with no
//!    claim could not ride trust-cg's permissive default even if one existed.
//! 5. **Link** (runtime R0 of the design, §2.4): the object, the C runtime,
//!    `runtime_extern.c`, the whole prelude shim union compiled as one object,
//!    and the entry driver the C lane synthesizes
//!    ([`crate::native_build::render_entry_driver`]), with the host `cc`.
//! 6. **Run** with inherited stdio, exactly as the C lane runs.
//!
//! Every receipt says `lowered: clean-compiler-unvalidated` and
//! `runtime: C via cc`, and claims nothing about the binary.

#[path = "native_trustcg_checks.rs"]
pub(crate) mod checks;
#[path = "native_trustcg_link.rs"]
pub(crate) mod link;

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use clean_compiler::cli::{CompileArgs, EmitFormat};
use clean_compiler::emit_trust_ir::{module_stable_digest_string, serialize_tmbc};
use clean_compiler::emit_trust_ir_lane::{Module, CLEAN_COMPILER_UNVALIDATED_AUTHORITY};
use clean_compiler::ir_checker::check_decls;
use clean_compiler::pass_manager::{compile_lcnf_decls, compile_lcnf_to_trust_ir_with_report};
use serde::Serialize;
use thiserror::Error;

use crate::compile::{
    host_trust_cg_target, object_emit_config, parse_compile_decl_name, select_lcnf_decl,
};

#[path = "native_trustcg_retention.rs"]
mod retention;
use retention::BuildScratch;
pub use retention::ScratchRetention;
#[path = "native_trustcg_cli.rs"]
mod cli;
use cli::compile_object_with_cli;
pub(crate) use cli::stderr_head;

/// What this lane's bodies are licensed as, in every receipt.
pub const LOWERED: &str = CLEAN_COMPILER_UNVALIDATED_AUTHORITY;
/// The runtime this lane links, in every receipt (R0 of the design).
pub const RUNTIME: &str = "C via cc";
/// The receipt's schema tag.
pub(crate) const RECEIPT_SCHEMA: &str = "clean-run-trustcg-receipt/v1";
/// The receipt's claim, verbatim.
pub(crate) const CLAIM: &str =
    "measurement only; no binary claim; lane = clean-compiler-unvalidated";

/// Where the lane stopped.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum Stage {
    /// The Clean core refused before or while emitting trust-ir, or one of the
    /// module self-checks refused the emitted module.
    Core,
    /// trust-cg was absent, or refused the module.
    TrustCg,
    /// The C compile or the link of the object failed.
    Link,
    /// The program was built (it then runs).
    Built,
}

/// A named refusal of the lane, carrying the first blocking cause verbatim.
#[derive(Debug, Error)]
pub enum LaneError {
    /// The core refused at `step`.
    #[error("the Clean core refused at `{step}`: {cause}")]
    Core {
        /// Which core step refused (`front-end`, `l5ir-check`, ...).
        step: &'static str,
        /// The refusal, verbatim.
        cause: String,
    },
    /// trust-cg was absent or refused.
    #[error("trust-cg refused: {0}")]
    TrustCg(String),
    /// The C compile or link failed.
    #[error("the link failed: {0}")]
    Link(String),
}

impl LaneError {
    pub(crate) fn core(step: &'static str) -> impl Fn(anyhow::Error) -> Self {
        move |err| Self::Core {
            step,
            cause: format!("{err:#}"),
        }
    }

    fn stage(&self) -> Stage {
        match self {
            Self::Core { .. } => Stage::Core,
            Self::TrustCg(_) => Stage::TrustCg,
            Self::Link(_) => Stage::Link,
        }
    }

    fn step(&self) -> &str {
        match self {
            Self::Core { step, .. } => step,
            Self::TrustCg(_) => "trust-cg",
            Self::Link(_) => "link",
        }
    }

    fn cause(&self) -> &str {
        match self {
            Self::Core { cause, .. } | Self::TrustCg(cause) | Self::Link(cause) => cause,
        }
    }
}

/// The build receipt: written as JSON with `--receipt`, else one stderr line.
#[derive(Debug, Clone, Serialize)]
pub struct Receipt {
    schema: &'static str,
    lowered: &'static str,
    runtime: &'static str,
    claim: &'static str,
    decl: String,
    trust_cg: Option<String>,
    stage: Stage,
    step: Option<String>,
    cause: Option<String>,
    /// Stable digest of the module AS THE CORE EMITTED IT, before this lane
    /// re-stamped any body (the cross-door key of the design's §3.4).
    module_digest: Option<String>,
    kernel_tv_certified: usize,
    bodies_unvalidated: usize,
    bodies_kept: BTreeMap<String, usize>,
    entry_symbol: Option<String>,
    driver_entry: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    retained_directory: Option<PathBuf>,
    #[serde(skip_serializing_if = "Option::is_none")]
    retained_input_sha256: Option<String>,
}

impl Receipt {
    fn new(decl: &str) -> Self {
        Self {
            schema: RECEIPT_SCHEMA,
            lowered: LOWERED,
            runtime: RUNTIME,
            claim: CLAIM,
            decl: decl.to_owned(),
            trust_cg: None,
            stage: Stage::Core,
            step: None,
            cause: None,
            module_digest: None,
            kernel_tv_certified: 0,
            bodies_unvalidated: 0,
            bodies_kept: BTreeMap::new(),
            entry_symbol: None,
            driver_entry: None,
            retained_directory: None,
            retained_input_sha256: None,
        }
    }

    /// The one-line form printed on stderr when no `--receipt` file is named.
    pub fn line(&self) -> String {
        let kept: Vec<String> = self
            .bodies_kept
            .iter()
            .map(|(authority, n)| format!("{n} {authority}"))
            .collect();
        format!(
            "clean run --backend trust-cg: lowered: {}; runtime: {}; trust-cg: {}; bodies: {} {}{}; \
             module digest: {}; {}",
            self.lowered,
            self.runtime,
            self.trust_cg.as_deref().unwrap_or("<none>"),
            self.bodies_unvalidated,
            self.lowered,
            if kept.is_empty() {
                String::new()
            } else {
                format!(", kept {}", kept.join(", "))
            },
            self.module_digest.as_deref().unwrap_or("<none>"),
            self.claim,
        )
    }
}

/// What compiles a licensed trust-ir module to an object file: the lane's one
/// pluggable step.
///
/// Everything else (the core, the module self-checks, the license, the link
/// and the receipt) is this crate's, shared by every front door. Clean's own
/// door uses the external trust-cg CLI ([`build_with_receipt`]); Trust's door
/// supplies the trust-cg library it already links (`Compiler::compile`, one
/// backend consumer).
///
/// THE CONTRACT. The module handed in carries bodies licensed
/// `Gated { clean-compiler-unvalidated }` (or a kept `clean-kernel-tv` claim)
/// and nothing claim-less. An implementation must recognize exactly
/// [`LOWERED`] beyond its own defaults for this compilation and must refuse any
/// body without a licensing claim, as the CLI backend does with
/// `--recognize-authority clean-compiler-unvalidated --refuse-unlicensed`. One
/// that admitted an `Ungated` or claim-less body would compile code this lane
/// never licensed.
pub trait ObjectBackend {
    /// Who compiled the object, for the receipt (e.g. a path and a version).
    fn identity(&self) -> String;

    /// Compile `module` for `target` (`aarch64`, `x86_64`) into an object file
    /// under `dir`, returning its path. A refusal is
    /// [`LaneError::TrustCg`] with the backend's own message.
    fn compile_object(
        &self,
        module: &Module,
        target: &str,
        dir: &Path,
    ) -> Result<PathBuf, LaneError>;
}

/// The trust-cg this lane invokes: where it is and what it says it is.
#[derive(Debug, Clone)]
pub(crate) struct TrustCg {
    path: PathBuf,
    version: String,
    retention: ScratchRetention,
}

impl ObjectBackend for TrustCg {
    fn identity(&self) -> String {
        format!("{} ({})", self.path.display(), self.version)
    }

    fn compile_object(
        &self,
        module: &Module,
        target: &str,
        dir: &Path,
    ) -> Result<PathBuf, LaneError> {
        compile_object_with_cli(self, target, module, dir)
    }
}

/// Select the explicit compiler or the first file on PATH.
/// An invalid explicit selection is refused; only unselected absence returns None.
pub(super) fn select_trust_cg_path(
    selected: Option<std::ffi::OsString>,
    search_path: Option<std::ffi::OsString>,
) -> Result<Option<PathBuf>, LaneError> {
    match selected {
        Some(selected) => {
            let path = PathBuf::from(&selected);
            if !path.is_file() {
                return Err(LaneError::TrustCg(format!(
                    "CLEAN_TRUST_CG_BIN={} does not name a file; a selected trust-cg is never \
                     replaced by the one on PATH",
                    path.display()
                )));
            }
            Ok(Some(path))
        }
        None => Ok(search_path.and_then(|paths| {
            std::env::split_paths(&paths)
                .map(|dir| dir.join("trust-cg"))
                .find(|candidate| candidate.is_file())
        })),
    }
}

fn resolve_trust_cg() -> Result<TrustCg, LaneError> {
    let path = select_trust_cg_path(
        std::env::var_os("CLEAN_TRUST_CG_BIN"),
        std::env::var_os("PATH"),
    )?
    .ok_or_else(|| {
        LaneError::TrustCg(
            "trust-cg not found: `--backend trust-cg` needs the external trust-cg \
                     compiler; set CLEAN_TRUST_CG_BIN or put `trust-cg` on PATH"
                .to_owned(),
        )
    })?;
    TrustCg::from_path(path)
}

impl TrustCg {
    pub(crate) fn compile_object_recording(
        &self,
        module: &Module,
        target: &str,
        dir: &Path,
        observer: &crate::primitive_uses::NativeRecorder,
    ) -> Result<(PathBuf, Option<crate::primitive_uses::NativeArtifactId>), LaneError> {
        cli::compile_object_with_cli_recording(self, target, module, dir, Some(observer))
    }

    pub(crate) fn from_path(path: PathBuf) -> Result<Self, LaneError> {
        let path = std::fs::canonicalize(&path).unwrap_or(path);
        let out = Command::new(&path).arg("--version").output().map_err(|e| {
            LaneError::TrustCg(format!("could not run `{} --version`: {e}", path.display()))
        })?;
        if !out.status.success() {
            return Err(LaneError::TrustCg(format!(
                "`{} --version` failed: {}",
                path.display(),
                String::from_utf8_lossy(&out.stderr).trim()
            )));
        }
        let version = String::from_utf8_lossy(&out.stdout)
            .lines()
            .next()
            .unwrap_or("")
            .trim()
            .to_owned();
        Ok(TrustCg {
            path,
            version,
            retention: ScratchRetention::Remove,
        })
    }
}

/// A program built through this lane, in a scratch directory it owns.
pub struct BuiltTrustCg {
    pub(crate) binary: PathBuf,
    scratch: BuildScratch,
}

impl BuiltTrustCg {
    /// The linked executable.
    #[must_use]
    pub fn binary(&self) -> &Path {
        &self.binary
    }

    /// Keep the scratch build directory instead of deleting it, and return
    /// its path.
    #[must_use]
    pub fn keep(self) -> PathBuf {
        self.scratch.keep()
    }
}

/// Build `decl` of `file` through the trust-cg lane, returning the receipt
/// (filled step by step, and with the failing stage, step and cause on
/// refusal) beside the result. This is the lane's one entry point: the
/// `clean run --backend trust-cg` adapter in clean-cli renders the receipt,
/// runs the binary and exits; Trust's front door can call it the same way.
pub fn build_with_receipt(
    file: &Path,
    decl: &str,
    opt_level: u8,
) -> (Receipt, Result<BuiltTrustCg, LaneError>) {
    build_with_receipt_retaining(file, decl, opt_level, ScratchRetention::Remove)
}

/// Build with explicit diagnostic retention, including codegen/link failures.
pub fn build_with_receipt_retaining(
    file: &Path,
    decl: &str,
    opt_level: u8,
    retention: ScratchRetention,
) -> (Receipt, Result<BuiltTrustCg, LaneError>) {
    match resolve_trust_cg() {
        Ok(mut tcg) => {
            tcg.retention = retention;
            build_with_backend_retaining(file, decl, opt_level, &tcg, retention)
        }
        Err(err) => {
            let mut receipt = Receipt::new(decl);
            let result = Err(err);
            record_outcome(&mut receipt, &result);
            (receipt, result)
        }
    }
}

/// [`build_with_receipt`] with the object step supplied by the caller: the
/// entry point for a front door that compiles the module itself (Trust's,
/// in-process). Everything but `backend` is the same lane.
pub fn build_with_backend(
    file: &Path,
    decl: &str,
    opt_level: u8,
    backend: &dyn ObjectBackend,
) -> (Receipt, Result<BuiltTrustCg, LaneError>) {
    build_with_backend_retaining(file, decl, opt_level, backend, ScratchRetention::Remove)
}

/// The shared native build with caller-selected diagnostic retention.
pub fn build_with_backend_retaining(
    file: &Path,
    decl: &str,
    opt_level: u8,
    backend: &dyn ObjectBackend,
    retention: ScratchRetention,
) -> (Receipt, Result<BuiltTrustCg, LaneError>) {
    let mut receipt = Receipt::new(decl);
    let result = build(file, decl, opt_level, backend, &mut receipt, retention);
    record_outcome(&mut receipt, &result);
    retention::record_receipt(&receipt);
    (receipt, result)
}

/// Stamp the receipt with the build's outcome: built, or the failing stage,
/// step and cause.
fn record_outcome(receipt: &mut Receipt, result: &Result<BuiltTrustCg, LaneError>) {
    match result {
        Ok(_) => receipt.stage = Stage::Built,
        Err(err) => {
            receipt.stage = err.stage();
            receipt.step = Some(err.step().to_owned());
            receipt.cause = Some(err.cause().to_owned());
        }
    }
}

/// Build `decl` of `file` through the trust-cg lane, filling `receipt` as
/// each step passes.
fn build(
    file: &Path,
    decl: &str,
    opt_level: u8,
    backend: &dyn ObjectBackend,
    receipt: &mut Receipt,
    retention: ScratchRetention,
) -> Result<BuiltTrustCg, LaneError> {
    receipt.trust_cg = Some(backend.identity());
    let target = host_trust_cg_target().map_err(|e| LaneError::TrustCg(format!("{e:#}")))?;

    // 1. The core: elaboration, entry selection and every fidelity audit, then
    //    the L5IR checker and the `--emit obj` lowering.
    let compile_args = CompileArgs {
        file: Some(file.to_path_buf()),
        decl: Some(decl.to_owned()),
        emit: EmitFormat::Obj,
        opt_level,
        output: None,
        link_artifact: Vec::new(),
    };
    let (decls, env, pipeline) =
        select_lcnf_decl(&compile_args).map_err(LaneError::core("front-end"))?;
    let root = parse_compile_decl_name(decl).map_err(LaneError::core("front-end"))?;
    let decl_type = env.get_const(&root).map(|info| info.type_.clone());
    let artifacts = compile_lcnf_decls(&decls, &env, &pipeline)
        .map_err(|e| LaneError::core("l5ir")(e.into()))?;
    check_decls(&artifacts.boxed_ir_decls).map_err(|e| LaneError::core("l5ir-check")(e.into()))?;
    let (mut module, tv) = compile_lcnf_to_trust_ir_with_report(
        &decls,
        &env,
        &pipeline,
        &object_emit_config(&compile_args),
    )
    .map_err(|e| LaneError::core("emit-trust-ir")(e.into()))?;
    receipt.module_digest = Some(
        module_stable_digest_string(&module).map_err(|e| LaneError::core("digest")(e.into()))?,
    );
    receipt.kernel_tv_certified = tv.certified.len();

    // 2. The module self-checks, which mint the only witness step 3 accepts.
    let checked =
        checks::module_self_checks_for_env(&env, &module, decl, &root, decl_type.as_ref())?;
    receipt.entry_symbol = Some(checked.entry_symbol().to_owned());

    // 3. The license.
    let census = checked.license(&mut module)?;
    receipt.bodies_unvalidated = census.unvalidated;
    receipt.bodies_kept = census.kept;

    // 4. trust-cg, through the caller's backend.
    let scratch = BuildScratch::new(retention)?;
    if retention == ScratchRetention::Keep {
        receipt.retained_directory = Some(scratch.path().to_path_buf());
        receipt.retained_input_sha256 = Some(retention::record_input(&module, scratch.path())?);
    }
    let object = backend.compile_object(&module, target, scratch.path())?;

    // 5. The link.
    let linked = link::link_program(scratch.path(), &object, &checked)?;
    receipt.driver_entry = Some(linked.driver_entry);
    Ok(BuiltTrustCg {
        binary: linked.binary,
        scratch,
    })
}

#[cfg(test)]
#[path = "native_trustcg_string_source_tests.rs"]
mod string_source_tests;
#[cfg(test)]
#[path = "native_trustcg_tests.rs"]
mod tests;
