// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Owned external Lean elaboration into Clean's existing general compiler.
//!
//! The installed Lean executable and its frontend/plugins are an explicit TCB.
//! Kernel replay checks declarations, not whether unsafe elaborator metaprograms
//! implemented the author's intent. Native emission remains experimental and
//! unverified; this handoff grants no binary proof authority. Executing source
//! commands executes their elaborators: a Veil consumer must install its own
//! request-capture hook before using this API on engine-running commands.

use std::collections::{BTreeSet, HashSet};
use std::path::{Path, PathBuf};
#[cfg(test)]
use std::process::Command;
use std::sync::{Arc, OnceLock};

use clean_compiler::cli::EmitFormat;
use clean_compiler::pass_manager::PipelineConfig;
use clean_compiler::runtime_lcnf::{
    RuntimeEnvironmentCapture, RuntimeSourceCaptureLimits, RuntimeSourceRecord,
};
use clean_compiler::Decl;
use clean_kernel::{ConstantInfo, Environment, LeanWorld, Name};
#[cfg(test)]
use clean_olean::ImportWorld;
use clean_olean::{ImportedConeGate, ImportedConeVerdict};

mod elaborate;
mod inspection;
mod scoped;
pub use inspection::ExternalLeanInspection;
pub use scoped::{ExternalLeanScopedProgram, ExternalLeanScopedSelection};
mod snapshot;
pub use snapshot::InputObservation;
mod context;
pub use context::{
    ReplayContextError, ReplayContextLimits, ReplayedContextDeclaration, ReplayedLeanContext,
};
#[cfg(feature = "trust-ir-backend")]
mod scalar_layout;
#[cfg(feature = "trust-ir-backend")]
pub use scalar_layout::{
    CheckedScalarLayoutFacts, ScalarLayoutFailure, ScalarLayoutStage, ScalarLayoutWord,
    ScalarWordLayoutFacts,
};
mod primary_artifact;
pub use primary_artifact::{
    PrimaryArtifactDeclaration, PrimaryArtifactError, PrimaryArtifactLimits, PrimaryArtifactView,
    SourceCopyAssociation,
};

/// Inputs are observations, never authority over an arbitrary Environment.
#[derive(Debug)]
pub struct ExternalLeanInput<'a> {
    pub file: &'a Path,
    pub module: &'a Name,
    /// Explicit dependency roots, captured transitively before elaboration.
    /// Include `Init` for a source with Lean's implicit default import.
    pub imports: &'a [Name],
    pub search_paths: &'a [PathBuf],
    /// Always explicit, including the measured, nondefault Lean 4.35 world.
    pub world: LeanWorld,
}

#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum ExternalLeanError {
    #[error("external Lean input refused: {0}")]
    Input(String),
    #[error("external Lean elaboration failed: {0}")]
    Elaboration(String),
    #[error("external Lean declaration `{root}` failed replay: {reason}")]
    Replay {
        root: Name,
        reason: String,
        verdict: Box<ImportedConeVerdict>,
    },
    #[error("external Lean compiler handoff failed: {0}")]
    Compile(String),
    #[error(transparent)]
    Inspection(#[from] ReplayContextError),
    #[error(transparent)]
    Io(#[from] std::io::Error),
}

/// Source/declaration custody minted only by running the selected Lean over
/// owned source/import bytes. No constructor accepts Environment or hashes.
/// The declaration tables stay private and immutable to callers.
pub struct ExternalLeanProgram {
    env: Arc<Environment>,
    base: Arc<Environment>,
    module_names: BTreeSet<Name>,
    custody: Arc<Custody>,
    usage: inspection::Usage,
}

struct Custody {
    world: LeanWorld,
    source: Arc<Environment>,
    base: Arc<Environment>,
    /// Frontend-owned bytes are available before any compiler row observation.
    sources: Vec<RuntimeSourceRecord>,
    /// Program and selection retain the same frozen inputs for full diagnostics.
    global_observation: OnceLock<RuntimeEnvironmentCapture>,
    inputs: Vec<InputObservation>,
    primary_artifact: Result<primary_artifact::PrimaryArtifactCapture, PrimaryArtifactError>,
    _snapshot: tempfile::TempDir,
}

impl Custody {
    fn global_observation(&self) -> &RuntimeEnvironmentCapture {
        self.global_observation.get_or_init(|| {
            RuntimeEnvironmentCapture::capture(
                &self.base,
                &self.source,
                self.sources.clone(),
                RuntimeSourceCaptureLimits::default(),
            )
        })
    }
}

impl ExternalLeanProgram {
    pub fn world(&self) -> LeanWorld {
        self.custody.world
    }
    pub fn source_capture(&self) -> &RuntimeEnvironmentCapture {
        self.custody.global_observation()
    }
    pub fn inputs(&self) -> &[InputObservation] {
        &self.custody.inputs
    }

    /// Inspect the actual stored kernel declaration after source ownership
    /// and cone replay. Useful for typed frontend request records that need
    /// no native code. This is the logical value, independent of extern or
    /// implemented_by runtime substitutions; it grants no binary authority.
    pub fn inspect_owned_declaration(
        &self,
        root: &Name,
    ) -> Result<ReplayedLeanDeclaration<'_>, ExternalLeanError> {
        if !self.module_names.contains(root) {
            return Err(ExternalLeanError::Input(format!(
                "{root:?} was not declared by the captured source module"
            )));
        }
        let mut gate = ImportedConeGate::new(&self.base);
        let verdict = gate.check(&self.env, &BTreeSet::from([root.clone()]));
        if !verdict.passed(false) {
            return Err(ExternalLeanError::Replay {
                root: root.clone(),
                reason: verdict.refusal_summary(false),
                verdict: Box::new(verdict),
            });
        }
        let closure_digest = self
            .env
            .closure_digest(root)
            .map_err(|e| ExternalLeanError::Input(e.to_string()))?;
        let info = self.env.get_const(root).ok_or_else(|| {
            ExternalLeanError::Input(format!("no stored constant record for {root:?}"))
        })?;
        Ok(ReplayedLeanDeclaration {
            info,
            closure_digest,
            verdict,
            gate,
        })
    }

    /// Bind selection to this source module's exact declaration and transitive
    /// closure, replaying over a kernel-owned base with no waived trust markers.
    /// Imported library names cannot masquerade as declarations of this source.
    pub fn select(
        &self,
        root: &Name,
        opt_level: u8,
    ) -> Result<ExternalLeanSelection, ExternalLeanError> {
        self.select_ordered(root, opt_level, false)
    }

    /// Explicit checked runtime binding-order closure. The full context and
    /// all order records remain intact; legacy `select` still refuses globally.
    /// This is an input policy contract, never source/binary proof authority.
    pub fn select_in_runtime_closure(
        &self,
        root: &Name,
        opt_level: u8,
    ) -> Result<ExternalLeanSelection, ExternalLeanError> {
        self.select_ordered(root, opt_level, true)
    }

    fn select_ordered(
        &self,
        root: &Name,
        opt_level: u8,
        scoped: bool,
    ) -> Result<ExternalLeanSelection, ExternalLeanError> {
        self.require_native()?;
        self.select_captured(root, opt_level, scoped, None)
    }

    // Only the default native guard above or the separate source-owned scoped
    // guard may enter this shared compiler handoff. No public promotion exists.
    fn select_captured(
        &self,
        root: &Name,
        opt_level: u8,
        scoped: bool,
        allowed: Option<&BTreeSet<Name>>,
    ) -> Result<ExternalLeanSelection, ExternalLeanError> {
        let ReplayedLeanDeclaration {
            info: _,
            closure_digest,
            verdict,
            mut gate,
        } = self.inspect_owned_declaration(root)?;
        let runtime_binding_closure = scoped
            .then(|| {
                clean_compiler::RuntimeBindingClosure::check(&self.env, std::slice::from_ref(root))
            })
            .transpose()
            .map_err(|e| ExternalLeanError::Compile(e.to_string()))?;
        let select = |closure: Option<&clean_compiler::RuntimeBindingClosure>| match closure {
            Some(closure) => crate::compile::select_in_environment_in_runtime_closure(
                (*self.env).clone(),
                &HashSet::new(),
                root,
                opt_level,
                &crate::native_build::is_primitive_denylisted,
                &|_| crate::compile::DepRoute::Compile,
                closure,
            ),
            None => crate::compile::select_in_environment(
                (*self.env).clone(),
                &HashSet::new(),
                root,
                opt_level,
                &crate::native_build::is_primitive_denylisted,
                &|_| crate::compile::DepRoute::Compile,
                crate::native_ffi_audit::CodeMeaning::LeanCompiled,
            ),
        };
        let (decls, env, pipeline, _) = select(runtime_binding_closure.as_ref())
            .map_err(|e| ExternalLeanError::Compile(format!("{e:#}")))?;
        if let Some(allowed) = allowed {
            for declaration in &decls {
                let name = &declaration.name;
                let resident = self.env.get_const(name).is_some()
                    || self.env.get_inductive(name).is_some()
                    || self.env.get_constructor(name).is_some()
                    || self.env.get_recursor(name).is_some()
                    || self.env.get_quot(name).is_some();
                if resident && !allowed.contains(name) {
                    return Err(ExternalLeanError::Compile(format!(
                        "selected runtime declaration {name:?} is outside captured scope"
                    )));
                }
            }
        }
        // Runtime redirects can add bodies absent from the logical cone.
        // Replay those exact selected definitions too, under the same gate.
        let runtime_roots = decls.iter().map(|decl| decl.name.clone()).collect();
        let runtime_verdict = gate.check(&self.env, &runtime_roots);
        if !runtime_verdict.passed(false) {
            return Err(ExternalLeanError::Replay {
                root: root.clone(),
                reason: runtime_verdict.refusal_summary(false),
                verdict: Box::new(runtime_verdict),
            });
        }
        Ok(ExternalLeanSelection {
            root: root.clone(),
            closure_digest,
            verdict,
            runtime_verdict,
            runtime_binding_closure,
            decls,
            env,
            pipeline,
            custody: Arc::clone(&self.custody),
            #[cfg(feature = "trust-ir-backend")]
            source_context: SelectionSource {
                original: Arc::clone(&self.custody.source),
                base: Arc::clone(&self.custody.base),
                owner: Arc::clone(&self.custody),
            },
        })
    }
}

/// Borrowed, replayed view of an actual owned declaration. Construction is
/// private; caller-provided ConstantInfo, Environment or hashes grant nothing.
pub struct ReplayedLeanDeclaration<'a> {
    info: &'a ConstantInfo,
    closure_digest: [u8; 32],
    verdict: ImportedConeVerdict,
    gate: ImportedConeGate,
}

impl ReplayedLeanDeclaration<'_> {
    pub fn constant(&self) -> &ConstantInfo {
        self.info
    }
    pub fn closure_digest(&self) -> [u8; 32] {
        self.closure_digest
    }
    pub fn replay_verdict(&self) -> &ImportedConeVerdict {
        &self.verdict
    }
}

#[cfg(feature = "trust-ir-backend")]
struct SelectionSource {
    original: Arc<Environment>,
    base: Arc<Environment>,
    owner: Arc<Custody>,
}

/// A replayed declaration handed to the existing L5CNF/pipeline emitters.
/// This selection is an input qualification, never a binary certificate.
pub struct ExternalLeanSelection {
    root: Name,
    closure_digest: [u8; 32],
    verdict: ImportedConeVerdict,
    runtime_verdict: ImportedConeVerdict,
    runtime_binding_closure: Option<clean_compiler::RuntimeBindingClosure>,
    decls: Vec<Decl>,
    env: Environment,
    pipeline: PipelineConfig,
    custody: Arc<Custody>,
    #[cfg(feature = "trust-ir-backend")]
    source_context: SelectionSource,
}

impl ExternalLeanSelection {
    pub fn world(&self) -> LeanWorld {
        self.custody.world
    }
    pub fn source_capture(&self) -> &RuntimeEnvironmentCapture {
        self.custody.global_observation()
    }
    pub fn inputs(&self) -> &[InputObservation] {
        &self.custody.inputs
    }
    pub fn root(&self) -> &Name {
        &self.root
    }
    pub fn closure_digest(&self) -> [u8; 32] {
        self.closure_digest
    }
    pub fn replay_verdict(&self) -> &ImportedConeVerdict {
        &self.verdict
    }
    pub fn runtime_replay_verdict(&self) -> &ImportedConeVerdict {
        &self.runtime_verdict
    }
    pub fn declarations(&self) -> &[Decl] {
        &self.decls
    }
    /// Existing checked object path, retaining its explicit
    /// `clean-compiler-unvalidated` disclosure and no binary proof claim.
    #[cfg(feature = "trust-ir-backend")]
    pub fn emit_object(&self, output: &Path) -> Result<(), ExternalLeanError> {
        let source = self
            .custody
            .sources
            .first()
            .map(|record| Path::new(&record.path));
        crate::compile::emit_selected_object(
            &self.decls,
            &self.env,
            &self.pipeline,
            source,
            output,
            self.runtime_binding_closure.as_ref(),
        )
        .map_err(|e| ExternalLeanError::Compile(format!("{e:#}")))
    }

    /// Build a thread-confined experimental scalar callable from this exact
    /// replayed selection. This retains all source/runtime closure checks and
    /// adds canonical primitive and source/emitted C signature checks. A
    /// differing primitive representation refuses; no binary proof is granted.
    #[cfg(feature = "trust-ir-backend")]
    pub fn load_scalar_call(&self) -> Result<crate::scalar_call::ScalarCall, ExternalLeanError> {
        let source = self.custody.sources.first().map(|s| Path::new(&s.path));
        if !Arc::ptr_eq(&self.custody, &self.source_context.owner)
            || !Arc::ptr_eq(&self.custody.source, &self.source_context.original)
            || !Arc::ptr_eq(&self.custody.base, &self.source_context.base)
        {
            return Err(ExternalLeanError::Input(
                "scalar replay source belongs to another source custody".into(),
            ));
        }
        // Reuse the existing scalar layout dependency walk. These are proof
        // prerequisites, not additional native-selection rights. Their actual
        // combined source context must fit the unchanged capture limits before
        // fresh kernel replay or unbounded record-digest consumers.
        let mut roots = crate::scalar_call::scalar_source_roots()
            .map_err(|e| ExternalLeanError::Compile(format!("{e:#}")))?;
        roots.insert(self.root.clone());
        roots.extend(
            self.decls
                .iter()
                .filter(|d| self.source_context.original.get_const(&d.name).is_some())
                .map(|d| d.name.clone()),
        );
        let source_roots: Vec<_> = roots.iter().cloned().collect();
        let plan = clean_compiler::RuntimeBindingPlan::discover(
            &self.source_context.original,
            &source_roots,
            RuntimeSourceCaptureLimits::default().declarations,
        )
        .map_err(|e| ExternalLeanError::Compile(e.to_string()))?;
        let observation = clean_compiler::runtime_lcnf::RuntimeScopedEnvironmentCapture::capture(
            &self.source_context.base,
            &self.source_context.original,
            self.custody.sources.clone(),
            &plan,
        );
        if !observation.is_complete() {
            return Err(ExternalLeanError::Input(format!(
                "incomplete scalar replay source context: {:?}",
                observation.errors()
            )));
        }
        let replay = clean_olean::ReplayedImportedSource::check(
            Arc::clone(&self.source_context.base),
            Arc::clone(&self.source_context.original),
            roots.clone(),
        )
        .map_err(|e| ExternalLeanError::Compile(e.to_string()))?;
        replay
            .require_context(
                &self.source_context.base,
                &self.source_context.original,
                &roots,
            )
            .map_err(|e| ExternalLeanError::Compile(e.to_string()))?;
        crate::scalar_call::ScalarCall::from_selected_with_replay(
            &self.decls,
            &self.env,
            &self.pipeline,
            &self.root,
            source,
            self.runtime_binding_closure.as_ref(),
            Some(&replay),
        )
        .map_err(|e| ExternalLeanError::Compile(format!("{e:#}")))
    }

    /// Existing general compiler emission, at the same Lean-compiled meaning
    /// used in selection. Emission retains all existing backend proof limits.
    pub fn emit(&self, format: EmitFormat) -> Result<String, ExternalLeanError> {
        if let Some(closure) = &self.runtime_binding_closure {
            return crate::compile::emit_decls_in_runtime_closure(
                &self.decls,
                &self.env,
                format,
                &self.pipeline,
                None,
                closure,
            )
            .map_err(|e| ExternalLeanError::Compile(format!("{e:#}")));
        }
        crate::compile::emit_decls(
            &self.decls,
            &self.env,
            format,
            &self.pipeline,
            None,
            crate::native_ffi_audit::CodeMeaning::LeanCompiled,
        )
        .map_err(|e| ExternalLeanError::Compile(format!("{e:#}")))
    }
}

#[cfg(test)]
mod tests;
