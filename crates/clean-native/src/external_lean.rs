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
use std::process::Command;
use std::sync::Arc;

use clean_compiler::cli::EmitFormat;
use clean_compiler::pass_manager::PipelineConfig;
use clean_compiler::runtime_lcnf::{
    RuntimeContext, RuntimeEnvironmentCapture, RuntimeSourceRecord,
};
use clean_compiler::Decl;
use clean_kernel::{ConstantInfo, Environment, LeanWorld, Name};
use clean_olean::{ImportWorld, ImportedConeGate, ImportedConeVerdict};

mod snapshot;
pub use snapshot::InputObservation;

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
    Io(#[from] std::io::Error),
}

/// Source/declaration custody minted only by running the selected Lean over
/// owned source/import bytes. No constructor accepts Environment or hashes.
/// The declaration tables stay private and immutable to callers.
pub struct ExternalLeanProgram {
    env: Environment,
    base: Environment,
    module_names: BTreeSet<Name>,
    custody: Arc<Custody>,
}

struct Custody {
    world: LeanWorld,
    observation: RuntimeEnvironmentCapture,
    inputs: Vec<InputObservation>,
    _snapshot: tempfile::TempDir,
}

impl ExternalLeanProgram {
    /// Elaborate exactly the captured source. Dependency artifacts (including
    /// runtime `.ir` companions) are copied before invoking Lean, and input
    /// files, executable and owned copies are compared again afterwards.
    /// Only the owned search path may supply the subsequently replayed context.
    pub fn elaborate(input: ExternalLeanInput<'_>) -> Result<Self, ExternalLeanError> {
        let decision = clean_olean::source_world_for_file(input.file, Some(input.world))
            .map_err(|e| ExternalLeanError::Input(e.to_string()))?;
        let Ok(ImportWorld::Explicit { lib, .. }) = decision.imports() else {
            return Err(ExternalLeanError::Input(
                "explicit Lean world required".into(),
            ));
        };
        let lean = lib
            .parent()
            .and_then(Path::parent)
            .ok_or_else(|| ExternalLeanError::Input("invalid installed Lean library path".into()))?
            .join("bin/lean");
        let snapshot = tempfile::tempdir()?;
        let root = snapshot.path();
        let mut files = snapshot::Files::default();
        files.observe(input.file)?;
        let source_path = snapshot::module_path(root, input.module, "lean")?;
        if let Some(parent) = source_path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        files.copy(input.file, &source_path)?;
        let source = std::fs::read_to_string(&source_path)?;
        files.observe(&lean)?;
        // Shared libraries are part of the frontend TCB, never proof evidence.
        snapshot::observe_frontend_libraries(lib, &mut files)?;
        files.observe(&source_path)?;
        let mut search_paths = input.search_paths.to_vec();
        search_paths.push(lib.clone());
        let mut base = Environment::for_lean_replay();
        clean_olean::declare_environment_world(&mut base, input.world.tag())
            .map_err(|e| ExternalLeanError::Input(e.to_string()))?;
        let mut world_scope = clean_olean::LeanWorldScope::of_environment(&base);
        snapshot::capture_imports(
            input.imports,
            &search_paths,
            root,
            &mut files,
            &mut world_scope,
        )?;
        let output_path = snapshot::module_path(root, input.module, "olean")?;
        if output_path.exists() {
            return Err(ExternalLeanError::Input(
                "source module redeclares a captured import".into(),
            ));
        }
        let output = Command::new(&lean)
            .current_dir(root)
            // Ambient Lean/sysroot/plugin/loader variables must not redirect
            // this explicitly selected frontend into another installation.
            .env_clear()
            .env("LEAN_PATH", root)
            .arg("--root")
            .arg(root)
            .arg("-o")
            .arg(&output_path)
            .arg(&source_path)
            .output()?;
        files.check()?;
        if !output.status.success() {
            return Err(ExternalLeanError::Elaboration(format!(
                "{}: {}{}",
                output.status,
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            )));
        }
        snapshot::observe_output(&output_path, &mut files, &mut world_scope)?;
        let mut env = base.clone();
        clean_olean::load_typed_module_with_deps_bounded(
            &mut env,
            input.module,
            &[root.to_path_buf()],
            4096,
        )
        .map_err(|e| ExternalLeanError::Input(e.to_string()))?;
        files.check()?;
        let artifact = clean_olean::read_artifact(
            &format!("{:?}", input.module),
            &output_path,
            clean_olean::ArtifactDepth::Records,
        )
        .map_err(|e| ExternalLeanError::Input(e.to_string()))?;
        let capture = RuntimeContext::capture_with_environment(
            vec![],
            &base,
            &env,
            vec![RuntimeSourceRecord {
                module: format!("{:?}", input.module),
                path: std::fs::canonicalize(input.file)?.display().to_string(),
                source,
            }],
        );
        let observation = capture
            .environment_capture()
            .cloned()
            .ok_or_else(|| ExternalLeanError::Input("missing source observation".into()))?;
        if !observation.errors.is_empty() || observation.snapshot_blake3.is_none() {
            return Err(ExternalLeanError::Input(format!(
                "incomplete source snapshot: {:?}",
                observation.errors
            )));
        }
        // Membership and source observations were read after loading. Close
        // that entire read interval, not only the loader's earlier reads.
        files.check()?;
        Ok(Self {
            env,
            base,
            module_names: artifact.names.into_iter().collect(),
            custody: Arc::new(Custody {
                world: input.world,
                observation,
                inputs: files.into_observations(),
                _snapshot: snapshot,
            }),
        })
    }

    pub fn world(&self) -> LeanWorld {
        self.custody.world
    }
    pub fn source_capture(&self) -> &RuntimeEnvironmentCapture {
        &self.custody.observation
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
                self.env.clone(),
                &HashSet::new(),
                root,
                opt_level,
                &crate::native_build::is_primitive_denylisted,
                &|_| crate::compile::DepRoute::Compile,
                closure,
            ),
            None => crate::compile::select_in_environment(
                self.env.clone(),
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
}

impl ExternalLeanSelection {
    pub fn world(&self) -> LeanWorld {
        self.custody.world
    }
    pub fn source_capture(&self) -> &RuntimeEnvironmentCapture {
        &self.custody.observation
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
            .observation
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
        let source = self
            .custody
            .observation
            .sources
            .first()
            .map(|s| Path::new(&s.path));
        crate::scalar_call::ScalarCall::from_selected(
            &self.decls,
            &self.env,
            &self.pipeline,
            &self.root,
            source,
            self.runtime_binding_closure.as_ref(),
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
