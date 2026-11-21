// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Fresh source-owned runtime scope, separate from global capture readiness.

use super::{
    Custody, ExternalLeanError, ExternalLeanInput, ExternalLeanProgram, ExternalLeanSelection,
    InputObservation, ReplayedLeanContext, ReplayedLeanDeclaration,
};
use clean_compiler::runtime_lcnf::{
    RuntimeEnvironmentCapture, RuntimeScopedEnvironmentCapture, RuntimeSourceCaptureLimits,
};
use clean_compiler::{cli::EmitFormat, Decl, RuntimeBindingPlan};
use clean_kernel::{LeanWorld, Name};
use clean_olean::ImportedConeVerdict;
use std::sync::Arc;

struct Scope {
    owner: Arc<Custody>,
    observation: RuntimeScopedEnvironmentCapture,
}

/// Fresh owned elaboration for an explicitly selected runtime dependency
/// closure. The default global constructor and logical inspection type keep
/// their existing guards. Neither can be promoted into this capability.
/// Every root must be declared by the actual captured source module.
///
/// Global diagnostics remain actual global diagnostics; a successful scoped
/// observation never marks an incomplete global observation complete.
pub struct ExternalLeanScopedProgram {
    program: ExternalLeanProgram,
    scope: Arc<Scope>,
}

impl ExternalLeanScopedProgram {
    pub fn elaborate(
        input: ExternalLeanInput<'_>,
        roots: &[Name],
    ) -> Result<Self, ExternalLeanError> {
        if roots.is_empty() {
            return Err(ExternalLeanError::Input(
                "runtime scope requires a root".into(),
            ));
        }
        let program = ExternalLeanProgram::capture(input)?;
        for root in roots {
            if !program.module_names.contains(root) {
                return Err(ExternalLeanError::Input(format!(
                    "{root:?} was not declared by the captured source module"
                )));
            }
        }
        let plan = discover(&program, roots)?;
        let observation = observe(&program, &plan);
        require_complete(&observation)?;
        // Mint the existing contract only after every actual required row and
        // compiler attribute has met the unchanged source-capture limits.
        plan.finish(&program.env)
            .map_err(|e| ExternalLeanError::Compile(e.to_string()))?;
        let scope = Arc::new(Scope {
            owner: Arc::clone(&program.custody),
            observation,
        });
        Ok(Self { program, scope })
    }

    pub fn world(&self) -> LeanWorld {
        self.program.world()
    }
    /// Observe the full frozen environment on first request, retaining any failures.
    pub fn source_capture(&self) -> &RuntimeEnvironmentCapture {
        self.program.source_capture()
    }
    /// Separate exact scope; never a claim about a complete global delta.
    pub fn scoped_capture(&self) -> &RuntimeScopedEnvironmentCapture {
        &self.scope.observation
    }
    pub fn inputs(&self) -> &[InputObservation] {
        self.program.inputs()
    }
    pub fn primary_artifact(
        &self,
        limits: super::PrimaryArtifactLimits,
    ) -> Result<super::PrimaryArtifactView<'_>, super::PrimaryArtifactError> {
        self.program.primary_artifact(limits)
    }
    pub fn inspect_owned_declaration(
        &self,
        root: &Name,
    ) -> Result<ReplayedLeanDeclaration<'_>, ExternalLeanError> {
        self.program.inspect_owned_declaration(root)
    }
    pub fn replay_context(
        &self,
        roots: &[Name],
    ) -> Result<ReplayedLeanContext<'_>, ExternalLeanError> {
        self.program.replay_context(roots)
    }
    /// Read-only logical layout facts; neither capture nor native guards change.
    #[cfg(feature = "trust-ir-backend")]
    pub fn inspect_scalar_layout(
        &self,
        source_root: &Name,
        limits: super::ReplayContextLimits,
    ) -> Result<super::CheckedScalarLayoutFacts<'_>, super::ScalarLayoutFailure> {
        self.program.inspect_scalar_layout(source_root, limits)
    }

    /// Retain the default compiler's global binding-order refusal policy.
    pub fn select(
        &self,
        root: &Name,
        opt_level: u8,
    ) -> Result<ExternalLeanScopedSelection, ExternalLeanError> {
        self.select_ordered(root, opt_level, false)
    }
    /// Use the existing explicit checked runtime binding-order policy.
    pub fn select_in_runtime_closure(
        &self,
        root: &Name,
        opt_level: u8,
    ) -> Result<ExternalLeanScopedSelection, ExternalLeanError> {
        self.select_ordered(root, opt_level, true)
    }
    fn select_ordered(
        &self,
        root: &Name,
        opt_level: u8,
        ordered: bool,
    ) -> Result<ExternalLeanScopedSelection, ExternalLeanError> {
        self.require_scope(root)?;
        if !ordered {
            crate::native_ffi_audit::refuse_compiled_before_binding(root, &self.program.env)
                .map_err(|e| ExternalLeanError::Compile(e.to_string()))?;
        }
        // Both new scoped paths retain the checked contract through every
        // lowering/emission stage. The default path additionally keeps the
        // existing whole-environment binding-order refusal above.
        let selection = self.program.select_captured(
            root,
            opt_level,
            true,
            Some(self.scope.observation.members()),
        )?;
        Ok(ExternalLeanScopedSelection {
            selection,
            scope: Arc::clone(&self.scope),
        })
    }
    fn require_scope(&self, root: &Name) -> Result<(), ExternalLeanError> {
        if !Arc::ptr_eq(&self.program.custody, &self.scope.owner) {
            return Err(ExternalLeanError::Input(
                "runtime scope belongs to different source custody".into(),
            ));
        }
        require_complete(&self.scope.observation)?;
        if !self.scope.observation.roots().contains(root) {
            return Err(ExternalLeanError::Input(format!(
                "{root:?} is outside explicitly captured runtime roots"
            )));
        }
        let roots: Vec<_> = self.scope.observation.roots().iter().cloned().collect();
        let plan = discover(&self.program, &roots)?;
        let actual = observe(&self.program, &plan);
        require_complete(&actual)?;
        if actual.snapshot_blake3() != self.scope.observation.snapshot_blake3() {
            return Err(ExternalLeanError::Input(
                "captured runtime scope changed".into(),
            ));
        }
        Ok(())
    }
}

fn discover(
    program: &ExternalLeanProgram,
    roots: &[Name],
) -> Result<RuntimeBindingPlan, ExternalLeanError> {
    RuntimeBindingPlan::discover(
        &program.env,
        roots,
        RuntimeSourceCaptureLimits::default().declarations,
    )
    .map_err(|e| ExternalLeanError::Compile(e.to_string()))
}
fn observe(
    program: &ExternalLeanProgram,
    plan: &RuntimeBindingPlan,
) -> RuntimeScopedEnvironmentCapture {
    RuntimeScopedEnvironmentCapture::capture(
        &program.base,
        &program.env,
        program.custody.sources.clone(),
        plan,
    )
}
fn require_complete(capture: &RuntimeScopedEnvironmentCapture) -> Result<(), ExternalLeanError> {
    if !capture.is_complete() {
        return Err(ExternalLeanError::Input(format!(
            "incomplete scoped source snapshot: {:?}",
            capture.errors()
        )));
    }
    Ok(())
}

/// Selection bound to its actual source-owned scope. It exposes the existing
/// compiler and scalar ABI without exposing a default executable program or an
/// unscoped selection. Scalar calls retain their thread confinement.
pub struct ExternalLeanScopedSelection {
    selection: ExternalLeanSelection,
    scope: Arc<Scope>,
}
impl ExternalLeanScopedSelection {
    pub fn world(&self) -> LeanWorld {
        self.selection.world()
    }
    pub fn source_capture(&self) -> &RuntimeEnvironmentCapture {
        self.selection.source_capture()
    }
    pub fn scoped_capture(&self) -> &RuntimeScopedEnvironmentCapture {
        &self.scope.observation
    }
    pub fn inputs(&self) -> &[InputObservation] {
        self.selection.inputs()
    }
    pub fn root(&self) -> &Name {
        self.selection.root()
    }
    pub fn closure_digest(&self) -> [u8; 32] {
        self.selection.closure_digest()
    }
    pub fn replay_verdict(&self) -> &ImportedConeVerdict {
        self.selection.replay_verdict()
    }
    pub fn runtime_replay_verdict(&self) -> &ImportedConeVerdict {
        self.selection.runtime_replay_verdict()
    }
    pub fn declarations(&self) -> &[Decl] {
        self.selection.declarations()
    }
    pub fn emit(&self, format: EmitFormat) -> Result<String, ExternalLeanError> {
        self.selection.emit(format)
    }
    #[cfg(feature = "trust-ir-backend")]
    pub fn emit_object(&self, output: &std::path::Path) -> Result<(), ExternalLeanError> {
        self.selection.emit_object(output)
    }
    #[cfg(feature = "trust-ir-backend")]
    pub fn load_scalar_call(&self) -> Result<crate::scalar_call::ScalarCall, ExternalLeanError> {
        self.selection.load_scalar_call()
    }
}

#[cfg(test)]
mod tests;
