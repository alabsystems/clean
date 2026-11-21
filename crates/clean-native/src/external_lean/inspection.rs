// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Logical-only custody has no native selection interface or promotion method.

use clean_compiler::runtime_lcnf::RuntimeEnvironmentCapture;
use clean_kernel::{LeanWorld, Name};

use super::{
    ExternalLeanError, ExternalLeanInput, ExternalLeanProgram, InputObservation,
    ReplayedLeanContext, ReplayedLeanDeclaration,
};

pub(super) enum Usage {
    Inspection,
    Executable,
}

/// Owned source/import custody for logical inspection only. Executing Lean
/// source still runs its frontend/plugins; this is not a source sandbox.
/// Compiler capture diagnostics are retained verbatim, not kernel verdicts.
/// This type cannot select, emit or load code and has no promotion operation.
///
/// ```compile_fail
/// use clean_native::external_lean::ExternalLeanInspection;
/// use clean_kernel::Name;
/// fn cannot_select(view: &ExternalLeanInspection) {
///     let _ = view.select(&Name::from_string("query"), 0);
/// }
/// ```
pub struct ExternalLeanInspection {
    pub(super) program: ExternalLeanProgram,
}

impl ExternalLeanInspection {
    /// Use the same selected frontend, captured import artifacts, explicit
    /// world and source/input bookends as executable elaboration. Full compiler
    /// row capture is attempted and disclosed, but confers no native authority.
    pub fn elaborate(input: ExternalLeanInput<'_>) -> Result<Self, ExternalLeanError> {
        let program = ExternalLeanProgram::capture(input)?;
        // Logical inspection discloses the full global diagnostics, even on failure.
        program.source_capture();
        Ok(Self { program })
    }

    pub fn world(&self) -> LeanWorld {
        self.program.world()
    }
    /// Actual capture, including every typed row failure, error and limitation.
    pub fn source_capture(&self) -> &RuntimeEnvironmentCapture {
        self.program.source_capture()
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
    /// Read-only logical layout facts; grants no native selection capability.
    #[cfg(feature = "trust-ir-backend")]
    pub fn inspect_scalar_layout(
        &self,
        source_root: &Name,
        limits: super::ReplayContextLimits,
    ) -> Result<super::CheckedScalarLayoutFacts<'_>, super::ScalarLayoutFailure> {
        self.program.inspect_scalar_layout(source_root, limits)
    }
}

impl ExternalLeanProgram {
    /// Elaborate exactly the captured source, requiring complete compiler
    /// runtime capture as before. Dependency artifacts and owned copies are
    /// compared before/after running the explicitly selected Lean frontend.
    pub fn elaborate(input: ExternalLeanInput<'_>) -> Result<Self, ExternalLeanError> {
        let mut program = Self::capture(input)?;
        program.require_complete_runtime_capture()?;
        program.usage = Usage::Executable;
        Ok(program)
    }

    // Both public selection routes enter this guard. A logical-only capture
    // cannot acquire native authority even if all its runtime rows succeeded.
    pub(super) fn require_native(&self) -> Result<(), ExternalLeanError> {
        if !matches!(self.usage, Usage::Executable) {
            return Err(ExternalLeanError::Compile(
                "logical inspection custody cannot select native code".into(),
            ));
        }
        // Revalidate actual capture independently of the private usage marker.
        self.require_complete_runtime_capture()
    }

    pub(super) fn require_complete_runtime_capture(&self) -> Result<(), ExternalLeanError> {
        let observation = self.source_capture();
        if !observation.errors.is_empty()
            || !observation.row_failures.is_empty()
            || !observation.delta_complete
            || observation.snapshot_blake3.is_none()
        {
            return Err(ExternalLeanError::Input(format!(
                "incomplete source snapshot: {:?}",
                observation.errors
            )));
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
