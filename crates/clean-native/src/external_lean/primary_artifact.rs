//! Read-only primary-artifact occurrences and actual captured source/copy links.
//! None of these data facts grants source, proof or native-selection rights.

use super::{ExternalLeanProgram, InputObservation, ReplayedLeanContext};
use clean_kernel::{name::NameInner, ConstantInfo, LeanWorld, Name};
use clean_olean::{
    ArtifactDeclaration, ArtifactDeclarationOrigin, ArtifactInventory, ArtifactInventoryError,
    ArtifactInventoryLimits,
};
use std::path::{Path, PathBuf};

/// No partial inventory/view accompanies one of these failures.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum PrimaryArtifactError {
    #[error("primary artifact observation requires positive finite limits")]
    InvalidLimits,
    #[error("primary artifact structural work limit")]
    StructuralLimit,
    #[error("primary artifact owned-input byte limit")]
    ByteLimit,
    #[error("primary artifact inventory unavailable: {0}")]
    Inventory(#[from] ArtifactInventoryError),
    #[error("primary artifact capture association is unavailable")]
    MissingAssociation,
    #[error("original/copy path association changed during capture")]
    ChangedAssociation,
    #[error("primary artifact owned input changed after capture")]
    ChangedOwnedInput,
    #[error("primary artifact belongs to another program/world/context")]
    ForeignContext,
    #[error("source byte range is reversed, outside capture or splits UTF-8")]
    InvalidRange,
    #[error("source producer path does not match the actual captured SDK path")]
    ProducerPathMismatch,
    #[error("primary artifact input inspection failed: {0}")]
    Io(#[source] std::sync::Arc<std::io::Error>),
}
impl From<std::io::Error> for PrimaryArtifactError {
    fn from(error: std::io::Error) -> Self {
        Self::Io(std::sync::Arc::new(error))
    }
}

/// Positive per-observation bounds; there is no unlimited mode.
#[derive(Debug, Clone, Copy)]
pub struct PrimaryArtifactLimits {
    declarations: usize,
    structural_units: usize,
    owned_input_bytes: usize,
}
impl PrimaryArtifactLimits {
    /// Bound declaration occurrences, expanded structure and newly hashed bytes.
    pub fn new(
        declarations: usize,
        structural_units: usize,
        owned_input_bytes: usize,
    ) -> Result<Self, PrimaryArtifactError> {
        if declarations == 0 || structural_units == 0 || owned_input_bytes == 0 {
            return Err(PrimaryArtifactError::InvalidLimits);
        }
        Ok(Self {
            declarations,
            structural_units,
            owned_input_bytes,
        })
    }
}
impl Default for PrimaryArtifactLimits {
    fn default() -> Self {
        Self {
            declarations: 100_000,
            structural_units: 100_000,
            owned_input_bytes: 64 * 1024 * 1024,
        }
    }
}

pub(super) struct Work(pub(super) usize);
impl Work {
    pub(super) fn spend(&mut self, n: usize) -> Result<(), PrimaryArtifactError> {
        self.0 = self
            .0
            .checked_sub(n)
            .ok_or(PrimaryArtifactError::StructuralLimit)?;
        Ok(())
    }
    pub(super) fn path(&mut self, path: &Path) -> Result<(), PrimaryArtifactError> {
        self.spend(path.as_os_str().as_encoded_bytes().len())?;
        for _ in path.components() {
            self.spend(1)?;
        }
        Ok(())
    }
    fn name(&mut self, mut name: &Name) -> Result<(), PrimaryArtifactError> {
        loop {
            self.spend(1)?;
            match name.inner() {
                NameInner::Anon => return Ok(()),
                NameInner::Str(parent, text) => {
                    self.spend(text.len())?;
                    name = parent;
                }
                NameInner::Num(parent, _) => {
                    self.spend(8)?;
                    name = parent;
                }
            }
        }
    }
}

struct OwnedPart {
    path: PathBuf,
    observation: Option<usize>,
}

/// Private capture facts, separate from compatibility ownership/module_names.
pub(super) struct PrimaryArtifactCapture {
    module: Name,
    inventory: ArtifactInventory,
    authoritative: clean_olean::module::OLeanLevel,
    original: usize,
    copy: usize,
    original_canonical: PathBuf,
    sdk_argument: PathBuf,
    sdk_canonical: PathBuf,
    parts: Vec<OwnedPart>,
}

pub(super) fn path_equal(
    a: &Path,
    b: &Path,
    work: &mut Work,
) -> Result<bool, PrimaryArtifactError> {
    let (a, b) = (
        a.as_os_str().as_encoded_bytes(),
        b.as_os_str().as_encoded_bytes(),
    );
    work.spend(1)?;
    if a.len() != b.len() {
        return Ok(false);
    }
    for (a, b) in a.iter().zip(b) {
        work.spend(1)?;
        if a != b {
            return Ok(false);
        }
    }
    Ok(true)
}
fn input_index(
    inputs: &[InputObservation],
    path: &Path,
    work: &mut Work,
) -> Result<usize, PrimaryArtifactError> {
    for (index, input) in inputs.iter().enumerate() {
        if path_equal(&input.path, path, work)? {
            return Ok(index);
        }
    }
    Err(PrimaryArtifactError::MissingAssociation)
}

impl PrimaryArtifactCapture {
    /// Bound this additional path observation before canonicalize can allocate
    /// an OS argument/result. Existing capture I/O keeps its original policy.
    pub(super) fn canonical_observation(path: &Path) -> Result<PathBuf, PrimaryArtifactError> {
        Work(64 * 1024 * 1024).path(path)?;
        Ok(std::fs::canonicalize(path)?)
    }
    pub(super) fn recorded_parts(
        output: &Path,
        files: &super::snapshot::Files,
    ) -> Result<Vec<(PathBuf, bool)>, PrimaryArtifactError> {
        let mut work = Work(64 * 1024 * 1024);
        let mut parts = Vec::new();
        for extension in super::snapshot::ARTIFACT_EXTENSIONS {
            work.path(output)?;
            work.spend(extension.len())?;
            let path = output.with_extension(extension);
            let present = files.recorded_presence(&path, &mut work)?;
            parts.push((path, present));
        }
        Ok(parts)
    }
    /// Called only inside actual SDK capture after the original Files bookend.
    pub(super) fn bind(
        module: &Name,
        artifact: clean_olean::ArtifactRead,
        original_path: &Path,
        original_before: Result<PathBuf, PrimaryArtifactError>,
        original_after: PathBuf,
        original_end: Result<PathBuf, PrimaryArtifactError>,
        sdk_argument: &Path,
        sdk_before: Result<PathBuf, PrimaryArtifactError>,
        sdk_after: Result<PathBuf, PrimaryArtifactError>,
        inputs: &[InputObservation],
        parts: Result<Vec<(PathBuf, bool)>, PrimaryArtifactError>,
    ) -> Result<Self, PrimaryArtifactError> {
        let inventory = artifact
            .inventory
            .ok_or(PrimaryArtifactError::MissingAssociation)??;
        let mut work = Work(64 * 1024 * 1024);
        work.name(module)?;
        work.path(original_path)?;
        work.path(&original_after)?;
        work.path(sdk_argument)?;
        let before = original_before?;
        work.path(&before)?;
        if !path_equal(&before, &original_after, &mut work)? {
            return Err(PrimaryArtifactError::ChangedAssociation);
        }
        let end = original_end?;
        work.path(&end)?;
        if !path_equal(&end, &original_after, &mut work)? {
            return Err(PrimaryArtifactError::ChangedAssociation);
        }
        let sdk_canonical = sdk_after?;
        work.path(&sdk_canonical)?;
        let sdk_before = sdk_before?;
        work.path(&sdk_before)?;
        if !path_equal(&sdk_before, &sdk_canonical, &mut work)? {
            return Err(PrimaryArtifactError::ChangedAssociation);
        }
        let original = input_index(inputs, original_path, &mut work)?;
        let copy = input_index(inputs, sdk_argument, &mut work)?;
        if inputs[original].bytes != inputs[copy].bytes
            || inputs[original].sha256 != inputs[copy].sha256
        {
            return Err(PrimaryArtifactError::ChangedAssociation);
        }
        let mut owned = Vec::new();
        for (path, present) in parts? {
            work.path(&path)?;
            let observation = if present {
                Some(input_index(inputs, &path, &mut work)?)
            } else {
                None
            };
            owned.push(OwnedPart { path, observation });
        }
        Ok(Self {
            module: module.clone(),
            inventory,
            authoritative: artifact.authoritative,
            original,
            copy,
            original_canonical: original_after,
            sdk_argument: sdk_argument.to_path_buf(),
            sdk_canonical,
            parts: owned,
        })
    }
}

/// Borrowed, complete artifact-membership facts after bounded owned-file checks.
/// This is neither an ownership/replay token nor a live filesystem lease.
pub struct PrimaryArtifactView<'program> {
    program: &'program ExternalLeanProgram,
    capture: &'program PrimaryArtifactCapture,
}

impl ExternalLeanProgram {
    /// Observe complete retained primary membership and the existing owned copy.
    /// Rechecks only that source/output subset; no replay/selection is granted.
    pub fn primary_artifact(
        &self,
        limits: PrimaryArtifactLimits,
    ) -> Result<PrimaryArtifactView<'_>, PrimaryArtifactError> {
        let capture = self
            .custody
            .primary_artifact
            .as_ref()
            .map_err(Clone::clone)?;
        let used = capture
            .inventory
            .check_limits(ArtifactInventoryLimits::new(
                limits.declarations,
                limits.structural_units,
            )?)?;
        let mut work = Work(
            limits
                .structural_units
                .checked_sub(used)
                .ok_or(PrimaryArtifactError::StructuralLimit)?,
        );
        work.name(&capture.module)?;
        for path in [
            &capture.original_canonical,
            &capture.sdk_argument,
            &capture.sdk_canonical,
        ] {
            work.path(path)?;
        }
        let original = self
            .custody
            .inputs
            .get(capture.original)
            .ok_or(PrimaryArtifactError::MissingAssociation)?;
        let copy = self
            .custody
            .inputs
            .get(capture.copy)
            .ok_or(PrimaryArtifactError::MissingAssociation)?;
        work.path(&original.path)?;
        work.path(&copy.path)?;
        for part in &capture.parts {
            work.path(&part.path)?;
            if let Some(index) = part.observation {
                let input = self
                    .custody
                    .inputs
                    .get(index)
                    .ok_or(PrimaryArtifactError::MissingAssociation)?;
                if !path_equal(&part.path, &input.path, &mut work)? {
                    return Err(PrimaryArtifactError::MissingAssociation);
                }
            }
        }
        if original.bytes != copy.bytes || original.sha256 != copy.sha256 {
            return Err(PrimaryArtifactError::ChangedAssociation);
        }
        let source = self
            .custody
            .sources
            .first()
            .ok_or(PrimaryArtifactError::MissingAssociation)?;
        if self.custody.sources.len() != 1 || source.source.len() as u64 != copy.bytes {
            return Err(PrimaryArtifactError::MissingAssociation);
        }
        let mut remaining = limits.owned_input_bytes;
        remaining = remaining
            .checked_sub(source.source.len())
            .ok_or(PrimaryArtifactError::ByteLimit)?;
        use sha2::{Digest, Sha256};
        let source_hash: [u8; 32] = Sha256::digest(source.source.as_bytes()).into();
        if source_hash != copy.sha256 {
            return Err(PrimaryArtifactError::ChangedAssociation);
        }
        let canonical = std::fs::canonicalize(&capture.sdk_argument)?;
        work.path(&canonical)?;
        if !path_equal(&canonical, &capture.sdk_canonical, &mut work)? {
            return Err(PrimaryArtifactError::ChangedOwnedInput);
        }
        super::snapshot::check_owned_input(&copy.path, Some(copy), &mut remaining)?;
        for part in &capture.parts {
            let expected = part
                .observation
                .map(|index| {
                    self.custody
                        .inputs
                        .get(index)
                        .ok_or(PrimaryArtifactError::MissingAssociation)
                })
                .transpose()?;
            super::snapshot::check_owned_input(&part.path, expected, &mut remaining)?;
        }
        Ok(PrimaryArtifactView {
            program: self,
            capture,
        })
    }
}

impl<'program> PrimaryArtifactView<'program> {
    /// Actual structural module identity passed to capture.
    pub fn module(&self) -> &Name {
        &self.capture.module
    }
    pub fn world(&self) -> LeanWorld {
        self.program.world()
    }
    pub fn authoritative_part(&self) -> clean_olean::module::OLeanLevel {
        self.capture.authoritative
    }
    pub fn declarations(
        &self,
    ) -> impl ExactSizeIterator<Item = PrimaryArtifactDeclaration<'_, 'program>> {
        self.capture
            .inventory
            .declarations()
            .iter()
            .map(|record| PrimaryArtifactDeclaration { view: self, record })
    }
    pub fn source(&self) -> SourceCopyAssociation<'_, 'program> {
        SourceCopyAssociation { view: self }
    }
    pub fn require_context(
        &self,
        context: &ReplayedLeanContext<'_>,
    ) -> Result<(), PrimaryArtifactError> {
        if !context.same_program(self.program) {
            return Err(PrimaryArtifactError::ForeignContext);
        }
        Ok(())
    }
}

/// An actual occurrence, not a checked declaration or source-selection right.
pub struct PrimaryArtifactDeclaration<'view, 'program> {
    view: &'view PrimaryArtifactView<'program>,
    record: &'view ArtifactDeclaration,
}
impl PrimaryArtifactDeclaration<'_, '_> {
    pub fn name(&self) -> &Name {
        self.record.name()
    }
    pub fn origin(&self) -> ArtifactDeclarationOrigin {
        self.record.origin()
    }
    /// Unreplayed candidate data. Missing rows remain missing, never Safe stubs.
    pub fn captured_constant(&self) -> Option<&ConstantInfo> {
        self.view.program.env.get_const(self.name())
    }
}

/// Actual original/copy/output association belonging to this captured program.
pub struct SourceCopyAssociation<'view, 'program> {
    view: &'view PrimaryArtifactView<'program>,
}
impl SourceCopyAssociation<'_, '_> {
    pub fn original_input(&self) -> &InputObservation {
        &self.view.program.custody.inputs[self.view.capture.original]
    }
    pub fn owned_source_input(&self) -> &InputObservation {
        &self.view.program.custody.inputs[self.view.capture.copy]
    }
    pub fn original_canonical_path(&self) -> &Path {
        &self.view.capture.original_canonical
    }
    pub fn sdk_argument_path(&self) -> &Path {
        &self.view.capture.sdk_argument
    }
    pub fn sdk_canonical_path(&self) -> &Path {
        &self.view.capture.sdk_canonical
    }
    pub fn utf8(&self) -> &str {
        &self.view.program.custody.sources[0].source
    }
    pub fn require_producer_path(
        &self,
        path: &Path,
        limits: PrimaryArtifactLimits,
    ) -> Result<(), PrimaryArtifactError> {
        let mut work = Work(limits.structural_units);
        work.path(path)?;
        if !path_equal(path, self.sdk_argument_path(), &mut work)?
            && !path_equal(path, self.sdk_canonical_path(), &mut work)?
        {
            return Err(PrimaryArtifactError::ProducerPathMismatch);
        }
        Ok(())
    }
    pub fn slice_utf8(&self, start: usize, end: usize) -> Result<&str, PrimaryArtifactError> {
        self.utf8()
            .get(start..end)
            .ok_or(PrimaryArtifactError::InvalidRange)
    }
    /// Every actual output companion, including frozen absence.
    pub fn output_parts(
        &self,
    ) -> impl ExactSizeIterator<Item = (&Path, Option<&InputObservation>)> {
        self.view.capture.parts.iter().map(|p| {
            (
                p.path.as_path(),
                p.observation.map(|i| &self.view.program.custody.inputs[i]),
            )
        })
    }
}

#[cfg(test)]
mod tests;
