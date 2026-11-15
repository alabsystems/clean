// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::ExternalLeanError;
use clean_kernel::Name;
use clean_olean::{parse_typed_imports, resolve_typed_module_path, LeanWorldScope};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::io::Read;
use std::path::{Component, Path, PathBuf};

/// Computed from actual files read by this run; never caller-provided hashes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InputObservation {
    pub path: PathBuf,
    pub sha256: [u8; 32],
    pub bytes: u64,
}

/// Presence includes dangling symlinks, matching the production artifact
/// reader: a present but unreadable companion is never sanitized to absence.
fn present(path: &Path) -> Result<bool, std::io::Error> {
    match std::fs::symlink_metadata(path) {
        Ok(_) => Ok(true),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(false),
        Err(error) => Err(error),
    }
}

fn observe(path: &Path) -> Result<InputObservation, ExternalLeanError> {
    let mut file = std::fs::File::open(path)?;
    let mut hash = Sha256::new();
    let mut bytes = 0u64;
    let mut buffer = [0u8; 65536];
    loop {
        let n = file.read(&mut buffer)?;
        if n == 0 {
            break;
        }
        hash.update(&buffer[..n]);
        bytes += n as u64;
    }
    Ok(InputObservation {
        path: path.to_path_buf(),
        sha256: hash.finalize().into(),
        bytes,
    })
}

#[derive(Default)]
pub(super) struct Files(BTreeMap<PathBuf, InputObservation>, BTreeSet<PathBuf>);
impl Files {
    pub(super) fn observe(&mut self, path: &Path) -> Result<(), ExternalLeanError> {
        let input = observe(path)?;
        if let Some(old) = self.0.get(path) {
            if old != &input {
                return Err(ExternalLeanError::Input(format!(
                    "input changed: {}",
                    path.display()
                )));
            }
        }
        self.0.insert(path.to_path_buf(), input);
        Ok(())
    }
    pub(super) fn absent(&mut self, path: &Path) {
        self.1.insert(path.to_path_buf());
    }
    pub(super) fn copy(&mut self, input: &Path, target: &Path) -> Result<(), ExternalLeanError> {
        self.observe(input)?;
        std::fs::copy(input, target)?;
        self.observe(target)?;
        let a = &self.0[input];
        let b = &self.0[target];
        if a.sha256 != b.sha256 || a.bytes != b.bytes {
            return Err(ExternalLeanError::Input("copy changed input bytes".into()));
        }
        if &observe(input)? != a {
            return Err(ExternalLeanError::Input(
                "source changed while copying".into(),
            ));
        }
        Ok(())
    }
    pub(super) fn check(&self) -> Result<(), ExternalLeanError> {
        for path in &self.1 {
            if present(path)? {
                return Err(ExternalLeanError::Input(format!(
                    "previously absent input appeared: {}",
                    path.display()
                )));
            }
        }
        for (path, old) in &self.0 {
            if old != &observe(path)? {
                return Err(ExternalLeanError::Input(format!(
                    "input changed: {}",
                    path.display()
                )));
            }
        }
        Ok(())
    }
    pub(super) fn into_observations(self) -> Vec<InputObservation> {
        self.0.into_values().collect()
    }
}

pub(super) fn module_path(
    root: &Path,
    module: &Name,
    extension: &str,
) -> Result<PathBuf, ExternalLeanError> {
    let mut cursor = module;
    while let clean_kernel::name::NameInner::Str(parent, part) = cursor.inner() {
        if part.is_empty() || part.contains(['/', '\\', '.', '\0']) {
            return Err(ExternalLeanError::Input(
                "external module components must have unambiguous filesystem identity".into(),
            ));
        }
        cursor = parent;
    }
    let relative = clean_olean::typed_module_rel_path(module)
        .map_err(|e| ExternalLeanError::Input(e.to_string()))?;
    if relative
        .components()
        .any(|c| !matches!(c, Component::Normal(_)))
    {
        return Err(ExternalLeanError::Input(
            "module escapes owned snapshot".into(),
        ));
    }
    Ok(root.join(relative).with_extension(extension))
}

pub(super) fn observe_frontend_libraries(
    lib: &Path,
    files: &mut Files,
) -> Result<(), ExternalLeanError> {
    // Lean's loader/native interpreter is part of elaboration's explicit TCB.
    for directory in [Some(lib), lib.parent()].into_iter().flatten() {
        for entry in std::fs::read_dir(directory)? {
            let path = entry?.path();
            if path.is_file()
                && matches!(
                    path.extension().and_then(|e| e.to_str()),
                    Some("dylib" | "so")
                )
            {
                files.observe(&path)?;
            }
        }
    }
    Ok(())
}

pub(super) fn observe_output(
    path: &Path,
    files: &mut Files,
    scope: &mut LeanWorldScope,
) -> Result<(), ExternalLeanError> {
    scope
        .admit_artifact(&path.display().to_string(), path)
        .map_err(|e| ExternalLeanError::Input(e.to_string()))?;
    for extension in ["olean", "olean.server", "olean.private", "ir"] {
        let part = path.with_extension(extension);
        if present(&part)? {
            files.observe(&part)?;
        } else {
            files.absent(&part);
        }
    }
    Ok(())
}

pub(super) fn capture_imports(
    roots: &[Name],
    search: &[PathBuf],
    snapshot: &Path,
    files: &mut Files,
    scope: &mut LeanWorldScope,
) -> Result<(), ExternalLeanError> {
    let mut pending = roots.to_vec();
    let mut seen = BTreeSet::new();
    while let Some(module) = pending.pop() {
        if !seen.insert(module.clone()) {
            continue;
        }
        if seen.len() > 4096 {
            return Err(ExternalLeanError::Input(
                "import closure exceeds 4096 modules".into(),
            ));
        }
        let input = resolve_typed_module_path(&module, search)
            .map_err(|e| ExternalLeanError::Input(e.to_string()))?;
        let target = module_path(snapshot, &module, "olean")?;
        if let Some(parent) = target.parent() {
            std::fs::create_dir_all(parent)?;
        }
        for extension in ["olean", "olean.server", "olean.private", "ir"] {
            let path = input.with_extension(extension);
            if present(&path)? {
                let copied = target.with_extension(extension);
                files.copy(&path, &copied)?;
                // Follow each part's typed imports. Artifact consistency is
                // subsequently checked by the actual production import loader.
                if extension != "ir" {
                    let bytes = std::fs::read(&copied)?;
                    scope
                        .admit_part(&format!("{module:?} ({extension})"), &bytes)
                        .map_err(|e| ExternalLeanError::Input(e.to_string()))?;
                    // Incremental companions borrow their base region; parsing
                    // their imports in isolation is invalid. The authoritative
                    // artifact reader checks header/import equality later.
                    if extension == "olean" {
                        pending.extend(
                            parse_typed_imports(&bytes)
                                .map_err(|e| ExternalLeanError::Input(e.to_string()))?
                                .into_iter()
                                .map(|import| import.module_name),
                        );
                    }
                }
            } else {
                files.absent(&path);
                files.absent(&target.with_extension(extension));
            }
        }
    }
    files.check()
}
