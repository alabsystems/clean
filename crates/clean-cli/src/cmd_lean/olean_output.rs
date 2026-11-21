// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Stable Lean module naming and native artifact publication.

use std::collections::HashSet;
use std::fs;
use std::path::{Path, PathBuf};

use anyhow::{bail, Context};
use clean_kernel::Name;
use clean_olean::{export::LeanV2ModuleParts, ImportWorld, OleanHeader, SourceWorldDecision};

pub(super) fn module_name(file: &Path, root: Option<&Path>) -> anyhow::Result<Name> {
    let root = root.unwrap_or_else(|| Path::new(".")).canonicalize()?;
    let path = file.canonicalize()?;
    let relative = path.strip_prefix(&root).with_context(|| {
        format!(
            "input file '{}' must be contained in root directory ({}/)",
            path.display(),
            root.display()
        )
    })?;
    relative
        .with_extension("")
        .components()
        .try_fold(Name::anon(), |name, component| {
            let part = component
                .as_os_str()
                .to_str()
                .context("module path contains a non-UTF-8 component")?;
            Ok(name.str(part))
        })
}

pub(super) fn stable_header(decision: &SourceWorldDecision) -> anyhow::Result<OleanHeader> {
    let world = decision.import_world()?;
    let (ImportWorld::Explicit { lib, .. } | ImportWorld::Project { lib, .. }) = world else {
        bail!("Lean v2 output requires a verified stable SDK");
    };
    let path = lib.join("Init/Prelude.olean");
    let mut input = fs::File::open(&path).with_context(|| path.display().to_string())?;
    let mut bytes = [0; clean_olean::header::HEADER_SIZE_V2];
    std::io::Read::read_exact(&mut input, &mut bytes)?;
    Ok(OleanHeader::parse(&bytes)?)
}

struct OutputPart {
    path: PathBuf,
    staged: PathBuf,
    previous: Option<PathBuf>,
}

/// Stage every part before replacing any output. Make the base visible last
/// and restore replaced files if the publication fails.
pub(super) fn publish(base: &Path, parts: LeanV2ModuleParts) -> anyhow::Result<()> {
    let file = base.file_name().context("missing .olean output filename")?;
    let directory = base
        .parent()
        .filter(|dir| !dir.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."))
        .canonicalize()?;
    let base = directory.join(file);
    let mut outputs = Vec::new();
    for (path, bytes) in [
        (base.with_extension("ir.sig"), parts.ir_signature),
        (base.with_extension("ir"), parts.ir),
        (with_suffix(&base, ".server"), parts.server),
        (with_suffix(&base, ".private"), parts.private),
        (base, Some(parts.base)),
    ] {
        if let Some(bytes) = bytes {
            outputs.push((path, bytes));
        }
    }
    let mut unique = HashSet::new();
    if outputs.iter().any(|(path, _)| !unique.insert(path.clone())) {
        bail!("the requested output name collides with a Lean companion file");
    }
    let transaction = tempfile::tempdir_in(&directory)?;
    let mut prepared = Vec::new();
    for (ordinal, (path, bytes)) in outputs.into_iter().enumerate() {
        let staged = transaction.path().join(format!("part-{ordinal}"));
        fs::write(&staged, bytes)?;
        prepared.push(OutputPart {
            path,
            staged,
            previous: None,
        });
    }
    // Cooperating writers share the parent directory's inode and need no
    // persistent lock file beside the Lean artifacts.
    #[cfg(unix)]
    let _directory_lock = {
        let directory = fs::File::open(&directory)?;
        directory.lock()?;
        directory
    };
    for (ordinal, part) in prepared.iter_mut().enumerate() {
        let path = &part.path;
        part.previous = match fs::symlink_metadata(path) {
            Ok(metadata) if metadata.is_file() => {
                let backup = transaction.path().join(format!("previous-{ordinal}"));
                fs::hard_link(path, &backup)
                    .with_context(|| format!("could not retain {}", path.display()))?;
                Some(backup)
            }
            Ok(_) => bail!("Lean output path is not a regular file: {}", path.display()),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
            Err(error) => return Err(error).with_context(|| path.display().to_string()),
        };
    }
    for (index, part) in prepared.iter().enumerate() {
        if let Err(error) = fs::rename(&part.staged, &part.path) {
            let mut restore_errors = Vec::new();
            for completed in prepared[..index].iter().rev() {
                let restore = match &completed.previous {
                    Some(previous) => fs::rename(previous, &completed.path),
                    None => fs::remove_file(&completed.path),
                };
                if let Err(error) = restore {
                    restore_errors.push(format!("{}: {error}", completed.path.display()));
                }
            }
            if !restore_errors.is_empty() {
                let backup = transaction.keep();
                bail!(
                    "could not write {}: {error}. Recovery files are in {}. {}",
                    part.path.display(),
                    backup.display(),
                    restore_errors.join(". ")
                );
            }
            return Err(error).with_context(|| format!("could not write {}", part.path.display()));
        }
    }
    Ok(())
}

fn with_suffix(path: &Path, suffix: &str) -> PathBuf {
    let mut name = path.as_os_str().to_owned();
    name.push(suffix);
    PathBuf::from(name)
}
