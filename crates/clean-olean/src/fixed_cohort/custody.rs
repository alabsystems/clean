// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Physical input custody only. Neither an inventory nor hashes admit math.
use super::Manifest;
use std::collections::BTreeSet;
use std::io::Read;
use std::path::Path;

fn part_name(path: &Path) -> bool {
    path.file_name()
        .and_then(|name| name.to_str())
        .is_some_and(|name| {
            [".olean", ".olean.server", ".olean.private", ".ir"]
                .iter()
                .any(|suffix| name.ends_with(suffix))
        })
}

fn regular(path: &Path) -> Result<std::fs::Metadata, String> {
    let metadata = std::fs::symlink_metadata(path)
        .map_err(|error| format!("fixed cohort artifact metadata {}: {error}", path.display()))?;
    if metadata.file_type().is_symlink() {
        return Err(format!(
            "fixed cohort artifact symlink refused: {}",
            path.display()
        ));
    }
    if !metadata.is_file() {
        return Err(format!(
            "fixed cohort artifact is not a regular file: {}",
            path.display()
        ));
    }
    if path.canonicalize().map_err(|error| error.to_string())? != path {
        return Err(format!(
            "fixed cohort artifact path alias refused: {}",
            path.display()
        ));
    }
    Ok(metadata)
}

/// Read the exact immutable contents of one regular companion, preserving
/// absence. Unix opens refuse symlink replacement and cannot block on a FIFO.
pub(super) fn captured_optional(path: &Path) -> Result<Option<Vec<u8>>, String> {
    match std::fs::symlink_metadata(path) {
        Ok(_) => {}
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(error) => return Err(error.to_string()),
    }
    let before = regular(path)?;
    let mut options = std::fs::OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK);
    }
    let mut file = options
        .open(path)
        .map_err(|error| format!("fixed cohort artifact open {}: {error}", path.display()))?;
    let opened = file.metadata().map_err(|error| error.to_string())?;
    if !opened.is_file() {
        return Err("captured fixed cohort part is not a regular file".into());
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        if before.dev() != opened.dev() || before.ino() != opened.ino() {
            return Err("fixed cohort artifact changed during capture".into());
        }
    }
    #[cfg(not(unix))]
    let _ = before;
    let mut bytes = Vec::new();
    file.read_to_end(&mut bytes)
        .map_err(|error| error.to_string())?;
    Ok(Some(bytes))
}

/// Require exactly the complete original manifest's module-artifact population.
/// Non-artifact package metadata (e.g. a manifest JSON or README) is not loaded
/// and does not confer authority. No directory, symlink or unreadable traversal
/// can hide another .olean/companion/.ir input. Run BEFORE library partitioning.
pub(super) fn validate_artifact_census(
    directory: &Path,
    manifest: &Manifest,
) -> Result<(), String> {
    let root = directory
        .canonicalize()
        .map_err(|error| error.to_string())?;
    let mut expected = BTreeSet::new();
    for (module, parts) in &manifest.modules {
        if module.split('.').any(|part| {
            part.is_empty()
                || !part
                    .bytes()
                    .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
        }) {
            return Err("invalid fixed cohort module identity".into());
        }
        let base = root.join(module.replace('.', "/") + ".olean");
        expected.insert(base.clone());
        for (present, extension) in [
            (parts.server.is_some(), "olean.server"),
            (parts.private.is_some(), "olean.private"),
            (parts.ir.is_some(), "ir"),
        ] {
            if present {
                expected.insert(base.with_extension(extension));
            }
        }
    }
    for path in &expected {
        regular(path)?;
    }
    let mut pending = vec![root];
    let mut actual = BTreeSet::new();
    while let Some(directory) = pending.pop() {
        for entry in std::fs::read_dir(&directory).map_err(|error| {
            format!(
                "fixed cohort directory read {}: {error}",
                directory.display()
            )
        })? {
            let entry = entry.map_err(|error| error.to_string())?;
            let path = entry.path();
            let kind = entry.file_type().map_err(|error| error.to_string())?;
            if kind.is_symlink() {
                return Err(format!(
                    "fixed cohort directory or artifact symlink refused: {}",
                    path.display()
                ));
            }
            if kind.is_dir() {
                if part_name(&path) {
                    return Err(format!(
                        "fixed cohort artifact is not a regular file: {}",
                        path.display()
                    ));
                }
                pending.push(path);
            } else if part_name(&path) {
                regular(&path)?;
                actual.insert(path);
            }
        }
    }
    if actual != expected {
        let extra = actual
            .difference(&expected)
            .map(|path| path.display().to_string())
            .collect::<Vec<_>>();
        let missing = expected
            .difference(&actual)
            .map(|path| path.display().to_string())
            .collect::<Vec<_>>();
        return Err(format!("fixed cohort physical artifact population differs: extra={extra:?} missing={missing:?}"));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    fn manifest() -> Manifest {
        serde_json::from_value(serde_json::json!({"schema":"cohort", "ir_commit":"data", "lean_version":"4.30.0-rc2", "lean_githash":"data", "source_sha256":{}, "modules":{"Library":{"base":"data"}}})).unwrap()
    }
    #[test]
    fn unimported_extra_olean_and_ir_are_not_hidden_by_loaded_module_census() {
        // A file-custody control only: no fake artifact is parsed or accepted.
        let directory = tempfile::tempdir().unwrap();
        std::fs::write(directory.path().join("Library.olean"), b"custody data").unwrap();
        validate_artifact_census(directory.path(), &manifest()).unwrap();
        for extra in ["Unimported.olean", "Unimported.ir", "Library.ir"] {
            let path = directory.path().join(extra);
            std::fs::write(&path, b"unmanifested input").unwrap();
            assert!(validate_artifact_census(directory.path(), &manifest())
                .unwrap_err()
                .contains("physical artifact population differs"));
            std::fs::remove_file(path).unwrap();
        }
    }
    #[cfg(unix)]
    #[test]
    fn identical_byte_source_and_companion_symlinks_are_refused() {
        use std::os::unix::fs::symlink;
        let directory = tempfile::tempdir().unwrap();
        let outside = tempfile::NamedTempFile::new().unwrap();
        std::fs::write(outside.path(), b"same bytes").unwrap();
        for extension in ["olean", "ir", "olean.server", "olean.private"] {
            let path = directory.path().join(format!("Library.{extension}"));
            symlink(outside.path(), &path).unwrap();
            assert!(captured_optional(&path).unwrap_err().contains("symlink"));
            if extension == "olean" {
                assert!(validate_artifact_census(directory.path(), &manifest())
                    .unwrap_err()
                    .contains("symlink"));
            }
            std::fs::remove_file(path).unwrap();
        }
        let directory_part = directory.path().join("Library.ir");
        std::fs::create_dir(&directory_part).unwrap();
        assert!(captured_optional(&directory_part)
            .unwrap_err()
            .contains("regular file"));
    }
}
