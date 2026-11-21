// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Repository-relative Lean files in the specification and control roots.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
};

use walkdir::WalkDir;

use super::Specification;

pub(super) fn discover(
    root: &Path,
    spec: &Specification,
    unreadable: &mut BTreeMap<PathBuf, String>,
) -> BTreeSet<PathBuf> {
    let mut roots = BTreeMap::from([(spec.root.as_path(), BTreeSet::from([Path::new("")]))]);
    for (prefix, directory) in &spec.control_roots {
        roots
            .entry(directory.as_path())
            .or_default()
            .insert(Path::new(prefix));
    }

    let mut files = BTreeSet::new();
    for (directory, prefixes) in roots {
        let absolute = match source_directory(root, directory) {
            Ok(path) => path,
            Err(error) => {
                unreadable.entry(directory.to_owned()).or_insert(error);
                continue;
            }
        };
        if excluded(directory) {
            continue;
        }

        // A parent of a selected prefix has to be traversed, but its files
        // and other subdirectories are outside that prefix.
        let in_walk = |path: &Path| {
            let Ok(relative) = path.strip_prefix(&absolute) else {
                return false;
            };
            !excluded(relative)
                && prefixes
                    .iter()
                    .any(|prefix| relative.starts_with(prefix) || prefix.starts_with(relative))
        };
        let entries = WalkDir::new(&absolute)
            .follow_root_links(false)
            .into_iter()
            .filter_entry(|entry| in_walk(entry.path()));
        for entry in entries {
            let entry = match entry {
                Ok(entry) => entry,
                Err(error) => {
                    let path = error.path().unwrap_or(&absolute);
                    // WalkDir's entry filter does not filter error values.
                    if in_walk(path) {
                        let key = path.strip_prefix(root).unwrap_or(directory);
                        unreadable
                            .entry(key.to_owned())
                            .or_insert_with(|| error.to_string());
                    }
                    continue;
                }
            };
            let Ok(relative) = entry.path().strip_prefix(&absolute) else {
                continue;
            };
            let file_type = entry.file_type();
            if file_type.is_symlink() && prefixes.iter().any(|prefix| prefix.starts_with(relative))
            {
                let path = directory.join(relative);
                unreadable.entry(path).or_insert_with(|| {
                    format!(
                        "{}: a symbolic link blocks a control prefix",
                        entry.path().display()
                    )
                });
                continue;
            }
            if file_type.is_dir()
                || relative
                    .extension()
                    .is_none_or(|extension| extension != "lean")
                || !prefixes.iter().any(|prefix| relative.starts_with(prefix))
            {
                continue;
            }
            let path = directory.join(relative);
            if file_type.is_file() {
                files.insert(path);
            } else {
                unreadable.entry(path).or_insert_with(|| {
                    format!(
                        "{} is not a regular Lean source file",
                        entry.path().display()
                    )
                });
            }
        }
    }
    files
}

fn excluded(path: &Path) -> bool {
    path.components().any(|part| part.as_os_str() == ".lake")
}

fn source_directory(root: &Path, directory: &Path) -> Result<PathBuf, String> {
    let path = root.join(directory);
    let metadata =
        fs::symlink_metadata(&path).map_err(|error| format!("{}: {error}", path.display()))?;
    if !metadata.is_dir() {
        return Err(format!(
            "{} is not a regular source directory",
            path.display()
        ));
    }
    Ok(path)
}
