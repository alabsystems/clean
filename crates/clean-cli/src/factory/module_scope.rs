// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lake-aware module scope and import/dependent closure for factory checks.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use walkdir::{DirEntry, WalkDir};

use super::FactoryOpsError;

/// Source scope used by a merge check.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct ScopeReport {
    pub(crate) kind: String,
    pub(crate) active_lean_files: Vec<String>,
    pub(crate) impacted_lean_files: Vec<String>,
}

/// Resolve active Lean source files for a repository or source root.
pub(crate) fn active_lean_files(root: &Path) -> Result<Vec<PathBuf>, FactoryOpsError> {
    let root = normalize_root(root);
    if let Ok(workspace) = clean_lake::Workspace::load(&root) {
        let mut files = workspace
            .all_modules()
            .into_iter()
            .filter_map(|module| workspace.find_module(&module))
            .filter(|path| is_lean_source_file(&root, path))
            .collect::<Vec<_>>();
        files.sort();
        files.dedup();
        if !files.is_empty() {
            return Ok(files);
        }
    }
    discover_lean_files(&root)
}

/// Resolve changed files plus active modules that transitively import them.
pub(crate) fn impacted_lean_files(
    root: &Path,
    changed_paths: &[PathBuf],
) -> Result<Vec<PathBuf>, FactoryOpsError> {
    let root = normalize_root(root);
    let active = active_lean_files(&root)?;
    let graph = ModuleGraph::build(&root, &active);
    let mut impacted = BTreeSet::new();

    let changed_abs = changed_paths
        .iter()
        .map(|path| {
            if path.is_absolute() {
                path.to_owned()
            } else {
                root.join(path)
            }
        })
        .collect::<Vec<_>>();

    let mut queue = VecDeque::new();
    for path in changed_abs {
        let report_path = relative_path(&root, &path);
        impacted.insert(report_path.clone());
        let module = graph
            .module_by_report_path
            .get(&report_path)
            .cloned()
            .unwrap_or_else(|| module_name_from_report_path(&report_path));
        queue.push_back(module);
    }

    let mut seen_modules = BTreeSet::new();
    while let Some(module) = queue.pop_front() {
        if !seen_modules.insert(module.clone()) {
            continue;
        }
        if let Some(path) = graph.file_by_module.get(&module) {
            impacted.insert(path.clone());
        }
        if let Some(dependents) = graph.reverse_imports.get(&module) {
            for dependent in dependents {
                queue.push_back(dependent.clone());
            }
        }
    }

    Ok(impacted.into_iter().map(PathBuf::from).collect::<Vec<_>>())
}

pub(crate) fn scope_report(
    root: &Path,
    changed_paths: &[PathBuf],
) -> Result<ScopeReport, FactoryOpsError> {
    let root = normalize_root(root);
    let active = active_lean_files(&root)?;
    let impacted = impacted_lean_files(&root, changed_paths)?;
    let kind = if root.join("lakefile.lean").is_file() {
        "lake_workspace"
    } else {
        "source_tree"
    };
    Ok(ScopeReport {
        kind: kind.to_owned(),
        active_lean_files: active
            .iter()
            .map(|path| relative_path(&root, path))
            .collect(),
        impacted_lean_files: impacted
            .iter()
            .map(|path| path.to_string_lossy().replace('\\', "/"))
            .collect(),
    })
}

struct ModuleGraph {
    module_by_report_path: BTreeMap<String, String>,
    file_by_module: BTreeMap<String, String>,
    reverse_imports: BTreeMap<String, BTreeSet<String>>,
}

impl ModuleGraph {
    fn build(root: &Path, active_files: &[PathBuf]) -> Self {
        let mut module_by_report_path = BTreeMap::new();
        let mut file_by_module = BTreeMap::new();
        for file in active_files {
            let report_path = relative_path(root, file);
            let module = module_name_from_report_path(&report_path);
            module_by_report_path.insert(report_path.clone(), module.clone());
            file_by_module.insert(module, report_path);
        }

        let mut reverse_imports: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for file in active_files {
            let report_path = relative_path(root, file);
            let module = module_name_from_report_path(&report_path);
            let Ok(text) = fs::read_to_string(file) else {
                continue;
            };
            for imported in import_modules(&text) {
                reverse_imports
                    .entry(imported)
                    .or_default()
                    .insert(module.clone());
            }
        }

        Self {
            module_by_report_path,
            file_by_module,
            reverse_imports,
        }
    }
}

fn import_modules(text: &str) -> Vec<String> {
    let mut imports = Vec::new();
    for line in text.lines() {
        let line = line.split("--").next().unwrap_or("").trim();
        let Some(rest) = line.strip_prefix("import ") else {
            if !line.is_empty() && !line.starts_with("@[") {
                break;
            }
            continue;
        };
        imports.extend(
            rest.split_whitespace()
                .map(|part| {
                    part.trim_matches(|ch: char| {
                        !(ch.is_ascii_alphanumeric() || ch == '_' || ch == '.')
                    })
                })
                .filter(|part| !part.is_empty())
                .map(ToOwned::to_owned),
        );
    }
    imports.sort();
    imports.dedup();
    imports
}

fn module_name_from_report_path(path: &str) -> String {
    path.strip_suffix(".lean")
        .unwrap_or(path)
        .replace(['/', '\\'], ".")
}

fn discover_lean_files(root: &Path) -> Result<Vec<PathBuf>, FactoryOpsError> {
    let mut files = Vec::new();
    for entry in WalkDir::new(root)
        .into_iter()
        .filter_entry(|entry| !is_skipped_entry(root, entry))
    {
        let entry = entry.map_err(|source| FactoryOpsError::Io {
            path: root.to_owned(),
            source: io::Error::other(source),
        })?;
        let path = entry.path();
        if is_lean_source_file(root, path) {
            files.push(path.to_owned());
        }
    }
    files.sort();
    files.dedup();
    Ok(files)
}

fn is_lean_source_file(root: &Path, path: &Path) -> bool {
    path.is_file()
        && path.extension().is_some_and(|ext| ext == "lean")
        && path
            .strip_prefix(root)
            .ok()
            .is_none_or(|relative| relative != Path::new("lakefile.lean"))
}

fn is_skipped_entry(root: &Path, entry: &DirEntry) -> bool {
    if entry.path() == root {
        return false;
    }
    entry.file_type().is_dir()
        && entry.file_name().to_str().is_some_and(|name| {
            matches!(
                name,
                ".git" | ".lake" | "target" | "node_modules" | "archive"
            )
        })
}

fn normalize_root(root: &Path) -> PathBuf {
    let path = if root.is_absolute() {
        root.to_owned()
    } else {
        std::env::current_dir()
            .unwrap_or_else(|_| PathBuf::from("."))
            .join(root)
    };
    fs::canonicalize(&path).unwrap_or(path)
}

fn relative_path(root: &Path, path: &Path) -> String {
    path.strip_prefix(root)
        .unwrap_or(path)
        .to_string_lossy()
        .replace('\\', "/")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn import_closure_finds_transitive_dependents() {
        let dir = tempfile::tempdir().expect("tempdir");
        fs::write(dir.path().join("A.lean"), "def a : Nat := 1\n").expect("write A");
        fs::write(dir.path().join("B.lean"), "import A\ndef b : Nat := 2\n").expect("write B");
        fs::write(dir.path().join("C.lean"), "import B\ndef c : Nat := 3\n").expect("write C");

        let impacted =
            impacted_lean_files(dir.path(), &[PathBuf::from("A.lean")]).expect("impacted");

        assert_eq!(
            impacted,
            vec![
                PathBuf::from("A.lean"),
                PathBuf::from("B.lean"),
                PathBuf::from("C.lean")
            ]
        );
    }

    #[test]
    fn import_closure_tracks_dependents_of_deleted_modules() {
        let dir = tempfile::tempdir().expect("tempdir");
        fs::write(dir.path().join("B.lean"), "import A\ndef b : Nat := 2\n").expect("write B");
        fs::write(dir.path().join("C.lean"), "import B\ndef c : Nat := 3\n").expect("write C");

        let impacted =
            impacted_lean_files(dir.path(), &[PathBuf::from("A.lean")]).expect("impacted");

        assert_eq!(
            impacted,
            vec![
                PathBuf::from("A.lean"),
                PathBuf::from("B.lean"),
                PathBuf::from("C.lean")
            ]
        );
    }

    #[test]
    fn lake_scope_finds_import_dependents() {
        let dir = tempfile::tempdir().expect("tempdir");
        fs::write(
            dir.path().join("lakefile.lean"),
            "package test\nlean_lib Test\n",
        )
        .expect("write lakefile");
        fs::write(dir.path().join("A.lean"), "def a : Nat := 1\n").expect("write A");
        fs::write(dir.path().join("B.lean"), "import A\ndef b : Nat := 2\n").expect("write B");

        let report = scope_report(dir.path(), &[PathBuf::from("A.lean")]).expect("scope");

        assert_eq!(report.kind, "lake_workspace");
        assert!(report.active_lean_files.contains(&"B.lean".to_owned()));
        assert!(report.impacted_lean_files.contains(&"B.lean".to_owned()));
    }
}
