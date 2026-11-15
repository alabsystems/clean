// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lake-aware module scope and import/dependent closure for factory checks.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use clean_kernel::Name;
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
        workspace
            .validate_module_index()
            .map_err(|error| FactoryOpsError::LeanAnalysis {
                path: root.clone(),
                message: error.to_string(),
            })?;
        let mut files = workspace
            .all_module_names()
            .into_iter()
            .map(|module| {
                workspace
                    .find_module_name(&module)
                    .ok_or_else(|| FactoryOpsError::LeanAnalysis {
                        path: root.clone(),
                        message: format!("indexed module {module:?} has no exact source path"),
                    })
            })
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
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
    let graph = ModuleGraph::build(&root, &active)?;
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
        impacted.insert(path.strip_prefix(&root).unwrap_or(&path).to_path_buf());
        let module = module_name_from_path(&root, &path)?;
        queue.push_back(module);
    }

    let mut seen_modules = BTreeSet::new();
    while let Some(module) = queue.pop_front() {
        if !seen_modules.insert(module.clone()) {
            continue;
        }
        if let Some(path) = graph.file_by_module.get(&module) {
            impacted.insert(path.strip_prefix(&root).unwrap_or(path).to_path_buf());
        }
        if let Some(dependents) = graph.reverse_imports.get(&module) {
            for dependent in dependents {
                queue.push_back(dependent.clone());
            }
        }
    }

    Ok(impacted.into_iter().collect())
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
    file_by_module: BTreeMap<Name, PathBuf>,
    reverse_imports: BTreeMap<Name, BTreeSet<Name>>,
}

impl ModuleGraph {
    fn build(root: &Path, active_files: &[PathBuf]) -> Result<Self, FactoryOpsError> {
        let mut file_by_module = BTreeMap::new();
        for file in active_files {
            let module = module_name_from_path(root, file)?;
            file_by_module.insert(module, file.clone());
        }

        let mut reverse_imports: BTreeMap<Name, BTreeSet<Name>> = BTreeMap::new();
        for file in active_files {
            let module = module_name_from_path(root, file)?;
            let text = fs::read_to_string(file).map_err(|source| FactoryOpsError::Io {
                path: file.clone(),
                source,
            })?;
            for imported in import_modules(&text) {
                reverse_imports
                    .entry(imported)
                    .or_default()
                    .insert(module.clone());
            }
        }

        Ok(Self {
            file_by_module,
            reverse_imports,
        })
    }
}

fn import_modules(text: &str) -> Vec<Name> {
    let mut imports = clean_parser::notation_seed::scan_imports(text)
        .into_iter()
        .map(clean_parser::SurfaceName::into_name)
        .collect::<Vec<_>>();
    imports.sort();
    imports.dedup();
    imports
}

fn module_name_from_path(root: &Path, path: &Path) -> Result<Name, FactoryOpsError> {
    let relative = path.strip_prefix(root).unwrap_or(path).with_extension("");
    relative
        .components()
        .try_fold(Name::anon(), |name, component| {
            let std::path::Component::Normal(part) = component else {
                return Err(FactoryOpsError::LeanAnalysis {
                    path: path.to_path_buf(),
                    message: "module path is not relative to the source root".to_owned(),
                });
            };
            let part = part.to_str().ok_or_else(|| FactoryOpsError::LeanAnalysis {
                path: path.to_path_buf(),
                message: "module component is not UTF-8".to_owned(),
            })?;
            Ok(name.str(part))
        })
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
    fn import_closure_distinguishes_quoted_dotted_files_and_hierarchical_paths() {
        let dir = tempfile::tempdir().expect("tempdir");
        fs::create_dir(dir.path().join("A")).expect("nested directory");
        fs::write(dir.path().join("A.B.lean"), "def quoted : Nat := 1\n").expect("quoted file");
        fs::write(dir.path().join("A/B.lean"), "def nested : Nat := 2\n").expect("nested file");
        fs::write(
            dir.path().join("Quoted.lean"),
            "import «A.B»\ndef q : Nat := 1\n",
        )
        .expect("quoted consumer");
        fs::write(
            dir.path().join("Nested.lean"),
            "import A.B\ndef n : Nat := 2\n",
        )
        .expect("nested consumer");
        assert_eq!(
            impacted_lean_files(dir.path(), &[PathBuf::from("A.B.lean")]).expect("quoted closure"),
            vec![PathBuf::from("A.B.lean"), PathBuf::from("Quoted.lean")]
        );
        assert_eq!(
            impacted_lean_files(dir.path(), &[PathBuf::from("A/B.lean")]).expect("nested closure"),
            vec![PathBuf::from("A/B.lean"), PathBuf::from("Nested.lean")]
        );
    }

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
