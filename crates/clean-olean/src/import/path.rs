// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Path resolution for .olean module names.
//!
//! Converts dot-separated Lean module names to filesystem paths and
//! discovers search paths from environment variables, the repository-pinned
//! Lean toolchain, and lake package build outputs.
//!
//! # External Package Support
//!
//! Lake (Lean's build system) compiles packages into `.lake/packages/<pkg>/build/lib/`.
//! The `LEAN_PACKAGES_PATH` environment variable and [`SearchPathBuilder`] API allow
//! specifying additional package roots for external libraries like TorchLean.

use super::ImportError;
use clean_kernel::name::{Name, NameInner};
use hashbrown::HashSet;
use std::env;
use std::path::{Path, PathBuf};

pub(super) fn module_name_to_rel_path(module: &str) -> Option<PathBuf> {
    let trimmed = module.trim_matches('.');
    if trimmed.is_empty() {
        return None;
    }

    let mut path = PathBuf::new();
    for part in trimmed.split('.') {
        if part.is_empty() {
            return None;
        }
        path.push(part);
    }
    path.set_extension("olean");
    Some(path)
}

/// Structural counterpart of Lean's `modToFilePath`: each Name.str is one
/// path append, and `.olean` is appended, never substituted for a quoted dot.
/// Numeric Name constructors are ill-formed module imports in upstream Lean.
pub fn typed_module_rel_path(module: &Name) -> Result<PathBuf, ImportError> {
    let mut components = Vec::new();
    let mut current = module;
    loop {
        match current.inner() {
            NameInner::Anon => break,
            NameInner::Str(parent, value) => {
                components.push(value.as_ref());
                current = parent;
            }
            NameInner::Num(_, _) => {
                return Err(ImportError::UnsupportedModule {
                    module: format!("{module:?}"),
                    reason: "numeric Name constructors are not Lean module path components".into(),
                })
            }
        }
    }
    if components.is_empty() {
        return Err(ImportError::UnsupportedModule {
            module: format!("{module:?}"),
            reason: "anonymous module has no import path".into(),
        });
    }
    let mut path = PathBuf::new();
    for component in components.into_iter().rev() {
        path.push(component);
    }
    path.as_mut_os_string().push(".olean");
    Ok(path)
}

/// Resolve an exact typed module identity in caller-supplied search order.
pub fn resolve_typed_module_path(
    module: &Name,
    search_paths: &[PathBuf],
) -> Result<PathBuf, ImportError> {
    resolve_typed_module_file(module, search_paths).map(|(_, path)| path)
}

/// [`resolve_typed_module_path`], with the index in `search_paths` of the
/// directory the file was found in.
pub(crate) fn resolve_typed_module_file(
    module: &Name,
    search_paths: &[PathBuf],
) -> Result<(usize, PathBuf), ImportError> {
    let relative = typed_module_rel_path(module)?;
    let mut searched = Vec::new();
    for (index, root) in search_paths.iter().enumerate() {
        let candidate = root.join(&relative);
        searched.push(candidate.clone());
        if candidate.exists() {
            return Ok((index, candidate));
        }
    }
    Err(ImportError::ModuleNotFound {
        module: format!("{module:?}"),
        searched,
    })
}

/// Compatibility spelling used by existing String-root APIs. Components are
/// literal strings, including digit-only components; this is not Name display
/// reconstruction, nor a parser for Lean's quoted-identifier syntax.
pub(crate) fn legacy_module_name(module: &str) -> Result<Name, ImportError> {
    module_name_to_rel_path(module).ok_or_else(|| ImportError::UnsupportedModule {
        module: module.to_owned(),
        reason: "module name is empty or contains empty dot-separated components; use a typed Name for quoted components".into(),
    })?;
    Ok(module
        .trim_matches('.')
        .split('.')
        .fold(Name::anon(), |parent, component| parent.str(component)))
}

/// Injective storage key for the legacy caller-owned `HashSet<String>`.
/// Ordinary dotted string names retain their historical keys. Other structural
/// names use a reserved NUL prefix and UTF-8 byte-length framing; keys are never
/// reparsed as module names or paths. No filesystem module can use that prefix.
pub(super) fn module_visit_key(module: &Name) -> Result<String, ImportError> {
    // Validate the structural root before a caller-supplied completed key can
    // suppress path resolution (in particular, Num/anonymous are not paths).
    typed_module_rel_path(module)?;
    let mut parts = Vec::new();
    let mut current = module;
    while let NameInner::Str(parent, part) = current.inner() {
        parts.push(part.as_ref());
        current = parent;
    }
    parts.reverse();
    if parts
        .iter()
        .all(|part| !part.is_empty() && !part.contains(['.', '\0']))
    {
        return Ok(parts.join("."));
    }
    let mut key = String::from("\0clean.module.str/v1:");
    for part in parts {
        key.push_str(&part.len().to_string());
        key.push(':');
        key.push_str(part);
    }
    Ok(key)
}

#[cfg(test)]
mod typed_visit_key_tests;

/// Discover lake package build output directories under a project root.
///
/// Scans `<project_root>/.lake/packages/*/…` for directories that contain
/// `.olean` files, plus the project's own build output.
///
/// Recognizes three output layouts:
/// - **legacy (Lake v3):** `build/lib/`
/// - **`clean lake`:** `.lake/build/lib/` (see [`clean_lake_lib_dir`])
/// - **modern (Lake v4, e.g. toolchain `v4.30.0-rc2`):** `.lake/build/lib/lean/`
///   — the project's own oleans live at `<root>/.lake/build/lib/lean/`, and each
///   dependency's at `<root>/.lake/packages/<pkg>/.lake/build/lib/lean/`.
///
/// The modern layout is why a `lake exe cache get` Mathlib tree keeps Mathlib +
/// Lean oleans in `<root>/.lake/build/lib/lean/` but Batteries / Std / Aesop
/// oleans under `<root>/.lake/packages/<pkg>/.lake/build/lib/lean/`; without the
/// nested-`.lake` candidate here those dependency oleans are invisible and the
/// front-end falls back to (re-)elaborating their `.lean` source.
///
/// # REQUIRES
/// - `project_root` should be a directory (does not need to contain a lakefile)
///
/// # ENSURES
/// - Returns only directories that actually exist
/// - Does not recurse into nested lake projects
pub(crate) fn discover_lake_package_paths<R>(project_root: &Path, mut read_dir: R) -> Vec<PathBuf>
where
    R: for<'a> FnMut(&'a Path) -> std::io::Result<std::fs::ReadDir>,
{
    // Candidate `<dir>/<rel>` olean lib directories, legacy first then modern.
    const LIB_RELS: [&str; 2] = ["build/lib", ".lake/build/lib/lean"];
    let mut paths = Vec::new();

    // Check the project's own build output (every layout).
    for rel in LIB_RELS {
        let own_build = project_root.join(rel);
        if own_build.exists() {
            paths.push(own_build);
        }
    }
    if let Some(clean_lake_lib) = clean_lake_lib_dir(project_root) {
        paths.push(clean_lake_lib);
    }

    // Check lake packages directory (every layout per package).
    let packages_dir = project_root.join(".lake/packages");
    if let Ok(entries) = read_dir(&packages_dir) {
        for entry in entries.flatten() {
            for rel in LIB_RELS {
                let lib_path = entry.path().join(rel);
                if lib_path.exists() {
                    paths.push(lib_path);
                }
            }
            if let Some(clean_lake_lib) = clean_lake_lib_dir(&entry.path()) {
                paths.push(clean_lake_lib);
            }
        }
    }

    paths
}

/// `<root>/.lake/build/lib` when it is `clean lake`'s own output, which writes
/// module `.olean`s there directly (`clean_lake::Workspace::lib_dir`), the
/// project's modules and its PATH dependencies' alike.
///
/// Lake v4 writes under `lib/lean/` instead, so a `lib` that holds a `lean/`
/// directory is Lake's layout and is not searched a second time. Until
/// 2026-09-29 this layout was searched by nothing but `clean lake`'s own
/// module build: the native step of `clean lake build <exe>` then resolved an
/// import of a path dependency to no artifact and, once imports became
/// fail-closed, refused it (`lake_path_stripped`'s dependency workflow).
fn clean_lake_lib_dir(root: &Path) -> Option<PathBuf> {
    let lib = root.join(".lake/build/lib");
    (lib.is_dir() && !lib.join("lean").exists()).then_some(lib)
}

pub(crate) fn collect_default_search_paths_with_pinned<F, R>(
    mut var_lookup: F,
    mut read_dir: R,
    pinned_lean_lib: Option<PathBuf>,
) -> Vec<PathBuf>
where
    F: for<'a> FnMut(&'a str) -> Option<std::ffi::OsString>,
    R: for<'a> FnMut(&'a Path) -> std::io::Result<std::fs::ReadDir>,
{
    let mut paths = Vec::new();
    let mut seen = HashSet::new();

    if let Some(val) = var_lookup("MATHLIB_PATH") {
        for path in env::split_paths(&val) {
            if path.exists() && seen.insert(path.clone()) {
                paths.push(path);
            }
        }
    }

    if let Some(val) = var_lookup("LEAN_PATH") {
        for path in env::split_paths(&val) {
            if path.exists() && seen.insert(path.clone()) {
                paths.push(path);
            }
        }
    }

    // LEAN_PACKAGES_PATH: colon-separated list of lake project roots.
    // For each root, discover build/lib and .lake/packages/*/build/lib.
    // This enables external packages like TorchLean to be found without
    // requiring the user to manually set LEAN_PATH.
    if let Some(val) = var_lookup("LEAN_PACKAGES_PATH") {
        for project_root in env::split_paths(&val) {
            if !project_root.exists() {
                continue;
            }
            for lib_path in discover_lake_package_paths(&project_root, &mut read_dir) {
                if seen.insert(lib_path.clone()) {
                    paths.push(lib_path);
                }
            }
        }
    }

    // The checkout's exact `lean-toolchain` pin is the only implicit stdlib
    // path, below the explicit caller paths. No other installed toolchain is
    // searched (R38, R81): until 2026-10-17 every `~/.elan/toolchains/*lean4*`
    // library followed it, first match winning, so 290 module paths of a
    // v4.30.0-rc2 closure resolved into v4.28.0, v4.32.1 or v4.33.1, among
    // them `Init.Data.Float.Model`, which pinned `lean` says does not exist.
    if let Some(lib_path) = pinned_lean_lib {
        if lib_path.exists() && seen.insert(lib_path.clone()) {
            paths.push(lib_path);
        }
    }

    paths
}

#[cfg(test)]
pub(crate) fn collect_default_search_paths<F, R>(var_lookup: F, read_dir: R) -> Vec<PathBuf>
where
    F: for<'a> FnMut(&'a str) -> Option<std::ffi::OsString>,
    R: for<'a> FnMut(&'a Path) -> std::io::Result<std::fs::ReadDir>,
{
    collect_default_search_paths_with_pinned(var_lookup, read_dir, None)
}

pub fn toolchain_versions_from_search_paths(paths: &[PathBuf]) -> Vec<String> {
    let mut versions = Vec::new();
    let mut seen = HashSet::new();

    for path in paths {
        let Some(version) = toolchain_version_from_search_path(path) else {
            continue;
        };

        if seen.insert(version.clone()) {
            versions.push(version);
        }
    }

    versions
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ActiveStdlibToolchain {
    Versioned { path: PathBuf, version: String },
    UnversionedPath(PathBuf),
}

pub fn active_stdlib_toolchain(paths: &[PathBuf]) -> Option<ActiveStdlibToolchain> {
    let path = paths
        .iter()
        .find(|path| is_stdlib_search_path(path))?
        .clone();
    Some(match toolchain_version_from_search_path(&path) {
        Some(version) => ActiveStdlibToolchain::Versioned { path, version },
        None => ActiveStdlibToolchain::UnversionedPath(path),
    })
}

pub fn alias_resolvable_toolchain_versions(paths: &[PathBuf]) -> Option<Vec<String>> {
    match active_stdlib_toolchain(paths) {
        Some(ActiveStdlibToolchain::Versioned { version, .. }) => Some(vec![version]),
        Some(ActiveStdlibToolchain::UnversionedPath(_)) | None => None,
    }
}

/// Discover likely search paths for Lean .olean files.
///
/// Priority order:
/// 1. `MATHLIB_PATH` environment variable entries (if set)
/// 2. `LEAN_PATH` environment variable entries (first match wins)
/// 3. `LEAN_PACKAGES_PATH` lake project roots (discovers `build/lib` and
///    `.lake/packages/*/build/lib` under each root)
/// 4. The exact Lean stdlib named by this checkout's `lean-toolchain`, and
///    no other installed toolchain (R38, R81)
///
/// # REQUIRES
/// - Environment variables may be unset; function must handle missing vars.
///
/// # ENSURES
/// - Returns a de-duplicated list of existing paths.
/// - Order preserves priority: `MATHLIB_PATH`, then `LEAN_PATH`, then packages,
///   then the repository pin.
pub fn default_search_paths() -> Vec<PathBuf> {
    collect_default_search_paths_with_pinned(
        |key: &str| env::var_os(key),
        |path: &Path| std::fs::read_dir(path),
        crate::pinned_lean_lib_path(),
    )
}

pub fn default_toolchain_versions() -> Vec<String> {
    alias_resolvable_toolchain_versions(&default_search_paths()).unwrap_or_default()
}

fn version_from_toolchain_dir(name: &str) -> Option<String> {
    if !name.contains("lean4") {
        return None;
    }

    let version = name.rsplit("---").next()?;
    if version.is_empty() {
        return None;
    }

    Some(version.to_string())
}

fn toolchain_version_from_search_path(path: &Path) -> Option<String> {
    let toolchain_dir = path
        .parent()
        .and_then(Path::parent)
        .and_then(Path::file_name)
        .and_then(|name| name.to_str())?;
    version_from_toolchain_dir(toolchain_dir)
}

fn is_stdlib_search_path(path: &Path) -> bool {
    path.join("Init/Prelude.olean").exists() || path.join("Init/Core.olean").exists()
}

/// Read-only probe: return the resolved `.olean` path for `module` if a prebuilt
/// artifact for it exists on `search_paths`, else `None`.
///
/// Unlike [`load_module_with_deps`], this does **not** parse or load anything —
/// it only checks the filesystem. Front-ends use it to decide whether to load a
/// module's compiled artifact instead of recursively elaborating its source
/// (Lean's actual import model: the current file elaborates from source, and its
/// imports are loaded from prebuilt `.olean`s rather than re-elaborated).
#[must_use]
pub fn find_module_olean(module: &str, search_paths: &[PathBuf]) -> Option<PathBuf> {
    resolve_module_path(module, search_paths).ok()
}

pub(super) fn resolve_module_path(
    module: &str,
    search_paths: &[PathBuf],
) -> Result<PathBuf, ImportError> {
    // A name that cannot be mapped to a relative path is malformed, not
    // missing: report it as such instead of a (misleading) empty search.
    let rel = module_name_to_rel_path(module).ok_or_else(|| ImportError::UnsupportedModule {
        module: module.to_string(),
        reason: "module name is empty or contains empty `.`-separated components, so it \
                 cannot be mapped to an .olean path"
            .to_string(),
    })?;

    let mut tried = Vec::new();
    for base in search_paths {
        let candidate = base.join(&rel);
        tried.push(candidate.clone());
        if candidate.exists() {
            return Ok(candidate);
        }
    }

    Err(ImportError::ModuleNotFound {
        module: module.to_string(),
        searched: tried,
    })
}

pub(crate) fn module_name_from_path(path: &Path) -> Option<String> {
    let mut components: Vec<String> = path
        .with_extension("")
        .components()
        .filter_map(|c| match c {
            std::path::Component::Normal(s) => {
                let s = s.to_string_lossy();
                if s.is_empty() {
                    None
                } else {
                    Some(s.to_string())
                }
            }
            _ => None,
        })
        .collect();

    if let Some(pos) = components
        .iter()
        .rposition(|c| c == "lean" || c == "library" || c == "lib")
    {
        components = components.split_off(pos + 1);
    }

    if components.is_empty() {
        return None;
    }

    Some(components.join("."))
}

/// Builder for constructing search paths for .olean module resolution.
///
/// Provides a programmatic API for specifying search paths, complementing
/// the environment-variable-based `default_search_paths()`. This is the
/// recommended way for downstream tools (like gamma-crown) to configure
/// .olean loading for external packages (like TorchLean).
///
/// # Example
///
/// ```rust
/// use clean_olean::SearchPathBuilder;
///
/// let paths = SearchPathBuilder::new()
///     .with_defaults()
///     .add_package_root("/path/to/TorchLean")
///     .add_lib_path("/path/to/TorchLean/build/lib")
///     .build();
/// ```
pub struct SearchPathBuilder {
    paths: Vec<PathBuf>,
    seen: HashSet<PathBuf>,
}

impl SearchPathBuilder {
    /// Create an empty search path builder.
    #[must_use]
    pub fn new() -> Self {
        Self {
            paths: Vec::new(),
            seen: HashSet::new(),
        }
    }

    /// Add the default search paths (from environment variables and elan toolchains).
    ///
    /// Equivalent to prepending the result of `default_search_paths()`.
    #[must_use]
    pub fn with_defaults(mut self) -> Self {
        for path in default_search_paths() {
            if self.seen.insert(path.clone()) {
                self.paths.push(path);
            }
        }
        self
    }

    /// Add a direct library path containing `.olean` files.
    ///
    /// Use this when you know the exact directory where compiled `.olean` files live,
    /// e.g., `/path/to/TorchLean/build/lib`.
    #[must_use]
    pub fn add_lib_path(mut self, path: impl AsRef<Path>) -> Self {
        let path = path.as_ref().to_path_buf();
        if path.exists() && self.seen.insert(path.clone()) {
            self.paths.push(path);
        }
        self
    }

    /// Add a lake project root and discover its build output paths.
    ///
    /// Scans for:
    /// - `<root>/build/lib/` (project's own build output)
    /// - `<root>/.lake/packages/*/build/lib/` (dependency build outputs)
    ///
    /// This is the recommended way to add external Lean packages like TorchLean.
    #[must_use]
    pub fn add_package_root(mut self, root: impl AsRef<Path>) -> Self {
        let root = root.as_ref();
        if !root.exists() {
            return self;
        }
        let discovered = discover_lake_package_paths(root, |p| std::fs::read_dir(p));
        for path in discovered {
            if self.seen.insert(path.clone()) {
                self.paths.push(path);
            }
        }
        self
    }

    /// Build the final search path list.
    ///
    /// Returns a de-duplicated list of paths in priority order.
    #[must_use]
    pub fn build(self) -> Vec<PathBuf> {
        self.paths
    }
}

impl Default for SearchPathBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod find_module_olean_tests {
    use super::find_module_olean;
    use std::fs;
    use tempfile::TempDir;

    #[test]
    fn find_module_olean_returns_path_when_artifact_present() {
        let temp = TempDir::new().expect("tempdir");
        let lib = temp.path();
        // A prebuilt olean laid out the way Lake writes it: `Foo/Bar.olean`.
        fs::create_dir_all(lib.join("Foo")).expect("mkdir");
        let olean = lib.join("Foo").join("Bar.olean");
        fs::write(&olean, b"stub").expect("write olean");

        let found = find_module_olean("Foo.Bar", &[lib.to_path_buf()]);
        assert_eq!(
            found.as_deref(),
            Some(olean.as_path()),
            "an existing Foo/Bar.olean must be discovered for module Foo.Bar",
        );
    }

    #[test]
    fn find_module_olean_returns_none_when_absent() {
        let temp = TempDir::new().expect("tempdir");
        // Empty search dir — no artifact for the module.
        let found = find_module_olean("Foo.Bar", &[temp.path().to_path_buf()]);
        assert!(
            found.is_none(),
            "no .olean on disk for the module must yield None (front-end then \
             falls back to source elaboration)",
        );
    }

    #[test]
    fn find_module_olean_returns_none_for_malformed_module_name() {
        let temp = TempDir::new().expect("tempdir");
        let found = find_module_olean("Foo..Bar", &[temp.path().to_path_buf()]);
        assert!(
            found.is_none(),
            "a module name with an empty `.`-separated component maps to no path",
        );
    }
}
