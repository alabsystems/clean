// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lake workspace management
//!
//! A workspace represents a Lake project with its configuration,
//! manifest, and build state.

use crate::cli::toolchain;
use crate::config::LakeConfig;
use crate::error::{LakeError, LakeResult};
use crate::manifest::{LakeManifest, ManifestPackage};
use clean_kernel::{name::NameInner, Name};
use clean_parser::SurfaceName;
use std::collections::HashMap;
use std::path::{Path, PathBuf};

/// A Lake workspace
#[derive(Debug)]
pub struct Workspace {
    /// Root directory of the workspace
    root: PathBuf,
    /// Lake configuration from lakefile.lean
    config: LakeConfig,
    /// Repo-root lean-toolchain identifier, if present
    toolchain: Option<String>,
    /// Resolved Lean version for the configured toolchain, if available.
    toolchain_version: Option<String>,
    /// Lake manifest from lake-manifest.json (if present)
    manifest: Option<LakeManifest>,
    /// Resolved module paths
    module_paths: HashMap<Name, PathBuf>,
    /// Indexing refusals remain visible; a checked graph/build cannot ignore them.
    module_index_errors: Vec<String>,
    /// Directory that replaces the configured build directory while set.
    ///
    /// Used by check-only builds, which must write their `.olean` files
    /// somewhere (module imports are loaded from disk) without touching the
    /// project's own artifacts. See [`BuildOptions::check_only`].
    ///
    /// [`BuildOptions::check_only`]: crate::BuildOptions::check_only
    build_dir_override: Option<PathBuf>,
}

impl Workspace {
    /// Load a workspace from a directory
    pub fn load(root: &Path) -> LakeResult<Self> {
        let root = root.canonicalize().unwrap_or_else(|_| root.to_path_buf());

        // Load the package configuration, preferring `lakefile.toml` (Lake's TOML
        // form) over `lakefile.lean` when present, then falling back to
        // `lakefile.lean`. This lets Cake/Lake open TOML-configured projects
        // (e.g. modern Mathlib-dependent packages) natively, not just DSL ones.
        let config = LakeConfig::load_from_dir(&root)?;
        let loaded_toolchain = toolchain::load_toolchain(&root)?;
        let (toolchain, toolchain_version) = loaded_toolchain
            .map(|toolchain| (Some(toolchain.identifier), toolchain.resolved_version))
            .unwrap_or((None, None));

        // Load manifest if present
        let manifest_path = root.join("lake-manifest.json");
        let manifest = if manifest_path.exists() {
            Some(LakeManifest::load(&manifest_path)?)
        } else {
            None
        };

        let mut ws = Self {
            root,
            config,
            toolchain,
            toolchain_version,
            manifest,
            module_paths: HashMap::new(),
            module_index_errors: Vec::new(),
            build_dir_override: None,
        };

        // Index modules
        ws.index_modules();

        Ok(ws)
    }

    /// Create a new workspace with minimal configuration
    #[must_use]
    pub fn new(root: &Path, package_name: &str) -> Self {
        let loaded_toolchain = toolchain::load_toolchain(root).ok().flatten();
        let toolchain = loaded_toolchain
            .as_ref()
            .map(|toolchain| toolchain.identifier.clone());
        let toolchain_version = loaded_toolchain.and_then(|toolchain| toolchain.resolved_version);

        Self {
            root: root.to_path_buf(),
            config: LakeConfig {
                package: crate::config::PackageConfig::minimal(package_name),
                libs: vec![],
                exes: vec![],
                tests: vec![],
                scripts: vec![],
                default_targets: vec![],
                diagnostics: vec![],
            },
            toolchain,
            toolchain_version,
            manifest: None,
            module_paths: HashMap::new(),
            module_index_errors: Vec::new(),
            build_dir_override: None,
        }
    }

    /// Create a workspace from a pre-parsed configuration
    #[must_use]
    pub fn from_config(root: &Path, config: LakeConfig) -> Self {
        let root = root.canonicalize().unwrap_or_else(|_| root.to_path_buf());
        let loaded_toolchain = toolchain::load_toolchain(&root).ok().flatten();
        let toolchain = loaded_toolchain
            .as_ref()
            .map(|toolchain| toolchain.identifier.clone());
        let toolchain_version = loaded_toolchain.and_then(|toolchain| toolchain.resolved_version);

        // Load manifest if present
        let manifest_path = root.join("lake-manifest.json");
        let manifest = if manifest_path.exists() {
            match LakeManifest::load(&manifest_path) {
                Ok(m) => Some(m),
                Err(e) => {
                    // Surface manifest-parse failures instead of swallowing
                    // them with `.ok()`. Silent parse failures hid audit
                    // item 1 (real Lean 4 manifests use a string-form
                    // `version`) and made the subsequent
                    // `validate_dependencies` failure look like a missing
                    // file when the file was actually present but
                    // unparseable.
                    eprintln!("Warning: failed to load {}: {e}", manifest_path.display());
                    None
                }
            }
        } else {
            None
        };

        let mut ws = Self {
            root,
            config,
            toolchain,
            toolchain_version,
            manifest,
            module_paths: HashMap::new(),
            module_index_errors: Vec::new(),
            build_dir_override: None,
        };

        // Index modules (no errors for new projects with no source files)
        ws.index_modules();

        ws
    }

    /// Get the workspace root directory
    #[must_use]
    pub fn root(&self) -> &Path {
        &self.root
    }

    /// Get the lake configuration
    #[must_use]
    pub fn config(&self) -> &LakeConfig {
        &self.config
    }

    /// Get the repo-root `lean-toolchain` identifier, if present.
    #[must_use]
    pub fn toolchain(&self) -> Option<&str> {
        self.toolchain.as_deref()
    }

    /// Get the resolved toolchain version from `lean-toolchain`, if present.
    #[must_use]
    pub(crate) fn toolchain_version(&self) -> Option<&str> {
        self.toolchain_version.as_deref()
    }

    /// Get the manifest (if present)
    #[must_use]
    pub(crate) fn manifest(&self) -> Option<&LakeManifest> {
        self.manifest.as_ref()
    }

    /// Get the source directory
    #[must_use]
    pub fn src_dir(&self) -> PathBuf {
        self.root.join(self.config.src_dir())
    }

    /// Get all configured source directories for package and target roots.
    fn source_dirs(&self) -> Vec<PathBuf> {
        let mut dirs = Vec::new();
        self.push_source_dir(&mut dirs, self.config.src_dir());

        for lib in &self.config.libs {
            if let Some(src_dir) = &lib.src_dir {
                self.push_source_dir(&mut dirs, src_dir.clone());
            }
        }
        for exe in &self.config.exes {
            if let Some(src_dir) = &exe.src_dir {
                self.push_source_dir(&mut dirs, src_dir.clone());
            }
        }
        for test in &self.config.tests {
            if let Some(src_dir) = &test.src_dir {
                self.push_source_dir(&mut dirs, src_dir.clone());
            }
        }

        dirs
    }

    fn push_source_dir(&self, dirs: &mut Vec<PathBuf>, src_dir: PathBuf) {
        let dir = self.root.join(src_dir);
        if !dirs.iter().any(|existing| existing == &dir) {
            dirs.push(dir);
        }
    }

    /// Get the build directory
    #[must_use]
    pub fn build_dir(&self) -> PathBuf {
        self.build_dir_override
            .clone()
            .unwrap_or_else(|| self.root.join(self.config.build_dir()))
    }

    /// Redirect every build output of this workspace to `dir`, or restore the
    /// configured directory with `None`.
    ///
    /// Everything derived from [`Self::build_dir`] moves with it — the lib
    /// directory, each module's `.olean` triple, the rebuild check and
    /// `LEAN_PATH` — which is what lets a check-only build write the imports
    /// it needs without touching the project. See [`BuildOptions::check_only`].
    ///
    /// [`BuildOptions::check_only`]: crate::BuildOptions::check_only
    pub(crate) fn set_build_dir_override(&mut self, dir: Option<PathBuf>) {
        self.build_dir_override = dir;
    }

    /// Get the lib directory (for .olean files)
    #[must_use]
    pub fn lib_dir(&self) -> PathBuf {
        self.build_dir().join("lib")
    }

    /// Get the packages directory
    #[must_use]
    pub(crate) fn packages_dir(&self) -> PathBuf {
        self.manifest.as_ref().map_or_else(
            || self.root.join(".lake/packages"),
            |m| self.root.join(&m.packages_dir),
        )
    }

    /// Index all module files in the workspace
    fn index_modules(&mut self) {
        self.module_paths.clear();
        self.module_index_errors.clear();

        for src_dir in self.source_dirs() {
            if !src_dir.exists() {
                continue;
            }

            // Walk the source directory, pruning `.lake/`.
            //
            // `.lake/` is Lake's build and dependency directory: `lake update` /
            // `lake exe cache get` populate `.lake/packages/<dep>` with entire
            // upstream checkouts. Those are DEPENDENCIES, not this project's
            // modules. Without this prune, a workspace with a Mathlib checkout
            // present indexes the checkout's 9,071 `.lean` files under names
            // like `.lake.packages.mathlib.Mathlib.*` and then tries to build
            // them, so the project's own modules never run.
            //
            // `filter_entry` prunes rather than filters: a rejected directory is
            // never descended into, so the cost is not paid at all. The
            // `depth() == 0` exemption keeps an explicitly-configured source dir
            // that itself lives under `.lake` (a dependency package built as a
            // workspace member) working — only nested `.lake` components prune.
            for entry in walkdir::WalkDir::new(&src_dir)
                .follow_links(true)
                .into_iter()
                .filter_entry(|e| e.depth() == 0 || e.file_name() != ".lake")
            {
                let entry = match entry {
                    Ok(entry) => entry,
                    Err(error) => {
                        self.module_index_errors.push(error.to_string());
                        continue;
                    }
                };
                self.index_module_path(&src_dir, entry.path());
            }
        }
    }

    /// Process one path delivered by the workspace walker. Keeping the exact
    /// path boundary separate also lets non-UTF8 refusal be tested on filesystems
    /// that reject such directory entries before the walker can see them.
    fn index_module_path(&mut self, src_dir: &Path, path: &Path) {
        if path.file_name().is_some_and(|name| name == "lakefile.lean") {
            return;
        }
        if path
            .extension()
            .is_some_and(|extension| extension == "lean")
        {
            if let Ok(relative) = path.strip_prefix(src_dir) {
                match Self::path_to_module_name(relative) {
                    Ok(module_name) => {
                        self.module_paths
                            .entry(module_name)
                            .or_insert_with(|| path.to_path_buf());
                    }
                    Err(error) => self
                        .module_index_errors
                        .push(format!("{}: {error}", path.display())),
                }
            }
        }
    }

    /// Convert a relative path to a module name
    fn path_to_module_name(path: &Path) -> LakeResult<Name> {
        let mut name = Name::anon();
        for component in path.with_extension("").components() {
            let std::path::Component::Normal(text) = component else {
                return Err(LakeError::InvalidConfig(
                    "module path must be relative normal components".into(),
                ));
            };
            let text = text.to_str().ok_or_else(|| {
                LakeError::InvalidConfig("module path has a non-UTF8 component".into())
            })?;
            name = name.str(text);
        }
        Self::module_name_path(&name, "lean")?;
        Ok(name)
    }

    /// Convert a module name to a relative path.
    ///
    /// TEST-ONLY: the five call sites are all in the `#[cfg(test)]` child
    /// `workspace_tests.rs`, so the lib unit correctly sees it as dead. Gated
    /// rather than deleted -- deleting it breaks those tests, and leaving it
    /// ungated reds `clippy --workspace --all-targets -- -D warnings`.
    #[cfg(test)]
    fn module_name_to_path(module_name: &str) -> LakeResult<PathBuf> {
        Self::module_name_path(&Self::parse_module_name(module_name)?, "lean")
    }

    pub(crate) fn parse_module_name(spelling: &str) -> LakeResult<Name> {
        let name = clean_parser::parse_name(spelling)
            .map_err(|error| LakeError::InvalidConfig(format!("invalid module name: {error}")))?;
        if name.is_relative_constructor() {
            return Err(LakeError::InvalidConfig(
                "relative constructor is not a module name".into(),
            ));
        }
        Ok(name.into_name())
    }

    fn module_source_spelling(name: &Name) -> LakeResult<String> {
        let spelling = SurfaceName::from_name(name.clone())
            .source_spelling()
            .ok_or_else(|| {
                LakeError::InvalidConfig("module has no source identifier spelling".into())
            })?;
        if Self::parse_module_name(&spelling)? != *name {
            return Err(LakeError::InvalidConfig(
                "module source spelling changes structural identity".into(),
            ));
        }
        Ok(spelling)
    }

    /// Filesystem components are Str only. Append the suffix to the leaf:
    /// replacing an extension would collapse `«A.B»` into `A.lean`.
    fn module_name_path(name: &Name, suffix: &str) -> LakeResult<PathBuf> {
        let mut parts = Vec::new();
        let mut current = name;
        loop {
            match current.inner() {
                NameInner::Anon => break,
                NameInner::Str(parent, text) => {
                    if text.is_empty()
                        || matches!(text.as_ref(), "." | "..")
                        || text.contains(['/', '\\', '\0'])
                    {
                        return Err(LakeError::InvalidConfig(
                            "module name has an invalid filesystem component".into(),
                        ));
                    }
                    parts.push(text.as_ref());
                    current = parent;
                }
                NameInner::Num(..) => {
                    return Err(LakeError::InvalidConfig(
                        "numeric Name component has no module source path".into(),
                    ))
                }
            }
        }
        if parts.is_empty() {
            return Err(LakeError::InvalidConfig(
                "anonymous module name has no source path".into(),
            ));
        }
        let mut path = PathBuf::new();
        for part in parts.into_iter().rev() {
            path.push(part);
        }
        let mut bytes = path.into_os_string();
        bytes.push(format!(".{suffix}"));
        Ok(PathBuf::from(bytes))
    }

    /// Find a module's source file
    #[must_use]
    pub fn find_module(&self, module_name: &str) -> Option<PathBuf> {
        self.find_module_name(&Self::parse_module_name(module_name).ok()?)
    }

    /// Resolve the exact typed module name without display parsing.
    #[must_use]
    pub fn find_module_name(&self, module_name: &Name) -> Option<PathBuf> {
        let rel_path = Self::module_name_path(module_name, "lean").ok()?;
        // Check indexed modules first
        if let Some(path) = self.module_paths.get(module_name) {
            return Some(path.clone());
        }

        // Try to construct path
        for src_dir in self.source_dirs() {
            let src_path = src_dir.join(&rel_path);
            if src_path.exists() {
                return Some(src_path);
            }
        }

        // Check packages
        for pkg_dir in self.package_dirs() {
            let pkg_src = pkg_dir.join(&rel_path);
            if pkg_src.exists() {
                return Some(pkg_src);
            }
        }

        None
    }

    /// The directory of the DEPENDENCY package [`Self::find_module_name`]
    /// resolves `module_name` into, or `None` when it resolves into this
    /// workspace's own package (or nowhere). Same search order, so the
    /// package named is the one whose source is elaborated.
    #[must_use]
    pub(crate) fn module_package_dir(&self, module_name: &Name) -> Option<PathBuf> {
        if self.module_paths.contains_key(module_name) {
            return None;
        }
        let rel_path = Self::module_name_path(module_name, "lean").ok()?;
        if self
            .source_dirs()
            .iter()
            .any(|dir| dir.join(&rel_path).exists())
        {
            return None;
        }
        self.package_dirs()
            .into_iter()
            .find(|dir| dir.join(&rel_path).exists())
    }

    /// Get the .olean file path for a module
    pub fn olean_path(&self, module_name: &str) -> LakeResult<PathBuf> {
        self.olean_path_name(&Self::parse_module_name(module_name)?)
    }

    /// Checked output path for an exact typed module identity.
    pub(crate) fn olean_path_name(&self, module_name: &Name) -> LakeResult<PathBuf> {
        Ok(self
            .lib_dir()
            .join(Self::module_name_path(module_name, "olean")?))
    }

    /// Get the .olean.server file path for a module.
    ///
    /// This corresponds to `OLeanLevel::Server` and contains LSP server metadata.
    /// The file is only loaded if the base .olean exists (server-gates-private semantics).
    pub fn olean_server_path(&self, module_name: &str) -> LakeResult<PathBuf> {
        Ok(self.olean_path(module_name)?.with_extension("olean.server"))
    }

    /// Get the .olean.private file path for a module.
    ///
    /// This corresponds to `OLeanLevel::Private` and contains private implementation details.
    /// The file is only loaded if both the base .olean and .olean.server exist.
    pub fn olean_private_path(&self, module_name: &str) -> LakeResult<PathBuf> {
        Ok(self
            .olean_path(module_name)?
            .with_extension("olean.private"))
    }

    /// Platform path-list separator (`;` on Windows, `:` elsewhere).
    #[must_use]
    pub(crate) fn lean_path_separator() -> &'static str {
        if cfg!(windows) {
            ";"
        } else {
            ":"
        }
    }

    /// The `LEAN_PATH` search list: this workspace's `.olean` lib directory
    /// first, then every fetched/path dependency package directory.
    #[must_use]
    pub(crate) fn lean_path(&self) -> String {
        let mut entries: Vec<PathBuf> = vec![self.lib_dir()];
        entries.extend(self.package_dirs());
        entries
            .iter()
            .map(|p| p.display().to_string())
            .collect::<Vec<_>>()
            .join(Self::lean_path_separator())
    }

    /// The resolved Lake environment as `(key, value)` pairs.
    ///
    /// This is the single definition of what `lake env` means, shared by the
    /// reporting path and by the child-process path. They used to disagree:
    /// the library printed `LEAN_PATH=…` while the CLI spawned `lake env <cmd>`
    /// with nothing but inherited environment, so a tool run that way could
    /// not resolve a single import. (The CLI refuses a Lean toolchain program
    /// there; see `clean-cli`'s `cmd_lake/env_guard.rs`.)
    #[must_use]
    pub fn env_pairs(&self) -> Vec<(String, String)> {
        vec![
            (
                "LAKE_PACKAGE".to_string(),
                self.config().package.name.clone(),
            ),
            ("LAKE_ROOT".to_string(), self.root().display().to_string()),
            ("LEAN_PATH".to_string(), self.lean_path()),
            (
                "LEAN_SRC_PATH".to_string(),
                self.src_dir().display().to_string(),
            ),
            (
                "LEAN_TOOLCHAIN".to_string(),
                self.toolchain_version()
                    .or_else(|| self.toolchain())
                    .unwrap_or_default()
                    .to_string(),
            ),
        ]
    }

    /// Get all package directories
    #[must_use]
    pub fn package_dirs(&self) -> Vec<PathBuf> {
        let mut dirs = vec![];

        if let Some(manifest) = &self.manifest {
            let pkg_dir = self.packages_dir();
            for pkg in &manifest.packages {
                match pkg {
                    ManifestPackage::Git(pkg) => dirs.push(pkg_dir.join(&pkg.name)),
                    ManifestPackage::Path(pkg) => dirs.push(self.root.join(&pkg.path)),
                }
            }
        }

        dirs
    }

    /// Get all modules in a library.
    ///
    /// When the lib declares explicit `globs`, the lib's modules are exactly
    /// the indexed modules matching any glob (union), mirroring Lake, where a
    /// lib's module set is determined by its globs. When `globs` is empty the
    /// historical root-based selection is preserved unchanged: each root module
    /// plus every module whose name has that root as a prefix.
    pub fn lib_modules(&self, lib_name: &str) -> LakeResult<Vec<String>> {
        self.lib_module_names(lib_name)?
            .iter()
            .map(Self::module_source_spelling)
            .collect()
    }

    /// Library selection compares typed component prefixes, never rendered dots.
    pub(crate) fn lib_module_names(&self, lib_name: &str) -> LakeResult<Vec<Name>> {
        self.validate_module_index()?;
        let Some(lib) = self.config.libs.iter().find(|l| l.name == lib_name) else {
            return Ok(Vec::new());
        };

        if !lib.globs.is_empty() {
            let mut globs = Vec::new();
            for spec in &lib.globs {
                let glob = crate::glob::ModuleGlob::parse(spec).ok_or_else(|| {
                    LakeError::InvalidConfig(format!("invalid module glob: {spec}"))
                })?;
                globs.push((Self::parse_module_name(&glob.module)?, glob.kind));
            }
            let mut modules = Vec::new();
            for name in self.all_module_names() {
                if globs.iter().any(|(root, kind)| match kind {
                    crate::glob::GlobKind::One => &name == root,
                    crate::glob::GlobKind::AndSubmodules => Self::name_is_under(&name, root),
                    crate::glob::GlobKind::Submodules => {
                        &name != root && Self::name_is_under(&name, root)
                    }
                }) {
                    modules.push(name);
                }
            }
            return Ok(modules);
        }

        // A module prefix is a component prefix: Foo is not the parent of FooBar
        // or of the single filesystem component «Foo.Bar».
        let roots = lib.root_modules();
        let mut modules = vec![];
        for root in roots {
            let root = Self::parse_module_name(&root)?;
            // Add the root module
            modules.push(root.clone());

            // Add all submodules
            for name in self.module_paths.keys() {
                if Self::name_is_under(name, &root) && name != &root {
                    modules.push(name.clone());
                }
            }
        }

        modules.sort();
        Ok(modules)
    }

    pub(crate) fn name_is_under(name: &Name, root: &Name) -> bool {
        let mut current = name;
        loop {
            if current == root {
                return true;
            }
            match current.inner() {
                NameInner::Anon => return false,
                NameInner::Str(parent, _) | NameInner::Num(parent, _) => current = parent,
            }
        }
    }

    /// Every filesystem entry that could not be indexed is retained explicitly.
    #[must_use]
    pub fn module_index_errors(&self) -> &[String] {
        &self.module_index_errors
    }

    /// Refuse a partial index before using the typed module population.
    pub fn validate_module_index(&self) -> LakeResult<()> {
        if self.module_index_errors.is_empty() {
            Ok(())
        } else {
            Err(LakeError::InvalidConfig(format!(
                "module indexing refused: {}",
                self.module_index_errors.join("; ")
            )))
        }
    }

    /// Exact indexed module identities, including names without a source spelling.
    /// Consumers needing a complete readable graph must also check indexing errors.
    #[must_use]
    pub fn all_module_names(&self) -> Vec<Name> {
        let mut names: Vec<_> = self.module_paths.keys().cloned().collect();
        names.sort();
        names
    }

    /// Get all modules that need to be built
    pub fn all_modules(&self) -> LakeResult<Vec<String>> {
        self.validate_module_index()?;
        self.all_module_names()
            .iter()
            .map(Self::module_source_spelling)
            .collect()
    }

    /// Parse direct source imports for every indexed module.
    ///
    /// Unlike [`BuildContext`](crate::BuildContext), this keeps stdlib and
    /// external package imports because callers use it for source provenance
    /// and trust audits, not just local build scheduling.
    pub fn import_graph(&self) -> LakeResult<HashMap<String, Vec<String>>> {
        self.import_graph_names()?
            .into_iter()
            .map(|(module, imports)| {
                Ok((
                    Self::module_source_spelling(&module)?,
                    imports
                        .iter()
                        .map(Self::module_source_spelling)
                        .collect::<LakeResult<_>>()?,
                ))
            })
            .collect()
    }

    /// Source-order direct import names from the parser's typed header scanner.
    /// This graph preserves duplicate source imports; it is not a build closure
    /// or a completeness attestation for unsupported header syntax.
    pub fn import_graph_names(&self) -> LakeResult<HashMap<Name, Vec<Name>>> {
        self.validate_module_index()?;
        let mut graph = HashMap::new();

        for module in self.all_module_names() {
            let src_path = self
                .find_module_name(&module)
                .ok_or_else(|| LakeError::ModuleNotFound(module.to_string()))?;
            let content = std::fs::read_to_string(src_path)?;
            graph.insert(
                module,
                clean_parser::notation_seed::scan_imports(&content)
                    .into_iter()
                    .map(SurfaceName::into_name)
                    .collect(),
            );
        }

        Ok(graph)
    }

    /// Check if a module needs rebuilding
    pub fn needs_rebuild(&self, module_name: &str) -> LakeResult<bool> {
        self.validate_module_index()?;
        let olean = self.olean_path(module_name)?;
        let Some(src) = self.find_module(module_name) else {
            return Err(LakeError::ModuleNotFound(module_name.into()));
        };

        // Rebuild if .olean doesn't exist
        if !olean.exists() {
            return Ok(true);
        }

        // Rebuild if source is newer
        let src_time = std::fs::metadata(&src).and_then(|m| m.modified()).ok();
        let olean_time = std::fs::metadata(&olean).and_then(|m| m.modified()).ok();

        Ok(match (src_time, olean_time) {
            (Some(src_t), Some(olean_t)) => src_t > olean_t,
            _ => true,
        })
    }

    /// Create workspace directories
    pub(crate) fn create_dirs(&self) -> LakeResult<()> {
        std::fs::create_dir_all(self.build_dir())?;
        std::fs::create_dir_all(self.lib_dir())?;
        Ok(())
    }

    /// Validate that declared dependencies are satisfied by the manifest
    pub(crate) fn validate_dependencies(&self) -> LakeResult<()> {
        if self.config.package.dependencies.is_empty() {
            return Ok(());
        }

        if let Some(manifest) = &self.manifest {
            self.config.validate_manifest(manifest)
        } else {
            Err(LakeError::ManifestMissingForDependencies)
        }
    }
}

#[cfg(test)]
#[path = "workspace_tests.rs"]
mod tests;
