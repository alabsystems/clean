// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lake workspace management
//!
//! A workspace represents a Lake project with its configuration,
//! manifest, and build state.

use crate::cli::toolchain;
use crate::config::{LakeConfig, LeanLib};
use crate::error::{LakeError, LakeResult};
use crate::manifest::{LakeManifest, ManifestPackage};
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
    module_paths: HashMap<String, PathBuf>,
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
            },
            toolchain,
            toolchain_version,
            manifest: None,
            module_paths: HashMap::new(),
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
    pub fn toolchain_version(&self) -> Option<&str> {
        self.toolchain_version.as_deref()
    }

    /// Get the manifest (if present)
    #[must_use]
    pub fn manifest(&self) -> Option<&LakeManifest> {
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
        self.root.join(self.config.build_dir())
    }

    /// Get the lib directory (for .olean files)
    #[must_use]
    pub fn lib_dir(&self) -> PathBuf {
        self.build_dir().join("lib")
    }

    /// Get the packages directory
    #[must_use]
    pub fn packages_dir(&self) -> PathBuf {
        self.manifest.as_ref().map_or_else(
            || self.root.join(".lake/packages"),
            |m| self.root.join(&m.packages_dir),
        )
    }

    /// Index all module files in the workspace
    fn index_modules(&mut self) {
        self.module_paths.clear();

        for src_dir in self.source_dirs() {
            if !src_dir.exists() {
                continue;
            }

            // Walk the source directory
            for entry in walkdir::WalkDir::new(&src_dir)
                .follow_links(true)
                .into_iter()
                .filter_map(Result::ok)
            {
                let path = entry.path();
                if path.file_name().is_some_and(|name| name == "lakefile.lean") {
                    continue;
                }
                if path.extension().is_some_and(|e| e == "lean") {
                    // Convert path to module name
                    if let Ok(rel_path) = path.strip_prefix(&src_dir) {
                        let module_name = Self::path_to_module_name(rel_path);
                        self.module_paths
                            .entry(module_name)
                            .or_insert_with(|| path.to_path_buf());
                    }
                }
            }
        }
    }

    /// Convert a relative path to a module name
    fn path_to_module_name(path: &Path) -> String {
        let parts: Vec<_> = path
            .with_extension("")
            .components()
            .filter_map(|c| c.as_os_str().to_str())
            .map(String::from)
            .collect();

        parts.join(".")
    }

    /// Convert a module name to a relative path
    fn module_name_to_path(module_name: &str) -> PathBuf {
        let parts: Vec<&str> = module_name.split('.').collect();
        let mut path = PathBuf::new();
        for part in parts {
            path.push(part);
        }
        path.with_extension("lean")
    }

    /// Find a module's source file
    #[must_use]
    pub fn find_module(&self, module_name: &str) -> Option<PathBuf> {
        // Check indexed modules first
        if let Some(path) = self.module_paths.get(module_name) {
            return Some(path.clone());
        }

        // Try to construct path
        let rel_path = Self::module_name_to_path(module_name);
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

    /// Get the .olean file path for a module
    #[must_use]
    pub fn olean_path(&self, module_name: &str) -> PathBuf {
        let rel_path = Self::module_name_to_path(module_name).with_extension("olean");
        self.lib_dir().join(rel_path)
    }

    /// Get the .olean.server file path for a module.
    ///
    /// This corresponds to `OLeanLevel::Server` and contains LSP server metadata.
    /// The file is only loaded if the base .olean exists (server-gates-private semantics).
    #[must_use]
    pub fn olean_server_path(&self, module_name: &str) -> PathBuf {
        self.olean_path(module_name).with_extension("olean.server")
    }

    /// Get the .olean.private file path for a module.
    ///
    /// This corresponds to `OLeanLevel::Private` and contains private implementation details.
    /// The file is only loaded if both the base .olean and .olean.server exist.
    #[must_use]
    pub fn olean_private_path(&self, module_name: &str) -> PathBuf {
        self.olean_path(module_name).with_extension("olean.private")
    }

    /// Get the .ilean file path for a module
    #[must_use]
    pub fn ilean_path(&self, module_name: &str) -> PathBuf {
        let rel_path = Self::module_name_to_path(module_name).with_extension("ilean");
        self.lib_dir().join(rel_path)
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
    pub fn lib_modules(&self, lib_name: &str) -> Vec<String> {
        let Some(lib) = self.config.libs.iter().find(|l| l.name == lib_name) else {
            return Vec::new();
        };

        if !lib.globs.is_empty() {
            let globs = crate::glob::parse_globs(&lib.globs);
            let mut modules: Vec<String> = self
                .module_paths
                .keys()
                .filter(|name| globs.iter().any(|g| g.matches(name)))
                .cloned()
                .collect();
            modules.sort();
            return modules;
        }

        // No explicit globs: preserve the historical root-prefix behavior
        // exactly (the default glob set in Lake is each root as
        // `.andSubmodules`, but the legacy prefix match is retained verbatim
        // so build outputs for glob-free libs are unchanged).
        let roots = lib.root_modules();
        let mut modules = vec![];
        for root in roots {
            // Add the root module
            modules.push(root.clone());

            // Add all submodules
            for name in self.module_paths.keys() {
                if name.starts_with(&root) && name != &root {
                    modules.push(name.clone());
                }
            }
        }

        modules
    }

    /// Get all modules that need to be built
    #[must_use]
    pub fn all_modules(&self) -> Vec<String> {
        self.module_paths.keys().cloned().collect()
    }

    /// Parse direct source imports for every indexed module.
    ///
    /// Unlike [`BuildContext`](crate::BuildContext), this keeps stdlib and
    /// external package imports because callers use it for source provenance
    /// and trust audits, not just local build scheduling.
    pub fn import_graph(&self) -> LakeResult<HashMap<String, Vec<String>>> {
        let mut graph = HashMap::new();

        for module in self.all_modules() {
            let src_path = self
                .find_module(&module)
                .ok_or_else(|| LakeError::ModuleNotFound(module.clone()))?;
            let content = std::fs::read_to_string(src_path)?;
            graph.insert(module, Self::imports_from_source(&content));
        }

        Ok(graph)
    }

    /// Extract the import statements declared in a Lean source string.
    ///
    /// Handles line and nested block comments, string literals, and the
    /// `public`/`private import` qualifiers so commented-out or quoted imports
    /// are not picked up.
    pub(crate) fn imports_from_source(content: &str) -> Vec<String> {
        let mut imports = Vec::new();
        let mut block_comment_depth = 0usize;
        let mut in_string = false;

        for line in content.lines() {
            let code =
                Self::strip_non_code_from_line(line, &mut block_comment_depth, &mut in_string);
            let tokens = code.split_whitespace().collect::<Vec<_>>();
            let start = match tokens.as_slice() {
                ["import", ..] => 1,
                ["public", "import", ..] | ["private", "import", ..] => 2,
                _ => continue,
            };

            for token in &tokens[start..] {
                if matches!(*token, "all" | "public" | "private") {
                    continue;
                }
                if let Some(module) = Self::normalize_lean_name_token(token) {
                    if !imports.contains(&module) {
                        imports.push(module);
                    }
                }
            }
        }

        imports
    }

    fn normalize_lean_name_token(token: &str) -> Option<String> {
        let token = token.trim_matches(|ch: char| {
            !(ch.is_alphanumeric() || matches!(ch, '_' | '.' | '\'' | '«' | '»'))
        });
        (!token.is_empty()).then(|| token.to_string())
    }

    fn strip_non_code_from_line(
        line: &str,
        block_comment_depth: &mut usize,
        in_string: &mut bool,
    ) -> String {
        let mut out = String::new();
        let mut i = 0usize;
        let bytes = line.as_bytes();

        while i < line.len() {
            if *block_comment_depth > 0 {
                if bytes[i..].starts_with(b"/-") {
                    *block_comment_depth += 1;
                    i += 2;
                } else if bytes[i..].starts_with(b"-/") {
                    *block_comment_depth -= 1;
                    i += 2;
                } else {
                    let ch = line[i..].chars().next().expect("valid char boundary");
                    i += ch.len_utf8();
                }
                continue;
            }

            if *in_string {
                if bytes[i] == b'\\' {
                    i += 1;
                    if i < line.len() {
                        let ch = line[i..].chars().next().expect("valid char boundary");
                        i += ch.len_utf8();
                    }
                } else if bytes[i] == b'"' {
                    *in_string = false;
                    i += 1;
                } else {
                    let ch = line[i..].chars().next().expect("valid char boundary");
                    i += ch.len_utf8();
                }
                continue;
            }

            if bytes[i..].starts_with(b"--") {
                break;
            }
            if bytes[i..].starts_with(b"/-") {
                *block_comment_depth += 1;
                i += 2;
                continue;
            }
            if bytes[i] == b'"' {
                *in_string = true;
                out.push(' ');
                i += 1;
                continue;
            }

            let ch = line[i..].chars().next().expect("valid char boundary");
            out.push(ch);
            i += ch.len_utf8();
        }

        out
    }

    /// Check if a module needs rebuilding
    #[must_use]
    pub fn needs_rebuild(&self, module_name: &str) -> bool {
        let Some(src) = self.find_module(module_name) else {
            return false;
        };

        let olean = self.olean_path(module_name);

        // Rebuild if .olean doesn't exist
        if !olean.exists() {
            return true;
        }

        // Rebuild if source is newer
        let src_time = std::fs::metadata(&src).and_then(|m| m.modified()).ok();
        let olean_time = std::fs::metadata(&olean).and_then(|m| m.modified()).ok();

        match (src_time, olean_time) {
            (Some(src_t), Some(olean_t)) => src_t > olean_t,
            _ => true,
        }
    }

    /// Create workspace directories
    pub fn create_dirs(&self) -> LakeResult<()> {
        std::fs::create_dir_all(self.build_dir())?;
        std::fs::create_dir_all(self.lib_dir())?;
        Ok(())
    }

    /// Validate that declared dependencies are satisfied by the manifest
    pub fn validate_dependencies(&self) -> LakeResult<()> {
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
mod tests {
    use super::*;
    use std::fs;
    use tempfile::TempDir;

    #[test]
    fn test_path_to_module_name() {
        assert_eq!(
            Workspace::path_to_module_name(Path::new("MyLib/Core.lean")),
            "MyLib.Core"
        );
        assert_eq!(
            Workspace::path_to_module_name(Path::new("Main.lean")),
            "Main"
        );
        assert_eq!(
            Workspace::path_to_module_name(Path::new("A/B/C.lean")),
            "A.B.C"
        );
    }

    #[test]
    fn test_module_name_to_path() {
        assert_eq!(
            Workspace::module_name_to_path("MyLib.Core"),
            PathBuf::from("MyLib/Core.lean")
        );
        assert_eq!(
            Workspace::module_name_to_path("Main"),
            PathBuf::from("Main.lean")
        );
    }

    #[test]
    fn test_workspace_new() {
        let tmp = TempDir::new().unwrap();
        let ws = Workspace::new(tmp.path(), "test");
        assert_eq!(ws.config().package.name, "test");
        assert!(ws.toolchain().is_none());
    }

    #[test]
    fn test_workspace_load() {
        let tmp = TempDir::new().unwrap();

        // Create lakefile.lean
        let lakefile = tmp.path().join("lakefile.lean");
        fs::write(&lakefile, "package test\nlean_lib Test").unwrap();

        // Create a source file
        let src = tmp.path().join("Test.lean");
        fs::write(&src, "-- Test module").unwrap();
        fs::copy(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../tests/fixtures/lean_toolchain/repo-root/lean-toolchain"),
            tmp.path().join("lean-toolchain"),
        )
        .unwrap();

        let ws = Workspace::load(tmp.path()).unwrap();
        assert_eq!(ws.config().package.name, "test");
        assert_eq!(ws.toolchain(), Some("leanprover/lean4:v4.13.0"));
        assert_eq!(ws.toolchain_version(), Some("v4.13.0"));
        assert!(
            ws.find_module("Test").is_some(),
            "workspace should find 'Test' module"
        );
        assert!(
            !ws.all_modules().iter().any(|module| module == "lakefile"),
            "workspace should not index lakefile.lean as a buildable module"
        );
    }

    #[test]
    fn test_workspace_load_toml() {
        let tmp = TempDir::new().unwrap();

        // A TOML-configured project (no lakefile.lean) must load natively.
        let lakefile = tmp.path().join("lakefile.toml");
        fs::write(
            &lakefile,
            "name = \"test\"\n\n[[lean_lib]]\nname = \"Test\"\n",
        )
        .unwrap();

        let src = tmp.path().join("Test.lean");
        fs::write(&src, "-- Test module").unwrap();

        let ws = Workspace::load(tmp.path()).unwrap();
        assert_eq!(ws.config().package.name, "test");
        assert!(
            ws.find_module("Test").is_some(),
            "TOML workspace should find 'Test' module"
        );
        assert!(
            ws.config().libs.iter().any(|lib| lib.name == "Test"),
            "TOML workspace should parse the [[lean_lib]] target"
        );
    }

    #[test]
    fn test_workspace_load_ignores_comment_lines_in_toolchain() {
        let tmp = TempDir::new().unwrap();
        let lakefile = tmp.path().join("lakefile.lean");
        fs::write(&lakefile, "package test\nlean_lib Test").unwrap();
        fs::write(
            tmp.path().join("lean-toolchain"),
            "\n# repo note\n-- Lean version\nleanprover/lean4:v4.29.1\n",
        )
        .unwrap();

        let ws = Workspace::load(tmp.path()).unwrap();
        assert_eq!(ws.toolchain(), Some("leanprover/lean4:v4.29.1"));
        assert_eq!(ws.toolchain_version(), Some("v4.29.1"));
    }

    #[test]
    fn test_workspace_load_rejects_multiple_toolchain_identifiers() {
        let tmp = TempDir::new().unwrap();
        let lakefile = tmp.path().join("lakefile.lean");
        fs::write(&lakefile, "package test\nlean_lib Test").unwrap();
        fs::write(
            tmp.path().join("lean-toolchain"),
            "leanprover/lean4:v4.29.1\nleanprover/lean4:v4.28.0\n",
        )
        .unwrap();

        let err = Workspace::load(tmp.path()).unwrap_err();
        assert!(err
            .to_string()
            .contains("must contain a single toolchain identifier"));
    }

    #[test]
    fn test_workspace_olean_path() {
        let tmp = TempDir::new().unwrap();
        let ws = Workspace::new(tmp.path(), "test");

        let olean = ws.olean_path("MyLib.Core");
        assert!(olean.to_string_lossy().contains("MyLib"));
        assert!(olean.to_string_lossy().ends_with(".olean"));
    }

    /// Create a `.lean` source file for `module_name` under `root`,
    /// translating the dotted module name into the matching directory layout.
    fn write_module(root: &Path, module_name: &str) {
        let rel = Workspace::module_name_to_path(module_name);
        let path = root.join(rel);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).unwrap();
        }
        fs::write(&path, format!("-- module {module_name}")).unwrap();
    }

    /// Build a workspace from an inline lakefile plus a set of module files.
    fn workspace_with_modules(lakefile: &str, modules: &[&str]) -> (TempDir, Workspace) {
        let tmp = TempDir::new().unwrap();
        fs::write(tmp.path().join("lakefile.lean"), lakefile).unwrap();
        for module in modules {
            write_module(tmp.path(), module);
        }
        let ws = Workspace::load(tmp.path()).unwrap();
        (tmp, ws)
    }

    #[test]
    fn test_lib_modules_submodules_glob_excludes_self_and_unrelated() {
        let lakefile = "package p\nlean_lib Foo where\n  globs := #[.submodules `Foo]\n";
        let (_tmp, ws) =
            workspace_with_modules(lakefile, &["Foo", "Foo.Bar", "Foo.Baz", "Qux", "FooBar"]);

        let mut modules = ws.lib_modules("Foo");
        modules.sort();

        assert_eq!(
            modules,
            vec!["Foo.Bar".to_string(), "Foo.Baz".to_string()],
            ".submodules Foo should include Foo.Bar/Foo.Baz but not Foo, Qux, or FooBar"
        );
    }

    #[test]
    fn test_lib_modules_and_submodules_glob_includes_self() {
        let lakefile = "package p\nlean_lib Foo where\n  globs := #[.andSubmodules `Foo]\n";
        let (_tmp, ws) = workspace_with_modules(lakefile, &["Foo", "Foo.Bar", "Qux"]);

        let mut modules = ws.lib_modules("Foo");
        modules.sort();

        assert_eq!(
            modules,
            vec!["Foo".to_string(), "Foo.Bar".to_string()],
            ".andSubmodules Foo should include Foo and Foo.Bar but not Qux"
        );
    }

    #[test]
    fn test_lib_modules_one_glob_includes_only_named_module() {
        let lakefile = "package p\nlean_lib Foo where\n  globs := #[.one `Foo]\n";
        let (_tmp, ws) = workspace_with_modules(lakefile, &["Foo", "Foo.Bar", "Qux"]);

        let modules = ws.lib_modules("Foo");

        assert_eq!(
            modules,
            vec!["Foo".to_string()],
            ".one Foo should include only Foo"
        );
    }

    #[test]
    fn test_lib_modules_empty_globs_preserves_root_prefix_behavior() {
        // Regression pin: a lib without explicit globs must behave exactly as
        // before — each root plus every module whose name has the root as a
        // prefix (legacy prefix match, no glob filtering).
        let lakefile = "package p\nlean_lib Foo\n";
        let (_tmp, ws) = workspace_with_modules(lakefile, &["Foo", "Foo.Bar", "Foo.Baz", "Qux"]);

        let mut modules = ws.lib_modules("Foo");
        modules.sort();

        assert_eq!(
            modules,
            vec!["Foo".to_string(), "Foo.Bar".to_string(), "Foo.Baz".to_string()],
            "empty globs should include the root and its prefixed submodules, excluding unrelated Qux"
        );
    }

    #[test]
    fn test_lib_modules_union_of_multiple_globs() {
        let lakefile = "package p\nlean_lib Lib where\n  globs := #[.one `Foo, .submodules `Bar]\n";
        let (_tmp, ws) = workspace_with_modules(
            lakefile,
            &["Foo", "Foo.Inner", "Bar", "Bar.A", "Bar.B", "Qux"],
        );

        let mut modules = ws.lib_modules("Lib");
        modules.sort();

        assert_eq!(
            modules,
            vec!["Bar.A".to_string(), "Bar.B".to_string(), "Foo".to_string()],
            "union of .one Foo and .submodules Bar"
        );
    }
}
