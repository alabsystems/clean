// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dependency fetching
//!
//! Fetches git dependencies for Lake projects.

use crate::config::{Dependency, LakeConfig};
use crate::error::{LakeError, LakeResult};
use crate::manifest::{GitPackage, LakeManifest, ManifestPackage, PathPackage};
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;

/// Fetch manager for Lake dependencies
pub struct FetchManager {
    /// Root directory of the workspace
    root: PathBuf,
    /// Packages directory
    packages_dir: PathBuf,
}

impl FetchManager {
    /// Create a new fetch manager
    #[must_use]
    pub fn new(root: &Path, packages_dir: &Path) -> Self {
        Self {
            root: root.to_path_buf(),
            packages_dir: packages_dir.to_path_buf(),
        }
    }

    /// Fetch all dependencies listed in the manifest
    pub fn fetch_all(&self, manifest: &LakeManifest) -> LakeResult<Vec<String>> {
        let mut fetched = vec![];

        for pkg in &manifest.packages {
            match pkg {
                ManifestPackage::Git(git_pkg) => {
                    self.fetch_git_package(git_pkg)?;
                    fetched.push(git_pkg.name.clone());
                }
                ManifestPackage::Path(path_pkg) => {
                    // Path packages don't need fetching, but validate they exist
                    let pkg_path = self.root.join(&path_pkg.path);
                    if !pkg_path.exists() {
                        return Err(LakeError::PackageNotFound {
                            name: path_pkg.name.clone(),
                            path: pkg_path,
                        });
                    }
                }
            }
        }

        Ok(fetched)
    }

    /// Fetch a single git package
    pub fn fetch_git_package(&self, pkg: &GitPackage) -> LakeResult<PathBuf> {
        let pkg_dir = self.packages_dir.join(&pkg.name);

        // Check if already fetched at correct revision
        if pkg_dir.exists() {
            let rev = &pkg.rev;
            if rev.is_empty() {
                // No specific revision requested, assume current is fine
                return Ok(pkg_dir);
            }
            let current_rev = self.get_git_rev(&pkg_dir)?;
            if current_rev.starts_with(rev) || rev.starts_with(&current_rev) {
                // Already at correct revision
                return Ok(pkg_dir);
            }
        }

        // Create packages directory if needed
        std::fs::create_dir_all(&self.packages_dir)?;

        if pkg_dir.exists() {
            // Update existing clone
            self.update_git_package(&pkg_dir, pkg)?;
        } else {
            // Clone new package
            self.clone_git_package(&pkg_dir, pkg)?;
        }

        Ok(pkg_dir)
    }

    /// Clone a git package
    fn clone_git_package(&self, target_dir: &Path, pkg: &GitPackage) -> LakeResult<()> {
        let rev = &pkg.rev;

        // Try shallow clone with branch/tag first
        if !rev.is_empty() {
            let output = Command::new("git")
                .arg("clone")
                .arg("--depth")
                .arg("1")
                .arg("--branch")
                .arg(rev)
                .arg(&pkg.url)
                .arg(target_dir)
                .output()
                .map_err(|e| LakeError::GitError {
                    operation: "clone".to_string(),
                    message: e.to_string(),
                })?;

            if output.status.success() {
                return Ok(());
            }

            // Remove partial clone before full clone
            if target_dir.exists() {
                std::fs::remove_dir_all(target_dir)?;
            }

            // Shallow clone failed, try full clone with checkout
            return self.clone_with_checkout(target_dir, pkg);
        }

        // No specific revision, just clone
        let output = Command::new("git")
            .arg("clone")
            .arg("--depth")
            .arg("1")
            .arg(&pkg.url)
            .arg(target_dir)
            .output()
            .map_err(|e| LakeError::GitError {
                operation: "clone".to_string(),
                message: e.to_string(),
            })?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(LakeError::GitError {
                operation: "clone".to_string(),
                message: stderr.to_string(),
            });
        }

        Ok(())
    }

    /// Clone with full history and checkout specific commit
    fn clone_with_checkout(&self, target_dir: &Path, pkg: &GitPackage) -> LakeResult<()> {
        // Remove partial clone if it exists
        if target_dir.exists() {
            std::fs::remove_dir_all(target_dir)?;
        }

        // Clone without depth
        let output = Command::new("git")
            .arg("clone")
            .arg(&pkg.url)
            .arg(target_dir)
            .output()
            .map_err(|e| LakeError::GitError {
                operation: "clone".to_string(),
                message: e.to_string(),
            })?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(LakeError::GitError {
                operation: "clone".to_string(),
                message: stderr.to_string(),
            });
        }

        // Checkout specific revision
        let rev = &pkg.rev;
        if !rev.is_empty() {
            let output = Command::new("git")
                .arg("-C")
                .arg(target_dir)
                .arg("checkout")
                .arg(rev)
                .output()
                .map_err(|e| LakeError::GitError {
                    operation: "checkout".to_string(),
                    message: e.to_string(),
                })?;

            if !output.status.success() {
                let stderr = String::from_utf8_lossy(&output.stderr);
                return Err(LakeError::GitError {
                    operation: "checkout".to_string(),
                    message: stderr.to_string(),
                });
            }
        }

        Ok(())
    }

    /// Update an existing git package
    fn update_git_package(&self, pkg_dir: &Path, pkg: &GitPackage) -> LakeResult<()> {
        // Fetch latest
        let output = Command::new("git")
            .arg("-C")
            .arg(pkg_dir)
            .arg("fetch")
            .arg("--all")
            .output()
            .map_err(|e| LakeError::GitError {
                operation: "fetch".to_string(),
                message: e.to_string(),
            })?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(LakeError::GitError {
                operation: "fetch".to_string(),
                message: stderr.to_string(),
            });
        }

        // Checkout specific revision if specified
        let rev = &pkg.rev;
        if !rev.is_empty() {
            let output = Command::new("git")
                .arg("-C")
                .arg(pkg_dir)
                .arg("checkout")
                .arg(rev)
                .output()
                .map_err(|e| LakeError::GitError {
                    operation: "checkout".to_string(),
                    message: e.to_string(),
                })?;

            if !output.status.success() {
                let stderr = String::from_utf8_lossy(&output.stderr);
                return Err(LakeError::GitError {
                    operation: "checkout".to_string(),
                    message: stderr.to_string(),
                });
            }
        }

        Ok(())
    }

    /// Get current git revision for a directory
    fn get_git_rev(&self, dir: &Path) -> LakeResult<String> {
        let output = Command::new("git")
            .arg("-C")
            .arg(dir)
            .arg("rev-parse")
            .arg("HEAD")
            .output()
            .map_err(|e| LakeError::GitError {
                operation: "rev-parse".to_string(),
                message: e.to_string(),
            })?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(LakeError::GitError {
                operation: "rev-parse".to_string(),
                message: stderr.to_string(),
            });
        }

        Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
    }

    /// Check if git is available
    #[must_use]
    pub fn git_available() -> bool {
        Command::new("git")
            .arg("--version")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
    }

    /// Update a git package to the latest revision from remote
    /// Returns the new commit SHA
    pub fn update_to_latest(&self, pkg: &GitPackage) -> LakeResult<String> {
        let pkg_dir = self.packages_dir.join(&pkg.name);

        if !pkg_dir.exists() {
            // Package not fetched yet, fetch it first
            self.fetch_git_package(pkg)?;
        }

        // Determine the branch to update
        let branch = pkg.input_rev.as_deref().unwrap_or("main");

        // Fetch from remote
        let output = Command::new("git")
            .arg("-C")
            .arg(&pkg_dir)
            .arg("fetch")
            .arg("origin")
            .arg(branch)
            .output()
            .map_err(|e| LakeError::GitError {
                operation: "fetch".to_string(),
                message: e.to_string(),
            })?;

        if !output.status.success() {
            // Try fetching all if specific branch fails
            Command::new("git")
                .arg("-C")
                .arg(&pkg_dir)
                .arg("fetch")
                .arg("--all")
                .output()
                .map_err(|e| LakeError::GitError {
                    operation: "fetch".to_string(),
                    message: e.to_string(),
                })?;
        }

        // Reset to origin/branch
        let target = format!("origin/{branch}");
        let output = Command::new("git")
            .arg("-C")
            .arg(&pkg_dir)
            .arg("reset")
            .arg("--hard")
            .arg(&target)
            .output()
            .map_err(|e| LakeError::GitError {
                operation: "reset".to_string(),
                message: e.to_string(),
            })?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(LakeError::GitError {
                operation: "reset".to_string(),
                message: stderr.to_string(),
            });
        }

        // Get the new revision
        self.get_git_rev(&pkg_dir)
    }

    /// Update all git packages and return the updated manifest
    pub fn update_all(
        &self,
        manifest: &LakeManifest,
    ) -> LakeResult<(LakeManifest, Vec<UpdateResult>)> {
        let mut updated_manifest = manifest.clone();
        let mut results = vec![];

        for (idx, pkg) in manifest.packages.iter().enumerate() {
            match pkg {
                ManifestPackage::Git(git_pkg) => {
                    let old_rev = git_pkg.rev.clone();
                    match self.update_to_latest(git_pkg) {
                        Ok(new_rev) => {
                            if new_rev != old_rev {
                                // Update the manifest entry
                                if let Some(ManifestPackage::Git(ref mut mp)) =
                                    updated_manifest.packages.get_mut(idx)
                                {
                                    mp.rev = new_rev.clone();
                                }
                                results.push(UpdateResult {
                                    name: git_pkg.name.clone(),
                                    old_rev,
                                    new_rev,
                                    status: UpdateStatus::Updated,
                                });
                            } else {
                                results.push(UpdateResult {
                                    name: git_pkg.name.clone(),
                                    old_rev: old_rev.clone(),
                                    new_rev: old_rev,
                                    status: UpdateStatus::UpToDate,
                                });
                            }
                        }
                        Err(e) => {
                            results.push(UpdateResult {
                                name: git_pkg.name.clone(),
                                old_rev: old_rev.clone(),
                                new_rev: old_rev,
                                status: UpdateStatus::Error(e.to_string()),
                            });
                        }
                    }
                }
                ManifestPackage::Path(path_pkg) => {
                    // Path packages don't get updated
                    results.push(UpdateResult {
                        name: path_pkg.name.clone(),
                        old_rev: String::new(),
                        new_rev: String::new(),
                        status: UpdateStatus::Skipped,
                    });
                }
            }
        }

        Ok((updated_manifest, results))
    }
}

/// Result of updating a single package
#[derive(Debug)]
pub struct UpdateResult {
    /// Package name
    pub name: String,
    /// Previous revision
    pub old_rev: String,
    /// New revision
    pub new_rev: String,
    /// Update status
    pub status: UpdateStatus,
}

/// Status of an update operation
#[derive(Debug)]
pub enum UpdateStatus {
    /// Package was updated to a new revision
    Updated,
    /// Package was already at the latest revision
    UpToDate,
    /// Package was skipped (path package)
    Skipped,
    /// Error occurred during update
    Error(String),
}

/// Result of resolving dependencies
#[derive(Debug)]
pub struct ResolveResult {
    /// Packages that were resolved
    pub resolved: Vec<ResolvedPackage>,
    /// Errors encountered during resolution
    pub errors: Vec<(String, String)>,
}

/// A resolved package with concrete revision
#[derive(Debug, Clone)]
pub struct ResolvedPackage {
    /// Package name
    pub name: String,
    /// Git URL (if git dependency)
    pub url: Option<String>,
    /// Resolved commit SHA
    pub rev: String,
    /// Original input revision (branch/tag name)
    pub input_rev: Option<String>,
    /// Path (if path dependency)
    pub path: Option<String>,
    /// Whether this package was transitively inherited from another
    /// package's requires (Lake manifest key: `inherited`)
    pub inherited: bool,
}

/// Maximum transitive `require` depth followed during dependency resolution.
///
/// Real dependency graphs (Mathlib and its closure) are only a handful of
/// levels deep; hitting this bound indicates a runaway or malformed
/// transitive require chain and is reported as a loud per-dependency error.
const MAX_RESOLVE_DEPTH: usize = 64;

/// Mutable state threaded through recursive dependency resolution.
struct ResolveCtx {
    /// Package names already resolved (first-wins conflict policy, like Lake)
    visited: BTreeSet<String>,
    /// Names currently being expanded, for cycle detection
    stack: Vec<String>,
    /// Successfully resolved packages, in first-encounter order
    resolved: Vec<ResolvedPackage>,
    /// Per-dependency resolution errors `(name, message)`
    errors: Vec<(String, String)>,
}

impl FetchManager {
    /// Resolve dependencies declared in the lakefile to concrete revisions,
    /// following each fetched package's own requires transitively.
    ///
    /// After fetching each git/path dependency this opens the dependency's
    /// own lakefile (`lakefile.toml` preferred, `lakefile.lean` fallback) and
    /// resolves its requires into the same result, so the full transitive
    /// closure lands in the manifest (as real Lake does for Mathlib-shaped
    /// projects). Name conflicts are first-wins (matching Lake), require
    /// cycles are detected and reported, and expansion is bounded by
    /// [`MAX_RESOLVE_DEPTH`]. Failures are collected per dependency in
    /// [`ResolveResult::errors`] rather than aborting the whole resolution.
    pub fn resolve_dependencies(&self, dependencies: &[Dependency]) -> LakeResult<ResolveResult> {
        let mut ctx = ResolveCtx {
            visited: BTreeSet::new(),
            stack: Vec::new(),
            resolved: Vec::new(),
            errors: Vec::new(),
        };

        for dep in dependencies {
            self.resolve_recursive(&mut ctx, dep, &self.root, 0);
        }

        Ok(ResolveResult {
            resolved: ctx.resolved,
            errors: ctx.errors,
        })
    }

    /// Resolve one dependency and recurse into the fetched package's own
    /// requires. `base_dir` is the directory of the package that declared
    /// `dep` (path requires are relative to their declaring package).
    fn resolve_recursive(
        &self,
        ctx: &mut ResolveCtx,
        dep: &Dependency,
        base_dir: &Path,
        depth: usize,
    ) {
        if depth > MAX_RESOLVE_DEPTH {
            let err = LakeError::DependencyDepthExceeded {
                name: dep.name.clone(),
                limit: MAX_RESOLVE_DEPTH,
            };
            ctx.errors.push((dep.name.clone(), err.to_string()));
            return;
        }

        // Cycle detection: a require chain re-entering a package that is
        // still being expanded is a genuine dependency cycle.
        if ctx.stack.contains(&dep.name) {
            let mut chain = ctx.stack.clone();
            chain.push(dep.name.clone());
            let err = LakeError::CircularDependency(chain.join(" -> "));
            ctx.errors.push((dep.name.clone(), err.to_string()));
            return;
        }

        // First-wins conflict policy (matching Lake): an earlier require
        // already resolved this package name.
        if ctx.visited.contains(&dep.name) {
            return;
        }

        let (mut pkg, pkg_dir) = match self.resolve_single_dependency(dep, base_dir) {
            Ok(ok) => ok,
            Err(e) => {
                ctx.errors.push((dep.name.clone(), e.to_string()));
                return;
            }
        };
        pkg.inherited = depth > 0;
        ctx.visited.insert(dep.name.clone());
        ctx.resolved.push(pkg);

        // Open the fetched package's own lakefile (toml preferred, lean
        // fallback) and resolve ITS requires into the same result set.
        match LakeConfig::load_from_dir(&pkg_dir) {
            Err(LakeError::LakefileNotFound(_)) => {
                // Leaf package: no lakefile means no further requires.
            }
            Err(e) => {
                ctx.errors.push((
                    dep.name.clone(),
                    format!("failed to load lakefile of fetched package: {e}"),
                ));
            }
            Ok(sub_config) => {
                ctx.stack.push(dep.name.clone());
                for sub in &sub_config.package.dependencies {
                    self.resolve_recursive(ctx, sub, &pkg_dir, depth + 1);
                }
                ctx.stack.pop();
            }
        }
    }

    /// Resolve a single dependency to a concrete revision. Returns the
    /// resolved package (with `inherited` unset) and the on-disk directory
    /// of the fetched package, for transitive lakefile inspection.
    fn resolve_single_dependency(
        &self,
        dep: &Dependency,
        base_dir: &Path,
    ) -> LakeResult<(ResolvedPackage, PathBuf)> {
        // Handle path dependencies (relative to the declaring package's dir)
        if let Some(path) = &dep.path {
            let full_path = base_dir.join(path);
            if !full_path.exists() {
                return Err(LakeError::PackageNotFound {
                    name: dep.name.clone(),
                    path: full_path,
                });
            }
            let stored_path = if base_dir == self.root.as_path() {
                path.to_string_lossy().to_string()
            } else {
                // Transitive path requires are declared relative to their
                // parent package; re-express them relative to the workspace
                // root so the manifest entry is meaningful from the root.
                match (full_path.canonicalize(), self.root.canonicalize()) {
                    (Ok(canon), Ok(root)) => canon
                        .strip_prefix(&root)
                        .map(|p| p.to_string_lossy().to_string())
                        .unwrap_or_else(|_| canon.to_string_lossy().to_string()),
                    _ => full_path.to_string_lossy().to_string(),
                }
            };
            return Ok((
                ResolvedPackage {
                    name: dep.name.clone(),
                    url: None,
                    rev: String::new(),
                    input_rev: None,
                    path: Some(stored_path),
                    inherited: false,
                },
                full_path,
            ));
        }

        // Handle git dependencies
        let url = dep.git.as_ref().ok_or_else(|| {
            LakeError::InvalidConfig(format!(
                "dependency '{}' has neither git nor path specified",
                dep.name
            ))
        })?;

        // Create a temporary GitPackage to fetch
        let input_rev = dep.rev.clone().or_else(|| dep.version.clone());
        let temp_pkg = GitPackage::new(&dep.name, url, input_rev.as_deref().unwrap_or("main"));

        // Fetch the package
        let pkg_dir = self.fetch_git_package(&temp_pkg)?;

        // Get the actual commit SHA
        let rev = self.get_git_rev(&pkg_dir)?;

        Ok((
            ResolvedPackage {
                name: dep.name.clone(),
                url: Some(url.clone()),
                rev,
                input_rev,
                path: None,
                inherited: false,
            },
            pkg_dir,
        ))
    }

    /// Resolve dependencies and generate a manifest
    pub fn resolve_to_manifest(
        &self,
        dependencies: &[Dependency],
    ) -> LakeResult<(LakeManifest, ResolveResult)> {
        let result = self.resolve_dependencies(dependencies)?;

        let mut manifest = LakeManifest::empty();
        for pkg in &result.resolved {
            if let Some(url) = &pkg.url {
                manifest.upsert_package(ManifestPackage::Git(GitPackage {
                    name: pkg.name.clone(),
                    url: url.clone(),
                    rev: pkg.rev.clone(),
                    input_rev: pkg.input_rev.clone(),
                    inherited: Some(pkg.inherited),
                    ..Default::default()
                }));
            } else if let Some(path) = &pkg.path {
                let mut path_pkg = PathPackage::new(&pkg.name, path);
                path_pkg.inherited = Some(pkg.inherited);
                manifest.upsert_package(ManifestPackage::Path(path_pkg));
            }
        }

        Ok((manifest, result))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    #[test]
    fn test_git_available() {
        // Git should be available in test environment
        assert!(FetchManager::git_available());
    }

    #[test]
    fn test_fetch_manager_new() {
        let root = Path::new("/tmp/test_project");
        let packages = Path::new("/tmp/test_project/.lake/packages");
        let fm = FetchManager::new(root, packages);
        assert_eq!(fm.root, root);
        assert_eq!(fm.packages_dir, packages);
    }

    #[test]
    fn test_resolve_result_empty() {
        let result = ResolveResult {
            resolved: vec![],
            errors: vec![],
        };
        assert!(result.resolved.is_empty());
        assert!(result.errors.is_empty());
    }

    #[test]
    fn test_resolved_package_git() {
        let pkg = ResolvedPackage {
            name: "std".to_string(),
            url: Some("https://github.com/leanprover/std4".to_string()),
            rev: "abc123def456".to_string(),
            input_rev: Some("main".to_string()),
            path: None,
            inherited: false,
        };
        assert_eq!(pkg.name, "std");
        assert!(pkg.url.is_some(), "git package should have url");
        assert!(pkg.path.is_none(), "git package should not have path");
    }

    #[test]
    fn test_resolved_package_path() {
        let pkg = ResolvedPackage {
            name: "local".to_string(),
            url: None,
            rev: String::new(),
            input_rev: None,
            path: Some("../local-pkg".to_string()),
            inherited: false,
        };
        assert_eq!(pkg.name, "local");
        assert!(pkg.url.is_none(), "path package should not have url");
        assert!(pkg.path.is_some(), "path package should have path");
    }

    #[test]
    fn test_resolve_path_dependency_not_found() {
        use tempfile::tempdir;

        let temp = tempdir().unwrap();
        let root = temp.path();
        let packages_dir = root.join(".lake/packages");

        let fm = FetchManager::new(root, &packages_dir);

        let dep = Dependency {
            name: "missing".to_string(),
            git: None,
            rev: None,
            path: Some(PathBuf::from("nonexistent")),
            version: None,
        };

        let result = fm.resolve_dependencies(&[dep]).unwrap();
        assert!(result.resolved.is_empty());
        assert_eq!(result.errors.len(), 1);
        assert!(result.errors[0].1.contains("not found"));
    }

    #[test]
    fn test_resolve_dependency_no_source() {
        use tempfile::tempdir;

        let temp = tempdir().unwrap();
        let root = temp.path();
        let packages_dir = root.join(".lake/packages");

        let fm = FetchManager::new(root, &packages_dir);

        let dep = Dependency {
            name: "invalid".to_string(),
            git: None,
            rev: None,
            path: None,
            version: None,
        };

        let result = fm.resolve_dependencies(&[dep]).unwrap();
        assert!(result.resolved.is_empty());
        assert_eq!(result.errors.len(), 1);
        assert!(result.errors[0].1.contains("neither git nor path"));
    }

    /// Write a minimal `lakefile.toml` package into `dir`, with the given
    /// path-form requires (each relative to `dir`, as Lake declares them).
    fn write_lakefile_toml(dir: &Path, name: &str, path_requires: &[(&str, &str)]) {
        std::fs::create_dir_all(dir).unwrap();
        let mut content = format!("name = \"{name}\"\n");
        for (rname, rpath) in path_requires {
            let req = format!("\n[[require]]\nname = \"{rname}\"\npath = \"{rpath}\"\n");
            content.push_str(&req);
        }
        std::fs::write(dir.join("lakefile.toml"), content).unwrap();
    }

    /// Run a git subcommand in `dir`, panicking with stderr on failure.
    fn git(dir: &Path, args: &[&str]) {
        let out = Command::new("git")
            .arg("-C")
            .arg(dir)
            .args(args)
            .output()
            .expect("git should be runnable in the test environment");
        assert!(
            out.status.success(),
            "git {args:?} failed: {}",
            String::from_utf8_lossy(&out.stderr)
        );
    }

    /// Turn `dir` into a single-commit git repo on branch `main`, so it can
    /// serve as a local "remote" for clone-based fetch tests (no network).
    fn git_init_commit(dir: &Path) {
        git(dir, &["init", "-q", "-b", "main"]);
        git(dir, &["add", "-A"]);
        git(
            dir,
            &[
                "-c",
                "user.email=test@example.com",
                "-c",
                "user.name=Test",
                "-c",
                "commit.gpgsign=false",
                "commit",
                "-q",
                "-m",
                "init",
            ],
        );
    }

    fn path_dep(name: &str, path: &str) -> Dependency {
        Dependency {
            name: name.to_string(),
            git: None,
            rev: None,
            path: Some(PathBuf::from(path)),
            version: None,
        }
    }

    /// Transitive closure over path deps: root requires B, B's own lakefile
    /// requires C — the manifest must list BOTH B and C, with C re-expressed
    /// relative to the workspace root and flagged as inherited.
    #[test]
    fn test_resolve_transitive_path_deps_lists_full_closure() {
        use tempfile::tempdir;

        let temp = tempdir().unwrap();
        let root = temp.path();
        let packages_dir = root.join(".lake/packages");
        // B requires C relative to B's own directory, as Lake declares it.
        write_lakefile_toml(&root.join("depB"), "depB", &[("depC", "../depC")]);
        write_lakefile_toml(&root.join("depC"), "depC", &[]);

        let fm = FetchManager::new(root, &packages_dir);
        let (manifest, result) = fm
            .resolve_to_manifest(&[path_dep("depB", "depB")])
            .expect("resolution should succeed");

        assert!(
            result.errors.is_empty(),
            "unexpected errors: {:?}",
            result.errors
        );
        let names: Vec<&str> = result.resolved.iter().map(|p| p.name.as_str()).collect();
        assert_eq!(names, vec!["depB", "depC"]);
        assert!(!result.resolved[0].inherited, "direct dep is not inherited");
        assert!(result.resolved[1].inherited, "transitive dep is inherited");
        // C's path was declared as "../depC" relative to depB; the manifest
        // entry must be meaningful from the workspace root.
        assert_eq!(result.resolved[1].path.as_deref(), Some("depC"));

        let b = manifest
            .get_package("depB")
            .expect("B listed in manifest")
            .as_path()
            .expect("B is a path package");
        assert_eq!(b.inherited, Some(false));
        let c = manifest
            .get_package("depC")
            .expect("transitive C listed in manifest")
            .as_path()
            .expect("C is a path package");
        assert_eq!(c.path, "depC");
        assert_eq!(c.inherited, Some(true));
    }

    /// Transitive closure over git deps using local repos as "remotes" (no
    /// network): root requires git package B, whose lakefile requires git
    /// package C — the manifest must pin concrete commit SHAs for BOTH.
    #[test]
    fn test_resolve_transitive_git_deps_pins_revs() {
        use tempfile::tempdir;

        let temp = tempdir().unwrap();
        let remotes = temp.path().join("remotes");

        // Leaf repo C.
        let repo_c = remotes.join("depC");
        write_lakefile_toml(&repo_c, "depC", &[]);
        git_init_commit(&repo_c);

        // Repo B requires C via a git URL (a local path works with git clone).
        let repo_b = remotes.join("depB");
        std::fs::create_dir_all(&repo_b).unwrap();
        std::fs::write(
            repo_b.join("lakefile.toml"),
            format!(
                "name = \"depB\"\n\n[[require]]\nname = \"depC\"\ngit = \"{}\"\n",
                repo_c.display()
            ),
        )
        .unwrap();
        git_init_commit(&repo_b);

        let proj = temp.path().join("proj");
        std::fs::create_dir_all(&proj).unwrap();
        let packages_dir = proj.join(".lake/packages");
        let fm = FetchManager::new(&proj, &packages_dir);

        let dep = Dependency {
            name: "depB".to_string(),
            git: Some(repo_b.display().to_string()),
            rev: None,
            path: None,
            version: None,
        };

        let (manifest, result) = fm
            .resolve_to_manifest(&[dep])
            .expect("resolution should succeed");
        assert!(
            result.errors.is_empty(),
            "unexpected errors: {:?}",
            result.errors
        );
        assert_eq!(result.resolved.len(), 2, "closure must contain B and C");

        for pkg_name in ["depB", "depC"] {
            let git_pkg = manifest
                .get_package(pkg_name)
                .unwrap_or_else(|| panic!("{pkg_name} listed in manifest"))
                .as_git()
                .unwrap_or_else(|| panic!("{pkg_name} is a git package"));
            assert_eq!(git_pkg.rev.len(), 40, "{pkg_name} rev is a full SHA");
            assert!(
                git_pkg.rev.chars().all(|c| c.is_ascii_hexdigit()),
                "{pkg_name} rev is hex: {}",
                git_pkg.rev
            );
        }
        assert_eq!(
            manifest
                .get_package("depB")
                .unwrap()
                .as_git()
                .unwrap()
                .inherited,
            Some(false)
        );
        assert_eq!(
            manifest
                .get_package("depC")
                .unwrap()
                .as_git()
                .unwrap()
                .inherited,
            Some(true)
        );
    }

    /// First-wins conflict policy (matching Lake): when the root requires C
    /// directly and B also requires C, the first resolution wins and C is
    /// listed exactly once.
    #[test]
    fn test_resolve_dedup_first_wins() {
        use tempfile::tempdir;

        let temp = tempdir().unwrap();
        let root = temp.path();
        let packages_dir = root.join(".lake/packages");
        write_lakefile_toml(&root.join("depB"), "depB", &[("depC", "../depC")]);
        write_lakefile_toml(&root.join("depC"), "depC", &[]);

        let fm = FetchManager::new(root, &packages_dir);
        let result = fm
            .resolve_dependencies(&[path_dep("depC", "depC"), path_dep("depB", "depB")])
            .expect("resolution should succeed");

        assert!(
            result.errors.is_empty(),
            "unexpected errors: {:?}",
            result.errors
        );
        let names: Vec<&str> = result.resolved.iter().map(|p| p.name.as_str()).collect();
        assert_eq!(names, vec!["depC", "depB"], "C listed once, first-wins");
        assert!(
            !result.resolved[0].inherited,
            "the direct C resolution won over B's transitive require"
        );
    }

    /// A require cycle (B -> C -> B) must be detected and reported loudly
    /// instead of looping; the acyclic part of the closure still resolves.
    #[test]
    fn test_resolve_cycle_reports_circular_error() {
        use tempfile::tempdir;

        let temp = tempdir().unwrap();
        let root = temp.path();
        let packages_dir = root.join(".lake/packages");
        write_lakefile_toml(&root.join("depB"), "depB", &[("depC", "../depC")]);
        write_lakefile_toml(&root.join("depC"), "depC", &[("depB", "../depB")]);

        let fm = FetchManager::new(root, &packages_dir);
        let result = fm
            .resolve_dependencies(&[path_dep("depB", "depB")])
            .expect("resolution itself should not abort");

        let names: Vec<&str> = result.resolved.iter().map(|p| p.name.as_str()).collect();
        assert_eq!(names, vec!["depB", "depC"], "acyclic part still resolves");
        assert_eq!(result.errors.len(), 1, "the cycle is reported");
        assert_eq!(result.errors[0].0, "depB");
        assert!(
            result.errors[0].1.contains("circular dependency"),
            "error names the cycle: {}",
            result.errors[0].1
        );
        assert!(
            result.errors[0].1.contains("depB -> depC -> depB"),
            "error shows the require chain: {}",
            result.errors[0].1
        );
    }

    /// A require chain deeper than MAX_RESOLVE_DEPTH stops with a loud
    /// depth-bound error instead of expanding forever.
    #[test]
    fn test_resolve_depth_bound_reports_loud_error() {
        use tempfile::tempdir;

        let temp = tempdir().unwrap();
        let root = temp.path();
        let packages_dir = root.join(".lake/packages");

        let n = MAX_RESOLVE_DEPTH + 5;
        for i in 0..=n {
            let dir = root.join(format!("pkg{i}"));
            let name = format!("pkg{i}");
            if i < n {
                let next = format!("pkg{}", i + 1);
                let rel = format!("../{next}");
                write_lakefile_toml(&dir, &name, &[(next.as_str(), rel.as_str())]);
            } else {
                write_lakefile_toml(&dir, &name, &[]);
            }
        }

        let fm = FetchManager::new(root, &packages_dir);
        let result = fm
            .resolve_dependencies(&[path_dep("pkg0", "pkg0")])
            .expect("resolution itself should not abort");

        assert_eq!(
            result.resolved.len(),
            MAX_RESOLVE_DEPTH + 1,
            "packages up to the bound still resolve"
        );
        assert_eq!(result.errors.len(), 1, "the depth overflow is reported");
        assert!(
            result.errors[0].1.contains("maximum depth"),
            "error names the depth bound: {}",
            result.errors[0].1
        );
    }
}
