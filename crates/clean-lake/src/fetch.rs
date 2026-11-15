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
    pub(crate) fn fetch_git_package(&self, pkg: &GitPackage) -> LakeResult<PathBuf> {
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
    pub(crate) fn resolve_dependencies(
        &self,
        dependencies: &[Dependency],
    ) -> LakeResult<ResolveResult> {
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

        // Fetch the package. A clone failure on a URL derived from a
        // scope-only (Reservoir) require is attributed to that offline
        // derivation instead of surfacing as a bare git error.
        let pkg_dir = self
            .fetch_git_package(&temp_pkg)
            .map_err(|e| attribute_scope_only_fetch_error(dep, url, e))?;

        // Get the actual commit SHA. This reads git metadata, so it must run
        // against the CLONE root, never a `subDir` beneath it.
        let rev = self.get_git_rev(&pkg_dir)?;

        // A `subDir` require names a package that lives inside the repository
        // rather than at its root (how a monorepo publishes several Lake
        // packages from one repo). The clone is only the transport; the package
        // root is the subdirectory, and resolving to the clone root instead
        // would silently build the wrong tree.
        let package_dir = match &dep.sub_dir {
            Some(sub) => {
                let joined = pkg_dir.join(sub);
                if !joined.is_dir() {
                    return Err(LakeError::PackageNotFound {
                        name: dep.name.clone(),
                        path: joined,
                    });
                }
                joined
            }
            None => pkg_dir,
        };

        Ok((
            ResolvedPackage {
                name: dep.name.clone(),
                url: Some(url.clone()),
                rev,
                input_rev,
                path: None,
                inherited: false,
            },
            package_dir,
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

/// Attribute a fetch failure to the interim offline scope-to-GitHub mapping
/// when the failed URL was derived from a scope-only (Reservoir) require:
/// the error must name the scope/name and state that the Reservoir registry
/// API was not consulted. Failures on explicitly-written git URLs pass
/// through unchanged (an explicit URL also wins this check when a scope was
/// declared alongside it, because the derivation is only to blame for URLs
/// it produced).
fn attribute_scope_only_fetch_error(dep: &Dependency, url: &str, err: LakeError) -> LakeError {
    let Some(scope) = dep.scope.as_deref() else {
        return err;
    };
    if url != crate::toml_config::reservoir_offline_git_url(scope, &dep.name) {
        return err;
    }
    LakeError::GitError {
        operation: "fetch".to_string(),
        message: format!(
            "scope-only require '{scope}/{name}': clone of {url} failed: {err}. \
             This URL was derived offline from the require's scope; the Reservoir \
             registry API was not consulted (interim limitation). If the package's \
             repository does not follow the github.com/{{scope}}/{{name}} convention, \
             add an explicit `git = \"<url>\"` to the [[require]] entry.",
            name = dep.name
        ),
    }
}

#[cfg(test)]
#[path = "fetch_tests.rs"]
mod tests;
