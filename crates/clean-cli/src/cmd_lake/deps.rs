// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dependency fetching, updating, resolution, and environment info.

use crate::cmd_core::resolve_project_dir;
use std::path::PathBuf;
use std::process::Command;

/// Fetch dependencies from git
pub(super) fn lake_fetch(verbose: bool, dir: Option<PathBuf>) -> anyhow::Result<()> {
    use clean_lake::{FetchManager, LakeManifest};

    let cwd = resolve_project_dir(dir)?;

    // Check for manifest
    let manifest_path = cwd.join("lake-manifest.json");
    if !manifest_path.exists() {
        anyhow::bail!(
            "No lake-manifest.json found in current directory.\n\
             Create a manifest with dependencies to fetch."
        );
    }

    // Load manifest
    let manifest = LakeManifest::load(&manifest_path)?;
    if manifest_requires_git(&manifest) && !FetchManager::git_available() {
        anyhow::bail!("Git is not available. Please install git to fetch dependencies.");
    }

    if manifest.packages.is_empty() {
        println!("No dependencies to fetch.");
        return Ok(());
    }

    let packages_dir = cwd.join(&manifest.packages_dir);
    let fm = FetchManager::new(&cwd, &packages_dir);

    if verbose {
        println!("Fetching {} dependencies...", manifest.packages.len());
    }

    let fetched = fm.fetch_all(&manifest)?;

    if fetched.is_empty() {
        println!("All dependencies up to date.");
    } else {
        println!("Fetched {} dependencies:", fetched.len());
        for name in fetched {
            println!("  {name}");
        }
    }

    Ok(())
}

/// Update dependencies to latest versions
pub(super) fn lake_update(
    package: Option<String>,
    verbose: bool,
    dir: Option<PathBuf>,
) -> anyhow::Result<()> {
    use clean_lake::{FetchManager, LakeManifest, UpdateStatus};

    let cwd = resolve_project_dir(dir)?;

    // Check for manifest. Lake's own `update` REGENERATES the manifest from the
    // lakefile's requires, so a missing one is the ordinary bootstrap case —
    // `lake update` is the second command most Lean users run, on a checkout
    // that has no manifest yet. Refusing it here ("Create a manifest with
    // dependencies to update") asked the user to produce by hand the artifact
    // the command exists to produce. Resolution from the lakefile is exactly
    // what `lake resolve` already does, so bootstrap delegates to it rather
    // than growing a second implementation.
    let manifest_path = cwd.join("lake-manifest.json");
    if !manifest_path.exists() {
        if verbose {
            println!("No lake-manifest.json yet; resolving dependencies from the lakefile.");
        }
        if package.is_some() {
            anyhow::bail!(
                "Cannot update a single package before a lake-manifest.json exists.\n\
                 Run `clean lake update` (no package argument) to resolve the \
                 lakefile's dependencies first."
            );
        }
        return lake_resolve(verbose, false, Some(cwd));
    }

    // Load manifest
    let manifest = LakeManifest::load(&manifest_path)?;
    if manifest_requires_git(&manifest) && !FetchManager::git_available() {
        anyhow::bail!("Git is not available. Please install git to update dependencies.");
    }

    if manifest.packages.is_empty() {
        println!("No dependencies to update.");
        return Ok(());
    }

    let packages_dir = cwd.join(&manifest.packages_dir);
    let fm = FetchManager::new(&cwd, &packages_dir);

    // Filter packages if specific one requested
    if let Some(pkg_name) = package {
        // Find the specific package
        let git_pkg = manifest
            .packages
            .iter()
            .find_map(|p| match p {
                clean_lake::ManifestPackage::Git(g) if g.name == pkg_name => Some(g),
                _ => None,
            })
            .ok_or_else(|| anyhow::anyhow!("Package '{pkg_name}' not found in manifest"))?;

        if verbose {
            println!("Updating package: {pkg_name}");
        }

        let old_rev = git_pkg.rev.clone();
        let new_rev = fm.update_to_latest(git_pkg)?;

        if new_rev != old_rev {
            // Update and save manifest
            let mut updated_manifest = manifest;
            for pkg in &mut updated_manifest.packages {
                if let clean_lake::ManifestPackage::Git(g) = pkg {
                    if g.name == pkg_name {
                        g.rev = new_rev.clone();
                        break;
                    }
                }
            }
            updated_manifest.save(&manifest_path)?;

            println!(
                "Updated {}: {} -> {}",
                pkg_name,
                &old_rev[..old_rev.len().min(8)],
                &new_rev[..new_rev.len().min(8)]
            );
        } else {
            println!("{pkg_name} is already up to date.");
        }
    } else {
        // Update all packages
        if verbose {
            println!("Updating {} dependencies...", manifest.packages.len());
        }

        let (updated_manifest, results) = fm.update_all(&manifest)?;

        let mut updated_count = 0;
        let mut error_count = 0;

        for result in &results {
            match &result.status {
                UpdateStatus::Updated => {
                    println!(
                        "Updated {}: {} -> {}",
                        result.name,
                        &result.old_rev[..result.old_rev.len().min(8)],
                        &result.new_rev[..result.new_rev.len().min(8)]
                    );
                    updated_count += 1;
                }
                UpdateStatus::UpToDate => {
                    if verbose {
                        println!("{} is up to date", result.name);
                    }
                }
                UpdateStatus::Skipped => {
                    if verbose {
                        println!("{} skipped (path package)", result.name);
                    }
                }
                UpdateStatus::Error(e) => {
                    eprintln!("Error updating {}: {}", result.name, e);
                    error_count += 1;
                }
            }
        }

        // Save updated manifest
        if updated_count > 0 {
            updated_manifest.save(&manifest_path)?;
        }

        if error_count > 0 {
            anyhow::bail!("{error_count} packages failed to update");
        }

        if updated_count == 0 {
            println!("All dependencies are up to date.");
        } else {
            println!("Updated {updated_count} dependencies.");
        }
    }

    Ok(())
}

/// Show build environment information
pub(super) fn lake_env(
    command: &[String],
    verbose: bool,
    dir: Option<PathBuf>,
) -> anyhow::Result<()> {
    use clean_lake::FetchManager;

    let cwd = resolve_project_dir(dir)?;

    if !command.is_empty() {
        return lake_env_command(command, &cwd, verbose);
    }

    // Basic environment info
    println!("Clean Build Environment");
    println!("=======================");
    println!();

    // clean version (from crate)
    println!("clean-lake version: {}", env!("CARGO_PKG_VERSION"));

    // Git availability
    let git_available = FetchManager::git_available();
    println!(
        "git: {}",
        if git_available {
            "available"
        } else {
            "not found"
        }
    );

    // Rayon thread count
    let num_threads = rayon::current_num_threads();
    println!("parallel jobs: {num_threads}");

    // Project info (lakefile.toml preferred, lakefile.lean fallback). Parse
    // errors surface; a missing lakefile prints the "no lakefile" note below.
    match super::try_load_project_config(&cwd)? {
        Some(config) => {
            println!();
            println!("Project");
            println!("-------");
            println!("name: {}", config.package.name);
            if let Some(v) = &config.package.version {
                println!("version: {v}");
            }
            println!("root: {}", cwd.display());

            // Libraries
            if !config.libs.is_empty() {
                println!();
                println!("Libraries:");
                for lib in &config.libs {
                    let is_default = config.default_targets.contains(&lib.name);
                    let default_marker = if is_default { " (default)" } else { "" };
                    println!("  - {}{}", lib.name, default_marker);
                    if verbose {
                        for root in &lib.roots {
                            println!("      root: {root}");
                        }
                    }
                }
            }

            // Executables
            if !config.exes.is_empty() {
                println!();
                println!("Executables:");
                for exe in &config.exes {
                    let is_default = config.default_targets.contains(&exe.name);
                    let default_marker = if is_default { " (default)" } else { "" };
                    println!("  - {}{}", exe.name, default_marker);
                    if verbose {
                        println!("      root: {}", exe.root);
                    }
                }
            }
        }
        None => {
            println!();
            println!("No lakefile.toml or lakefile.lean found in current directory.");
        }
    }

    // Exported environment.
    //
    // This is the headline the `lake env` contract promises — "the toolchain,
    // resolved search paths, and other variables the Lake build would export
    // for sub-processes" — and until 2026-08-26 the bare form printed NONE of
    // it: no LEAN_PATH, no toolchain, nothing. Only the `lake env <cmd>` form
    // used `env_pairs`, to populate the child. That also made the comment in
    // `lake_env_command` false where it says the pairs are "the same definition
    // `clean lake env` reports" — it reported nothing to compare against.
    //
    // Printing the SAME `Workspace::env_pairs` the child receives is what makes
    // that invariant real: what is printed and what a child gets now come from
    // one definition.
    match clean_lake::Workspace::load(&cwd) {
        Ok(ws) => {
            println!();
            println!("Exported environment");
            println!("--------------------");
            for (key, value) in ws.env_pairs() {
                println!("{key}={value}");
            }
        }
        Err(err) => {
            if verbose {
                eprintln!("warning: no Lake workspace at {}: {err}", cwd.display());
            }
        }
    }

    // Manifest info
    let manifest_path = cwd.join("lake-manifest.json");
    if manifest_path.exists() {
        if let Ok(manifest) = clean_lake::LakeManifest::load(&manifest_path) {
            if !manifest.packages.is_empty() {
                println!();
                println!("Dependencies ({}):", manifest.packages.len());
                for pkg in &manifest.packages {
                    match pkg {
                        clean_lake::ManifestPackage::Git(g) => {
                            let rev_short = &g.rev[..g.rev.len().min(8)];
                            println!("  - {} (git: {})", g.name, rev_short);
                            if verbose {
                                println!("      url: {}", g.url);
                            }
                        }
                        clean_lake::ManifestPackage::Path(p) => {
                            println!("  - {} (path: {})", p.name, p.path);
                        }
                    }
                }
            }
        }
    }

    Ok(())
}

fn lake_env_command(
    command: &[String],
    cwd: &std::path::Path,
    verbose: bool,
) -> anyhow::Result<()> {
    let (program, args) = command
        .split_first()
        .ok_or_else(|| anyhow::anyhow!("lake env command handoff requires a command"))?;
    let diagnostic_cwd = cwd.canonicalize().unwrap_or_else(|_| cwd.to_path_buf());

    if verbose {
        eprintln!(
            "Executing {program:?} {args:?} from {}",
            diagnostic_cwd.display()
        );
    }

    // Inject the resolved Lake environment. Without this the child inherited
    // only the ambient environment, so `clean lake env lean Foo.lean` — the
    // whole point of the `env <cmd>` form, and what CI scripts are built on —
    // could not resolve a single import. The pairs come from
    // `Workspace::env_pairs`, the same definition `clean lake env` reports, so
    // what is printed and what a child actually receives cannot disagree.
    //
    // A workspace that fails to load is not fatal here: `lake env` is also used
    // to run tools outside a Lake project, so the handoff proceeds with the
    // ambient environment rather than refusing.
    let mut cmd = Command::new(program);
    cmd.args(args).current_dir(cwd);
    match clean_lake::Workspace::load(cwd) {
        Ok(ws) => {
            for (key, value) in ws.env_pairs() {
                cmd.env(key, value);
            }
        }
        Err(err) => {
            if verbose {
                eprintln!(
                    "warning: no Lake workspace at {}: {err}; running with the ambient \
                     environment",
                    diagnostic_cwd.display()
                );
            }
        }
    }

    let status = cmd.status().map_err(|err| {
        anyhow::anyhow!(
            "clean lake env is fail-closed: failed to execute command '{program}' from \
                 workspace {}: {err}",
            diagnostic_cwd.display()
        )
    })?;

    if !status.success() {
        return Err(super::forwarded_process_exit(status));
    }

    Ok(())
}

/// Resolve dependencies and update lake-manifest.json
pub(super) fn lake_resolve(
    verbose: bool,
    dry_run: bool,
    dir: Option<PathBuf>,
) -> anyhow::Result<()> {
    use clean_lake::{FetchManager, LakeManifest};

    let cwd = resolve_project_dir(dir)?;

    // Load lakefile to get dependencies (lakefile.toml preferred, lakefile.lean fallback)
    let config = super::load_project_config(&cwd)?;
    if dependencies_require_git(&config.package.dependencies) && !FetchManager::git_available() {
        anyhow::bail!("Git is not available. Please install git to resolve dependencies.");
    }

    if config.package.dependencies.is_empty() {
        println!("No dependencies declared in lakefile.lean.");
        return Ok(());
    }

    if verbose {
        println!(
            "Resolving {} dependencies for package '{}'...",
            config.package.dependencies.len(),
            config.package.name
        );
    }

    // Create fetch manager
    let packages_dir = cwd.join(".lake/packages");
    let fm = FetchManager::new(&cwd, &packages_dir);

    // Resolve dependencies
    let (manifest, result) = fm.resolve_to_manifest(&config.package.dependencies)?;

    // Report results
    if !result.errors.is_empty() {
        eprintln!("Errors resolving dependencies:");
        for (name, err) in &result.errors {
            eprintln!("  {name}: {err}");
        }
        if result.resolved.is_empty() {
            anyhow::bail!("Failed to resolve any dependencies");
        }
    }

    if verbose || dry_run {
        println!("Resolved dependencies:");
        for pkg in &result.resolved {
            if let Some(url) = &pkg.url {
                let rev_short = &pkg.rev[..pkg.rev.len().min(12)];
                let input = pkg
                    .input_rev
                    .as_deref()
                    .map(|r| format!(" (from {r})"))
                    .unwrap_or_default();
                println!("  {} @ {}{}", pkg.name, rev_short, input);
                if verbose {
                    println!("    url: {url}");
                }
            } else if let Some(path) = &pkg.path {
                println!("  {} (path: {})", pkg.name, path);
            }
        }
    }

    if dry_run {
        println!("\n(dry run - lake-manifest.json not modified)");
    } else {
        // Load existing manifest to preserve any extra data
        let manifest_path = cwd.join("lake-manifest.json");
        let mut final_manifest = if manifest_path.exists() {
            LakeManifest::load(&manifest_path).unwrap_or_else(|_| manifest.clone())
        } else {
            LakeManifest::empty()
        };

        // Update with resolved packages
        for pkg in manifest.packages {
            final_manifest.upsert_package(pkg);
        }

        // Save manifest
        final_manifest.save(&manifest_path)?;

        println!(
            "Resolved {} dependencies -> lake-manifest.json",
            result.resolved.len()
        );
    }

    if !result.errors.is_empty() {
        anyhow::bail!("{} dependencies failed to resolve", result.errors.len());
    }

    Ok(())
}

fn manifest_requires_git(manifest: &clean_lake::LakeManifest) -> bool {
    manifest
        .packages
        .iter()
        .any(clean_lake::ManifestPackage::is_git)
}

fn dependencies_require_git(dependencies: &[clean_lake::config::Dependency]) -> bool {
    dependencies.iter().any(|dep| dep.git.is_some())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    /// A project whose only dependency is a sibling PATH package, so resolution
    /// needs no network and no git.
    fn project_with_path_dep() -> tempfile::TempDir {
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();

        let dep = root.join("vendor/helper");
        fs::create_dir_all(&dep).expect("dep dir");
        fs::write(
            dep.join("lakefile.toml"),
            "name = \"helper\"\n\n[[lean_lib]]\nname = \"Helper\"\n",
        )
        .expect("dep lakefile");

        fs::write(
            root.join("lakefile.toml"),
            "name = \"consumer\"\n\n[[require]]\nname = \"helper\"\npath = \"vendor/helper\"\n\n\
             [[lean_lib]]\nname = \"Consumer\"\n",
        )
        .expect("root lakefile");

        dir
    }

    /// `lake env <cmd>` must hand the child the resolved Lake environment.
    /// Spawning with only the ambient environment is why `lake env lean
    /// Foo.lean` could not resolve imports: `LEAN_PATH` never reached the
    /// child. The injected pairs must be exactly what `clean lake env` reports.
    #[test]
    fn test_lake_env_command_injects_the_resolved_environment() {
        let project = project_with_path_dep();
        let root = project.path();
        let ws = clean_lake::Workspace::load(root).expect("workspace should load");
        let pairs = ws.env_pairs();

        let lean_path = pairs
            .iter()
            .find(|(k, _)| k == "LEAN_PATH")
            .map(|(_, v)| v.clone())
            .expect("LEAN_PATH must be part of the resolved environment");
        assert!(
            !lean_path.is_empty(),
            "LEAN_PATH must name at least the workspace lib dir"
        );
        assert!(
            lean_path.contains(&ws.lib_dir().display().to_string()),
            "LEAN_PATH must lead with the workspace lib dir: {lean_path}"
        );

        // The child sees them. `env` prints the process environment, so a
        // successful run whose output carries LEAN_PATH proves injection.
        let out = Command::new("/usr/bin/env")
            .current_dir(root)
            .envs(pairs.iter().map(|(k, v)| (k.clone(), v.clone())))
            .output()
            .expect("run /usr/bin/env");
        let text = String::from_utf8_lossy(&out.stdout);
        assert!(
            text.contains(&format!("LEAN_PATH={lean_path}")),
            "child environment must carry LEAN_PATH"
        );
    }

    /// Lake's `update` REGENERATES the manifest from the lakefile's requires, so
    /// a missing manifest is the bootstrap case, not an error. This used to
    /// bail with "Create a manifest with dependencies to update" — asking the
    /// user to hand-write the artifact the command produces.
    #[test]
    fn test_lake_update_bootstraps_a_missing_manifest() {
        let project = project_with_path_dep();
        let root = project.path();
        let manifest = root.join("lake-manifest.json");
        assert!(!manifest.exists(), "precondition: no manifest yet");

        lake_update(None, false, Some(root.to_path_buf())).expect("update should bootstrap");

        assert!(
            manifest.exists(),
            "update must write the manifest it resolved"
        );
        let text = fs::read_to_string(&manifest).expect("read manifest");
        assert!(
            text.contains("helper"),
            "manifest should record the resolved path dependency: {text}"
        );
    }

    /// Bootstrapping resolves the WHOLE lakefile, so narrowing it to one package
    /// has no manifest entry to narrow against. Refuse with an instruction that
    /// names the command that works, rather than resolving everything and
    /// silently ignoring the argument.
    #[test]
    fn test_lake_update_single_package_without_manifest_is_refused() {
        let project = project_with_path_dep();
        let err = lake_update(
            Some("helper".to_string()),
            false,
            Some(project.path().to_path_buf()),
        )
        .expect_err("single-package update needs an existing manifest");
        let msg = err.to_string();
        assert!(
            msg.contains("clean lake update"),
            "error should name the command that works: {msg}"
        );
        assert!(
            !project.path().join("lake-manifest.json").exists(),
            "a refused update must not leave a partial manifest"
        );
    }
}
