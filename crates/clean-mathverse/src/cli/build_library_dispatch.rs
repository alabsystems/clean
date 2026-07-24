// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean mathverse build-library` — orchestrator that produces a
//! downloader-compatible `mathverse-library-v*.tar.zst` release from configured
//! upstream proof system sources.
//!
//! Pipeline:
//!
//! 1. Verify (and optionally install) external prerequisites
//!    (`git`, `cargo`, `b3sum`, `zstd`).
//! 2. Clone the upstream proof system sources configured in
//!    `data/mathverse_sources.toml` via `scripts/download_all_libraries.sh`
//!    (includes Lean 3 mathlib3).
//! 3. Convert sources to `.mathverse` shards via `mathverse_convert all`.
//! 4. Package shards + a fresh blake3 manifest into
//!    `mathverse-library-v*.tar.zst` via `scripts/package_mathverse_release.sh`.
//! 5. Optionally `gh release upload` the archive + manifest.
//!
//! Each stage is independently skippable so the command supports partial
//! rebuilds (re-package without re-downloading, publish an already-packaged
//! archive, etc.).
//!
//! Lean 3 note: the `lean3_import.rs` module reads `.lean` source text
//! directly via a Pratt-style type parser — it does NOT require a Lean 3
//! compiler or runtime to be installed. Only the source files (mathlib3) are
//! needed.

use std::path::{Path, PathBuf};
use std::process::Command;

use crate::cli::{BuildLibraryArgs, MathverseCliError};

/// External tools the build-library pipeline depends on.
///
/// Each entry: (program name on PATH, suggested install hint for the user).
const REQUIRED_TOOLS: &[(&str, &str)] = &[
    ("git", "brew install git  /  apt install git"),
    ("cargo", "https://rustup.rs"),
    ("b3sum", "brew install b3sum  /  cargo install b3sum"),
    ("zstd", "brew install zstd  /  apt install zstd"),
];

/// Additional tools required only when `--publish` is set.
const PUBLISH_REQUIRED_TOOLS: &[(&str, &str)] =
    &[("gh", "brew install gh  /  https://cli.github.com")];

/// Stage-1: verify (and optionally install) external prereqs.
///
/// Returns the first missing prerequisite on the relevant list, mapped to
/// [`MathverseCliError::MissingPrereq`]. If `--auto-install-prereqs` is set, runs
/// the system package manager (Homebrew on macOS, apt-get on Linux) before
/// reporting any missing tool.
fn check_prereqs(args: &BuildLibraryArgs) -> Result<(), MathverseCliError> {
    let mut required: Vec<(&str, &str)> = REQUIRED_TOOLS.to_vec();
    if args.publish {
        required.extend(PUBLISH_REQUIRED_TOOLS.iter().copied());
    }

    let missing: Vec<(&str, &str)> = required
        .iter()
        .filter(|(tool, _)| which(tool).is_none())
        .copied()
        .collect();

    if missing.is_empty() {
        return Ok(());
    }

    if args.auto_install_prereqs {
        for (tool, _) in &missing {
            install_tool(tool)?;
        }
        // Re-check after install.
        for (tool, hint) in &required {
            if which(tool).is_none() {
                return Err(MathverseCliError::MissingPrereq {
                    tool,
                    install_hint: (*hint).to_string(),
                });
            }
        }
        return Ok(());
    }

    let (tool, hint) = missing[0];
    Err(MathverseCliError::MissingPrereq {
        tool,
        install_hint: hint.to_string(),
    })
}

/// Return the absolute path to `tool` if it is on `$PATH`, otherwise `None`.
///
/// Pure-Rust replacement for the `which` crate so we don't add a dependency
/// just for this lookup. Looks at every entry in `$PATH` for an executable
/// regular file matching `tool` (no extension handling — POSIX semantics).
fn which(tool: &str) -> Option<PathBuf> {
    let path_var = std::env::var_os("PATH")?;
    for dir in std::env::split_paths(&path_var) {
        let candidate = dir.join(tool);
        if candidate.is_file() {
            // Best-effort executable check; on most systems this is enough.
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                if let Ok(meta) = std::fs::metadata(&candidate) {
                    if meta.permissions().mode() & 0o111 != 0 {
                        return Some(candidate);
                    }
                }
            }
            #[cfg(not(unix))]
            {
                return Some(candidate);
            }
        }
    }
    None
}

/// Install a single tool using the best available system package manager.
fn install_tool(tool: &str) -> Result<(), MathverseCliError> {
    let installers: &[(&str, &[&str])] = if cfg!(target_os = "macos") {
        &[("brew", &["install"])]
    } else {
        &[
            ("apt-get", &["install", "-y"]),
            ("dnf", &["install", "-y"]),
            ("pacman", &["-S", "--noconfirm"]),
        ]
    };

    for (pm, base_args) in installers {
        if which(pm).is_none() {
            continue;
        }
        let mut cmd = Command::new(pm);
        cmd.args(*base_args).arg(tool);
        eprintln!("[build-library] installing prereq `{tool}` via `{pm}`");
        let status = cmd
            .status()
            .map_err(|e| MathverseCliError::BuildLibraryStage {
                stage: "prereqs",
                message: format!("failed to spawn `{pm} install {tool}`: {e}"),
            })?;
        if status.success() {
            return Ok(());
        }
        return Err(MathverseCliError::BuildLibraryStage {
            stage: "prereqs",
            message: format!("`{pm} install {tool}` exited with {status}"),
        });
    }
    Err(MathverseCliError::BuildLibraryStage {
        stage: "prereqs",
        message: format!(
            "no supported package manager found to install `{tool}`; install it manually"
        ),
    })
}

/// Stage-2: clone upstream proof system source repos.
///
/// Runs `scripts/download_all_libraries.sh <data-dir>`. The script is
/// idempotent — it clones missing repos and skips ones already present.
fn run_download(data_dir: &Path) -> Result<(), MathverseCliError> {
    let script = repo_root()?.join("scripts/download_all_libraries.sh");
    if !script.exists() {
        return Err(MathverseCliError::BuildLibraryStage {
            stage: "download",
            message: format!(
                "scripts/download_all_libraries.sh not found at `{}` — is this the clean repo?",
                script.display()
            ),
        });
    }
    eprintln!(
        "[build-library] cloning upstream sources via `{} {}`",
        script.display(),
        data_dir.display()
    );
    let status = Command::new("bash")
        .arg(&script)
        .arg(data_dir)
        .status()
        .map_err(|e| MathverseCliError::BuildLibraryStage {
            stage: "download",
            message: format!("failed to spawn download script: {e}"),
        })?;
    if !status.success() {
        return Err(MathverseCliError::BuildLibraryStage {
            stage: "download",
            message: format!("download script exited with {status}"),
        });
    }
    Ok(())
}

/// Stage-3: run the conversion pipeline.
///
/// `download_all_libraries.sh` invokes `mathverse_convert all` at the end of its
/// own run, so when `--skip-download` is set we still need to convert
/// separately. When download just ran, this step re-runs convert to make
/// sure outputs are fresh against any new shards.
fn run_convert(data_dir: &Path) -> Result<(), MathverseCliError> {
    let bin = repo_root()?.join("target/release/mathverse_convert");
    if !bin.exists() {
        eprintln!("[build-library] building `mathverse_convert` (release profile)…");
        let build = Command::new("cargo")
            .args([
                "build",
                "--locked",
                "--release",
                "-p",
                "clean-mathverse",
                "--bin",
                "mathverse_convert",
                "--message-format=short",
            ])
            .current_dir(repo_root()?)
            .status()
            .map_err(|e| MathverseCliError::BuildLibraryStage {
                stage: "convert",
                message: format!("failed to spawn cargo build: {e}"),
            })?;
        if !build.success() {
            return Err(MathverseCliError::BuildLibraryStage {
                stage: "convert",
                message: format!("`cargo build` exited with {build}"),
            });
        }
    }
    eprintln!(
        "[build-library] running `{} all {}`",
        bin.display(),
        data_dir.display()
    );
    let status = Command::new(&bin)
        .arg("all")
        .arg(data_dir)
        .status()
        .map_err(|e| MathverseCliError::BuildLibraryStage {
            stage: "convert",
            message: format!("failed to spawn mathverse_convert: {e}"),
        })?;
    if !status.success() {
        return Err(MathverseCliError::BuildLibraryStage {
            stage: "convert",
            message: format!("mathverse_convert all exited with {status}"),
        });
    }
    Ok(())
}

/// Stage-4: package the shards into a release archive.
///
/// Calls `scripts/package_mathverse_release.sh <shard-dir> --output-dir <out>`,
/// which produces `mathverse-library-v<workspace-version>.tar.zst` plus the
/// `mathverse-manifest.json` it consumed.
fn run_package(args: &BuildLibraryArgs) -> Result<PathBuf, MathverseCliError> {
    let script = repo_root()?.join("scripts/package_mathverse_release.sh");
    if !script.exists() {
        return Err(MathverseCliError::BuildLibraryStage {
            stage: "package",
            message: format!(
                "scripts/package_mathverse_release.sh not found at `{}`",
                script.display()
            ),
        });
    }
    let shard_dir = args.data_dir.join("mathverse-shards");
    if !shard_dir.exists() {
        return Err(MathverseCliError::BuildLibraryStage {
            stage: "package",
            message: format!(
                "shard directory `{}` not found — run convert first or pass --data-dir to a tree with mathverse-shards/",
                shard_dir.display()
            ),
        });
    }
    let output_dir = absolute_path(&args.package_output_dir);
    std::fs::create_dir_all(&output_dir).map_err(|e| MathverseCliError::BuildLibraryStage {
        stage: "package",
        message: format!(
            "failed to create output dir `{}`: {e}",
            output_dir.display()
        ),
    })?;
    eprintln!(
        "[build-library] packaging `{}` → `{}`",
        shard_dir.display(),
        output_dir.display()
    );
    let status = Command::new("bash")
        .arg(&script)
        .arg(&shard_dir)
        .arg(format!("--output-dir={}", output_dir.display()))
        .status()
        .map_err(|e| MathverseCliError::BuildLibraryStage {
            stage: "package",
            message: format!("failed to spawn package script: {e}"),
        })?;
    if !status.success() {
        return Err(MathverseCliError::BuildLibraryStage {
            stage: "package",
            message: format!("package script exited with {status}"),
        });
    }
    let version = workspace_version()?;
    let archive = output_dir.join(format!("mathverse-library-v{version}.tar.zst"));
    if !archive.exists() {
        return Err(MathverseCliError::BuildLibraryStage {
            stage: "package",
            message: format!(
                "package script reported success but archive `{}` is missing",
                archive.display()
            ),
        });
    }
    Ok(archive)
}

/// Stage-5: upload the archive + manifest to a GitHub Release.
///
/// Uses `gh release upload --clobber` to overwrite any existing assets on the
/// target tag. Creates the release first if it doesn't exist.
fn run_publish(args: &BuildLibraryArgs, archive: &Path) -> Result<(), MathverseCliError> {
    let version = workspace_version()?;
    let tag = args
        .tag
        .clone()
        .unwrap_or_else(|| format!("mathverse-v{version}"));
    let manifest = args
        .data_dir
        .join("mathverse-shards/mathverse-manifest.json");
    if !manifest.exists() {
        return Err(MathverseCliError::BuildLibraryStage {
            stage: "publish",
            message: format!("manifest `{}` not found", manifest.display()),
        });
    }

    // Check whether the release already exists.
    let view = Command::new("gh")
        .args(["release", "view", &tag, "--repo", &args.repo])
        .output()
        .map_err(|e| MathverseCliError::BuildLibraryStage {
            stage: "publish",
            message: format!("failed to spawn gh: {e}"),
        })?;

    if !view.status.success() {
        eprintln!(
            "[build-library] creating release `{tag}` in `{}`",
            args.repo
        );
        let create = Command::new("gh")
            .args([
                "release",
                "create",
                &tag,
                "--repo",
                &args.repo,
                "--title",
                &format!("Mathverse Library v{version}"),
                "--notes",
                "Built end-to-end via `clean mathverse build-library`. See \
                 docs/MATHVERSE_RELEASE_PROCESS.md.",
            ])
            .status()
            .map_err(|e| MathverseCliError::BuildLibraryStage {
                stage: "publish",
                message: format!("failed to spawn `gh release create`: {e}"),
            })?;
        if !create.success() {
            return Err(MathverseCliError::BuildLibraryStage {
                stage: "publish",
                message: format!("`gh release create {tag}` exited with {create}"),
            });
        }
    } else {
        eprintln!("[build-library] release `{tag}` exists; uploading with --clobber");
    }

    let upload = Command::new("gh")
        .args(["release", "upload", &tag, "--repo", &args.repo, "--clobber"])
        .arg(archive)
        .arg(&manifest)
        .status()
        .map_err(|e| MathverseCliError::BuildLibraryStage {
            stage: "publish",
            message: format!("failed to spawn `gh release upload`: {e}"),
        })?;
    if !upload.success() {
        return Err(MathverseCliError::BuildLibraryStage {
            stage: "publish",
            message: format!("`gh release upload {tag}` exited with {upload}"),
        });
    }
    Ok(())
}

// -- helpers ------------------------------------------------------------------

/// Locate the repository root by walking up from the current dir looking for
/// `Cargo.toml` with a `[workspace]` table.
fn repo_root() -> Result<PathBuf, MathverseCliError> {
    let mut cur = std::env::current_dir().map_err(|e| MathverseCliError::BuildLibraryStage {
        stage: "prereqs",
        message: format!("failed to read current dir: {e}"),
    })?;
    loop {
        let manifest = cur.join("Cargo.toml");
        if manifest.exists() {
            if let Ok(contents) = std::fs::read_to_string(&manifest) {
                if contents.contains("[workspace]") {
                    return Ok(cur);
                }
            }
        }
        if !cur.pop() {
            break;
        }
    }
    Err(MathverseCliError::BuildLibraryStage {
        stage: "prereqs",
        message: "could not locate workspace root (no Cargo.toml with [workspace] found in any \
                  parent of the current dir) — run from inside the clean checkout"
            .to_string(),
    })
}

/// Read the workspace version from the root `Cargo.toml`.
fn workspace_version() -> Result<String, MathverseCliError> {
    let manifest = repo_root()?.join("Cargo.toml");
    let contents =
        std::fs::read_to_string(&manifest).map_err(|e| MathverseCliError::BuildLibraryStage {
            stage: "package",
            message: format!("failed to read `{}`: {e}", manifest.display()),
        })?;
    // Naive parse: find `[workspace.package]` then the first `version = "X"`.
    let mut in_section = false;
    for line in contents.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with('[') {
            in_section = trimmed == "[workspace.package]";
            continue;
        }
        if in_section {
            if let Some(rest) = trimmed.strip_prefix("version") {
                if let Some(eq_rest) = rest.trim_start().strip_prefix('=') {
                    return Ok(eq_rest.trim().trim_matches('"').to_string());
                }
            }
        }
    }
    Err(MathverseCliError::BuildLibraryStage {
        stage: "package",
        message: format!(
            "could not parse workspace version from `{}`",
            manifest.display()
        ),
    })
}

/// Convert a path to absolute (relative paths are resolved against cwd).
fn absolute_path(p: &Path) -> PathBuf {
    if p.is_absolute() {
        p.to_path_buf()
    } else {
        std::env::current_dir()
            .map(|cwd| cwd.join(p))
            .unwrap_or_else(|_| p.to_path_buf())
    }
}

/// Entry point invoked from [`crate::cli::run`].
pub(super) fn cmd_build_library(args: BuildLibraryArgs) -> Result<(), MathverseCliError> {
    eprintln!("[build-library] data-dir = {}", args.data_dir.display());

    // Stage 1: prereqs.
    if !args.skip_prereqs {
        eprintln!("[build-library] stage 1/5: checking prerequisites…");
        check_prereqs(&args)?;
    } else {
        eprintln!("[build-library] stage 1/5: SKIPPED (--skip-prereqs)");
    }

    // Stage 2: download upstream sources.
    if !args.skip_download {
        eprintln!("[build-library] stage 2/5: downloading upstream sources…");
        run_download(&args.data_dir)?;
    } else {
        eprintln!("[build-library] stage 2/5: SKIPPED (--skip-download)");
    }

    // Stage 3: convert sources to shards.
    if !args.skip_convert {
        eprintln!("[build-library] stage 3/5: running mathverse_convert all…");
        run_convert(&args.data_dir)?;
    } else {
        eprintln!("[build-library] stage 3/5: SKIPPED (--skip-convert)");
    }

    // Stage 4: package shards into a release archive.
    let archive = if !args.skip_package {
        eprintln!("[build-library] stage 4/5: packaging release archive…");
        Some(run_package(&args)?)
    } else {
        eprintln!("[build-library] stage 4/5: SKIPPED (--skip-package)");
        None
    };

    // Stage 5: publish (optional).
    if args.publish {
        let archive = archive
            .as_deref()
            .ok_or_else(|| MathverseCliError::BuildLibraryStage {
                stage: "publish",
                message:
                    "cannot publish without a packaged archive — re-run without --skip-package"
                        .to_string(),
            })?;
        eprintln!("[build-library] stage 5/5: publishing to GitHub Release…");
        run_publish(&args, archive)?;
    } else {
        eprintln!("[build-library] stage 5/5: SKIPPED (no --publish)");
    }

    eprintln!("[build-library] complete");
    if let Some(archive) = archive {
        eprintln!("[build-library] archive: {}", archive.display());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn which_finds_cargo() {
        // cargo is required for the build that's running this test.
        assert!(
            which("cargo").is_some(),
            "cargo should be on PATH for tests"
        );
    }

    #[test]
    fn which_returns_none_for_missing() {
        assert!(which("definitely-not-a-real-binary-xyz-12345").is_none());
    }

    #[test]
    fn absolute_path_preserves_absolute() {
        let abs = PathBuf::from("/tmp/foo");
        assert_eq!(absolute_path(&abs), abs);
    }

    #[test]
    fn absolute_path_resolves_relative() {
        let rel = PathBuf::from("foo");
        let result = absolute_path(&rel);
        assert!(result.is_absolute());
        assert!(result.ends_with("foo"));
    }

    #[test]
    fn workspace_version_is_parseable() {
        // Should find a version string in the workspace Cargo.toml.
        let v = workspace_version().expect("workspace version should parse");
        assert!(!v.is_empty());
        // Sanity: must look like a semver string.
        assert!(v.chars().any(|c| c.is_ascii_digit()));
    }
}
