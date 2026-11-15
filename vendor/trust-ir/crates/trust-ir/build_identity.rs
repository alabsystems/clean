// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Source-identity resolution for `trust_ir::BUILD_IDENTITY` (roadmap WS8.4).
//!
//! This file is the whole logic of `crates/trust-ir/build.rs`, split out so the
//! CLI tests can drive the exact code the build script runs (`#[path]`-included
//! there) against a controlled environment and a scratch checkout. The build
//! script only prints what [`build_directives`] returns, or panics with its
//! error.
//!
//! The rule, in order:
//!
//! 1. **Packaging override.** `ALAB_BUILD_GIT_SHA` (12–40 lowercase hex) plus
//!    `ALAB_BUILD_GIT_DIRTY` (`0` or `1`), set by packaging and by the Trust
//!    bootstrap from the gitlink, which is exact. A malformed value — including
//!    one that is not valid Unicode — or one of the pair without the other
//!    FAILS the build naming the variable: it is a packaging bug and must be
//!    loud, never a silent fall-through to git.
//!
//!    The roadmap drafted these as `TRUST_BUILD_GIT_SHA` / `_DIRTY`. That
//!    spelling cannot work: verified Targo (`targo trust build`) removes EVERY
//!    `TRUST_*` variable from a build script's environment
//!    (`scrub_verified_build_script_authority_env`), so on the lane this stack
//!    is ratcheting toward the override would silently vanish and the build
//!    would fall through to `.local`/`unknown`. The `TRUST_*` spelling is
//!    therefore REFUSED wherever it is visible (the unverified and bootstrap
//!    lanes), naming the replacement, so a packager who followed the draft
//!    finds out on the first build instead of shipping unattested binaries.
//! 2. **Own-checkout fallback.** `git rev-parse HEAD`, but only when
//!    `git rev-parse --show-toplevel` is this crate's OWN repository root (the
//!    directory holding `crates/trust-ir/Cargo.toml`) and that root's `HEAD`
//!    tree records this crate's manifest. Without that check a copy of the
//!    crate vendored inside an unrelated repository would report the ENCLOSING
//!    repository's sha with confidence. The fallback cannot attest the working
//!    tree, so its suffix is always `.local` — it never yields an unqualified
//!    `g<sha>`.
//! 3. **Otherwise `unknown`.** A missing or failing `git` never fails the
//!    build.
//!
//! Std only: the zero-dependency `trust-ir` crate gains no dependency, and a
//! build script is a host unit, outside the verified artifact.

use std::ffi::OsStr;
use std::path::{Path, PathBuf};
use std::process::Command;

/// Packaging override: the source commit sha (12–40 lowercase hex).
pub const ENV_GIT_SHA: &str = "ALAB_BUILD_GIT_SHA";
/// Packaging override: `0` for a clean tree, `1` for a dirty one.
pub const ENV_GIT_DIRTY: &str = "ALAB_BUILD_GIT_DIRTY";

/// The roadmap's draft spelling of the override, paired with its replacement.
/// Verified Targo scrubs every `TRUST_*` variable from a build script, so this
/// spelling would be silently dropped on the verified lane; wherever it IS
/// visible it fails the build, naming the replacement.
pub const REFUSED_ENV: &[(&str, &str)] = &[
    ("TRUST_BUILD_GIT_SHA", ENV_GIT_SHA),
    ("TRUST_BUILD_GIT_DIRTY", ENV_GIT_DIRTY),
];

// The `rustc-env` keys below deliberately avoid the `TRUST_` prefix:
// authenticated Targo refuses a build script that sets a `TRUST_*` (or
// `RUSTC_*`) variable for rustc, because those are process-authority channels.
// These are self-provenance stamps read only by `env!` in `src/build_info.rs`.

/// `rustc-env` key carrying the rendered source label (`g<12-hex>`,
/// `g<12-hex>.dirty`, `g<12-hex>.local` or `unknown`).
pub const OUT_SOURCE: &str = "TIR_BUILD_SOURCE";
/// `rustc-env` key carrying the full sha the label abbreviates, or `unknown`.
pub const OUT_SHA: &str = "TIR_BUILD_GIT_SHA";
/// `rustc-env` key carrying how the sha was attested (see [`Attestation`]).
pub const OUT_ATTESTATION: &str = "TIR_BUILD_ATTESTATION";

/// Hex digits of the sha shown in the version string.
pub const SHORT_SHA_LEN: usize = 12;

/// The crate's position inside its own repository.
pub const CRATE_REL_PATH: &[&str] = &["crates", "trust-ir"];

/// Environment variables that would redirect a `git` child to another
/// repository. They are cleared so the checkout the crate sits in is the only
/// thing consulted.
const GIT_REDIRECT_VARS: &[&str] = &[
    "GIT_DIR",
    "GIT_WORK_TREE",
    "GIT_COMMON_DIR",
    "GIT_INDEX_FILE",
    "GIT_OBJECT_DIRECTORY",
    "GIT_ALTERNATE_OBJECT_DIRECTORIES",
    "GIT_NAMESPACE",
    // Command-line-equivalent config (`core.worktree`, `include.path`, ...)
    // smuggled through the environment.
    "GIT_CONFIG_PARAMETERS",
    "GIT_CONFIG_COUNT",
];

/// Read one build-environment variable for [`resolve`]. A value that is not
/// valid Unicode is returned lossily (U+FFFD in place of the bad bytes) so it
/// FAILS the override's syntax check by name, rather than reading as unset —
/// `std::env::var(..).ok()` would silently turn it into a git fall-through.
pub fn env_value(value: Option<std::ffi::OsString>) -> Option<String> {
    value.map(|v| v.to_string_lossy().into_owned())
}

/// How the source sha was established.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Attestation {
    /// Packaging override, working tree attested clean.
    PackagedClean,
    /// Packaging override, working tree attested dirty.
    PackagedDirty,
    /// Own-checkout `git` fallback; the working tree is NOT attested.
    Local,
    /// Neither source was available.
    Unknown,
}

impl Attestation {
    /// Wire spelling passed to the compiled crate.
    pub fn as_str(self) -> &'static str {
        match self {
            Attestation::PackagedClean => "packaged-clean",
            Attestation::PackagedDirty => "packaged-dirty",
            Attestation::Local => "local",
            Attestation::Unknown => "unknown",
        }
    }
}

/// The resolved source identity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceIdentity {
    /// Full sha as reported by the source, or `None` when unknown.
    pub sha: Option<String>,
    /// How it was attested.
    pub attestation: Attestation,
}

impl SourceIdentity {
    /// The SemVer build-metadata label: `g<12-hex>[.dirty|.local]` or
    /// `unknown`. Never an unqualified `g<sha>` unless packaging attested a
    /// clean tree.
    pub fn label(&self) -> String {
        match (&self.sha, self.attestation) {
            (Some(sha), Attestation::PackagedClean) => format!("g{}", short(sha)),
            (Some(sha), Attestation::PackagedDirty) => format!("g{}.dirty", short(sha)),
            (Some(sha), Attestation::Local) => format!("g{}.local", short(sha)),
            _ => "unknown".to_string(),
        }
    }
}

fn short(sha: &str) -> &str {
    &sha[..SHORT_SHA_LEN.min(sha.len())]
}

fn is_lower_hex(s: &str, min: usize, max: usize) -> bool {
    (min..=max).contains(&s.len())
        && s.bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

/// Resolve the source identity. `env` reads the build's environment, `crate_dir`
/// is `CARGO_MANIFEST_DIR`, `git` is the program to run for the fallback.
///
/// # Errors
///
/// A malformed or half-set packaging override; the message names the
/// offending variable.
pub fn resolve(
    env: &dyn Fn(&str) -> Option<String>,
    crate_dir: &Path,
    git: &OsStr,
) -> Result<SourceIdentity, String> {
    for (refused, replacement) in REFUSED_ENV {
        if env(refused).is_some() {
            return Err(format!(
                "{refused} is not read: verified Targo removes every TRUST_* variable from a \
                 build script's environment, so this spelling would be silently dropped on the \
                 verified lane; set {replacement} instead"
            ));
        }
    }
    match (env(ENV_GIT_SHA), env(ENV_GIT_DIRTY)) {
        (Some(sha), dirty) => {
            if !is_lower_hex(&sha, SHORT_SHA_LEN, 40) {
                return Err(format!(
                    "{ENV_GIT_SHA}={sha:?} is malformed: expected 12 to 40 lowercase hex digits \
                     (a packaging bug; refusing to embed a guessed build identity)"
                ));
            }
            let attestation = match dirty.as_deref() {
                Some("0") => Attestation::PackagedClean,
                Some("1") => Attestation::PackagedDirty,
                Some(other) => {
                    return Err(format!(
                        "{ENV_GIT_DIRTY}={other:?} is malformed: expected `0` or `1`"
                    ));
                }
                None => {
                    return Err(format!(
                        "{ENV_GIT_SHA} is set but {ENV_GIT_DIRTY} is not: packaging must attest \
                         the working tree as `0` (clean) or `1` (dirty)"
                    ));
                }
            };
            Ok(SourceIdentity {
                sha: Some(sha),
                attestation,
            })
        }
        (None, Some(dirty)) => Err(format!(
            "{ENV_GIT_DIRTY}={dirty:?} is set but {ENV_GIT_SHA} is not: a dirty flag without a \
             sha is a packaging bug"
        )),
        (None, None) => Ok(match own_checkout_head(crate_dir, git) {
            Some(sha) => SourceIdentity {
                sha: Some(sha),
                attestation: Attestation::Local,
            },
            None => SourceIdentity {
                sha: None,
                attestation: Attestation::Unknown,
            },
        }),
    }
}

/// `git -C <dir> <args>` with every repository-redirecting variable cleared.
fn git_command(git: &OsStr, dir: &Path, args: &[&str]) -> Command {
    let mut cmd = Command::new(git);
    cmd.arg("-C").arg(dir).args(args);
    for var in GIT_REDIRECT_VARS {
        cmd.env_remove(var);
    }
    cmd
}

/// Run `git -C <dir> <args>`, returning trimmed, non-empty stdout on success.
fn run_git(git: &OsStr, dir: &Path, args: &[&str]) -> Option<String> {
    let out = git_command(git, dir, args).output().ok()?;
    if !out.status.success() {
        return None;
    }
    let s = String::from_utf8(out.stdout).ok()?.trim().to_string();
    (!s.is_empty()).then_some(s)
}

/// Whether `git -C <dir> <args>` runs and exits successfully.
fn git_succeeds(git: &OsStr, dir: &Path, args: &[&str]) -> bool {
    git_command(git, dir, args)
        .output()
        .is_ok_and(|out| out.status.success())
}

/// The repository root this crate is expected to sit at, or `None` when the
/// crate is not in its own checkout.
fn own_repo_root(crate_dir: &Path, git: &OsStr) -> Option<PathBuf> {
    let crate_dir = crate_dir.canonicalize().ok()?;
    let top = PathBuf::from(run_git(git, &crate_dir, &["rev-parse", "--show-toplevel"])?)
        .canonicalize()
        .ok()?;
    let mut expected = top.clone();
    for part in CRATE_REL_PATH {
        expected.push(part);
    }
    if expected.canonicalize().ok()? != crate_dir {
        return None;
    }
    // The root's HEAD must record this crate's manifest: an untracked copy
    // dropped at the right relative path is not this repository's source.
    let manifest = format!("HEAD:{}/Cargo.toml", CRATE_REL_PATH.join("/"));
    if !git_succeeds(git, &top, &["cat-file", "-e", &manifest]) {
        return None;
    }
    Some(top)
}

/// The own checkout's `HEAD` commit, or `None`.
fn own_checkout_head(crate_dir: &Path, git: &OsStr) -> Option<String> {
    let top = own_repo_root(crate_dir, git)?;
    let sha = run_git(
        git,
        &top,
        &["rev-parse", "--verify", "--quiet", "HEAD^{commit}"],
    )?;
    // SHA-1 (40) or SHA-256 (64) object names only.
    (is_lower_hex(&sha, 40, 40) || is_lower_hex(&sha, 64, 64)).then_some(sha)
}

/// Paths whose change must re-run the build script so the fallback sha tracks
/// `HEAD`: `HEAD`, and when `HEAD` names a branch, `packed-refs` and the branch
/// ref (or, when that ref is packed and its parent directories do not exist,
/// the nearest existing ancestor where Git will create them). A detached
/// `HEAD` holds its commit itself, so
/// nothing else is read: watching `packed-refs` there re-ran the script, and
/// rebuilt every crate above `trust-ir`, whenever a fetch packed new refs or
/// another checkout of the same commit was compared (a superproject's
/// submodule is always detached). Resolved through `--git-path`, so linked
/// worktrees are handled.
fn rerun_paths(crate_dir: &Path, git: &OsStr) -> Vec<PathBuf> {
    let Some(top) = own_repo_root(crate_dir, git) else {
        return Vec::new();
    };
    let git_path = |p: &str| {
        run_git(git, &top, &["rev-parse", "--git-path", p]).map(|s| {
            let path = PathBuf::from(s);
            if path.is_absolute() {
                path
            } else {
                top.join(path)
            }
        })
    };
    let mut paths: Vec<PathBuf> = git_path("HEAD")
        .filter(|p| p.exists())
        .into_iter()
        .collect();
    if let Some(head_ref) = run_git(git, &top, &["symbolic-ref", "-q", "HEAD"]) {
        paths.extend(git_path("packed-refs").filter(|p| p.exists()));
        if let Some(path) = git_path(&head_ref) {
            if path.exists() {
                paths.push(path);
            } else if let Some(parent) = path.ancestors().skip(1).find(|p| p.exists()) {
                paths.push(parent.to_path_buf());
            }
        }
    }
    paths
}

/// Every `cargo:` line the build script prints, in order.
///
/// # Errors
///
/// See [`resolve`].
pub fn build_directives(
    env: &dyn Fn(&str) -> Option<String>,
    crate_dir: &Path,
    git: &OsStr,
) -> Result<Vec<String>, String> {
    let identity = resolve(env, crate_dir, git)?;
    let mut out = vec![
        format!("cargo:rerun-if-env-changed={ENV_GIT_SHA}"),
        format!("cargo:rerun-if-env-changed={ENV_GIT_DIRTY}"),
    ];
    // Setting a refused spelling later must re-run the script so it fails.
    for (refused, _) in REFUSED_ENV {
        out.push(format!("cargo:rerun-if-env-changed={refused}"));
    }
    out.extend([
        "cargo:rerun-if-changed=build.rs".to_string(),
        "cargo:rerun-if-changed=build_identity.rs".to_string(),
    ]);
    if identity.attestation == Attestation::Local {
        for path in rerun_paths(crate_dir, git) {
            out.push(format!("cargo:rerun-if-changed={}", path.display()));
        }
    }
    out.push(format!("cargo:rustc-env={OUT_SOURCE}={}", identity.label()));
    out.push(format!(
        "cargo:rustc-env={OUT_SHA}={}",
        identity.sha.as_deref().unwrap_or("unknown")
    ));
    out.push(format!(
        "cargo:rustc-env={OUT_ATTESTATION}={}",
        identity.attestation.as_str()
    ));
    Ok(out)
}
