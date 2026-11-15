// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The compiler for Clean's generated ORACLE programs: `native_decide`'s
//! evaluator and the differential battery of `clean extract --backend rust`.
//!
//! An oracle's answer feeds a decision, so the compiler that builds it sits in
//! Clean's decision path. It is therefore Trust's OWN compiler, admitted by
//! what it is rather than by its name, and nothing else. Resolution, once per
//! process:
//!
//! 1. [`TRUSTC_ENV`] (`CLEAN_NATIVE_DECIDE_TRUSTC`), an absolute path, when set.
//!    A refused setting is final: nothing else is consulted.
//! 2. Otherwise the `trustc` beside the running executable (its canonical
//!    path): Clean linked into `trustc` itself, or a toolchain's `bin/clean`
//!    next to `bin/trustc`.
//! 3. Otherwise none.
//!
//! Never `PATH`, `$RUSTC` or rustup: a bare `rustc` or `trustc` resolves to
//! whatever the caller's `PATH` and `RUSTUP_TOOLCHAIN` say, which on a machine
//! with rustup is stock Rust in every directory without a Trust pin. A
//! candidate is admitted (`admit`) only when
//!
//! - its canonical path lies outside rustup's, cargo's and Homebrew's install
//!   directories, which hold stock Rust;
//! - it is a regular file that starts with a Mach-O, ELF or PE header -- a
//!   script is never admitted, whatever it prints;
//! - its `-vV`, run in the scrubbed environment below, says `binary: trustc`,
//!   carries Trust's `trust:` line and a full `commit-hash:`;
//! - when this library was built as part of a Trust toolchain
//!   (`CFG_TRUST_ORACLE_HOST=1`), that commit is the running host's own,
//!   bound immutably by its entrypoint. The large elaborator
//!   library does not embed a changing toolchain build ID;
//! - it has a sysroot (`<sysroot>/bin/trustc` beside `<sysroot>/lib/rustlib`).
//!
//! What admission is, and is not: these checks keep out stock Rust that
//! arrives by accident -- a rustup proxy, a reroute script, a stock `rustc`
//! under another name (its driver still prints `binary: rustc`). They read
//! the candidate's own `-vV`, so they are not provenance against a binary
//! crafted to lie. No proof Clean accepts depends on them: the Clean kernel is
//! the authority for ACCEPTANCE either way, since a native `true` is re-derived
//! by kernel reduction of the `Decidable` instance before a proof is returned,
//! and a native `false` only fails the tactic. A lying compiler can cost
//! completeness, or pass an extraction battery (a differential CHECK, not a
//! proof) on a binary that is not the emitted module.
//!
//! When nothing is admitted there is no native path: `native_decide` is decided
//! by the Clean kernel, and extraction refuses with `E_RUST_TOOLCHAIN`. A
//! refused candidate is never replaced by another compiler, and a failed
//! compile is never retried with other flags.
//!
//! Every process this module starts runs with `RUSTUP_TOOLCHAIN`, `RUSTC` and
//! every `TRUST_*` variable removed: an oracle compile is a plain compile with
//! verification off, so it must not inherit the caller's Trust session (Targo
//! hands a compiler unit `TRUST_TARGO_TEST_MONITOR_SESSION`, which a compile
//! that was not selected for that monitor refuses as fatal).

use std::ffi::OsStr;
use std::path::{Component, Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, OnceLock};

use thiserror::Error;

/// Names the oracle compiler explicitly: an absolute path to a `trustc`.
pub const TRUSTC_ENV: &str = "CLEAN_NATIVE_DECIDE_TRUSTC";

mod host_identity;
pub use host_identity::bind_host_toolchain;
use host_identity::host_toolchain_commit;

/// Variables that would steer a rustup proxy or a nested build; removed from
/// every process this module starts, with every [`SCRUBBED_ENV_PREFIX`] one.
const SCRUBBED_ENV: [&str; 2] = ["RUSTUP_TOOLCHAIN", "RUSTC"];

/// Trust's own controls (Targo's session protocol, untracked codegen
/// switches): an oracle compile inherits none of them.
const SCRUBBED_ENV_PREFIX: &str = "TRUST_";

/// An admitted Trust compiler for oracle programs.
#[derive(Debug, Clone)]
pub struct OracleCompiler {
    path: PathBuf,
    sysroot: PathBuf,
    commit: String,
    /// Compiles started through this admission (and its clones).
    spawns: Arc<AtomicU64>,
}

/// Why no oracle compiler is available, or why a compile failed.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum OracleCompilerError {
    #[error("cannot establish the running Trust host's identity: {detail}")]
    HostIdentity { detail: String },
    #[error("no oracle compiler: {TRUSTC_ENV} is unset and there is no `trustc` beside {exe}")]
    NoCandidate { exe: String },
    #[error("{TRUSTC_ENV}={path} is not an absolute path")]
    NotAbsolute { path: String },
    #[error("{path}: cannot resolve: {detail}")]
    Unresolvable { path: String, detail: String },
    #[error("{path}: under a rustup, cargo or Homebrew install directory, which holds stock Rust")]
    StockInstallDir { path: String },
    #[error("{path}: not a regular file")]
    NotAFile { path: String },
    #[error(
        "{path}: not a native executable (no Mach-O, ELF or PE header); a script is never admitted"
    )]
    NotAnExecutable { path: String },
    #[error("{path}: `-vV` failed: {detail}")]
    ProbeFailed { path: String, detail: String },
    #[error("{path}: not a Trust compiler: its `-vV` has no {missing}")]
    NotTrust { path: String, missing: &'static str },
    #[error("{path}: commit {found} is not this toolchain's commit {expected}")]
    CommitMismatch {
        path: String,
        found: String,
        expected: String,
    },
    #[error("{path}: no sysroot: {detail}")]
    NoSysroot { path: String, detail: String },
    #[error("failed to launch {path}: {detail}")]
    Launch { path: String, detail: String },
    #[error("{path} exited with {status}: {stderr}")]
    CompileFailed {
        path: String,
        status: String,
        stderr: String,
    },
}

impl OracleCompiler {
    /// The admitted compiler's canonical path.
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// The Trust commit its `-vV` reports.
    pub(crate) fn commit(&self) -> &str {
        &self.commit
    }

    /// How many compiles this admission has started. A diagnostic: zero means
    /// no oracle program was compiled through it.
    pub fn spawns(&self) -> u64 {
        self.spawns.load(Ordering::Relaxed)
    }

    /// Compile the single-file oracle program `source` into the executable
    /// `output`. ONE spawn: a failure is returned, never retried with other
    /// flags or another compiler.
    ///
    /// TRUST OPT-OUT. `-Ztrust-verify=off` because an oracle program is an
    /// evaluator for a ground proposition or a test battery, not a
    /// verification target -- under the strict policy Trust's obligation
    /// checker failed it (`2 obligation(s) were not fully verified` in
    /// `native_decide::nat_succ`). Its arithmetic is checked by construction
    /// (`checked_add(..)` into an `Err`), and the opt-out removes only the
    /// static REPORT: the emitted semantics are unchanged.
    pub fn compile(&self, source: &Path, output: &Path) -> Result<(), OracleCompilerError> {
        let mut command = command_for(&self.path);
        command
            .args(["--edition=2021", "-O", "-Ztrust-verify=off", "--sysroot"])
            .arg(&self.sysroot)
            .arg(source)
            .arg("-o")
            .arg(output);
        self.spawns.fetch_add(1, Ordering::Relaxed);
        let result = command
            .output()
            .map_err(|err| OracleCompilerError::Launch {
                path: self.path.display().to_string(),
                detail: err.to_string(),
            })?;
        if result.status.success() {
            Ok(())
        } else {
            Err(OracleCompilerError::CompileFailed {
                path: self.path.display().to_string(),
                status: result.status.to_string(),
                stderr: String::from_utf8_lossy(&result.stderr).trim().to_owned(),
            })
        }
    }
}

fn command_for(path: &Path) -> Command {
    let mut command = Command::new(path);
    command.stdin(Stdio::null());
    for var in SCRUBBED_ENV {
        command.env_remove(var);
    }
    for (var, _) in std::env::vars_os() {
        if is_trust_control(&var) {
            command.env_remove(var);
        }
    }
    command
}

/// One of Trust's own controls: a `TRUST_*` variable.
fn is_trust_control(var: &OsStr) -> bool {
    var.to_str()
        .is_some_and(|var| var.starts_with(SCRUBBED_ENV_PREFIX))
}

/// This process's oracle compiler, resolved and admitted once.
pub fn oracle_compiler() -> Result<&'static OracleCompiler, &'static OracleCompilerError> {
    static RESOLVED: OnceLock<Result<OracleCompiler, OracleCompilerError>> = OnceLock::new();
    RESOLVED
        .get_or_init(|| {
            let explicit = std::env::var_os(TRUSTC_ENV).filter(|value| !value.is_empty());
            let exe = std::env::current_exe().ok();
            let resolved = resolve(explicit.as_deref(), exe.as_deref());
            match &resolved {
                Ok(compiler) => tracing::debug!(
                    compiler = %compiler.path.display(),
                    commit = %compiler.commit,
                    "oracle compiler admitted"
                ),
                Err(why @ OracleCompilerError::NoCandidate { .. }) => tracing::debug!(
                    %why,
                    "no oracle compiler: native_decide is decided by the Clean kernel, \
                     and `clean extract --backend rust` refuses"
                ),
                Err(why) => tracing::warn!(
                    %why,
                    "oracle compiler refused: native_decide is decided by the Clean kernel, \
                     and `clean extract --backend rust` refuses"
                ),
            }
            resolved
        })
        .as_ref()
}

/// Resolve the oracle compiler from an explicit setting (the value of
/// [`TRUSTC_ENV`]) or, without one, the `trustc` beside `current_exe`.
/// A refused explicit setting is final: the sibling is not consulted.
pub(crate) fn resolve(
    explicit: Option<&OsStr>,
    current_exe: Option<&Path>,
) -> Result<OracleCompiler, OracleCompilerError> {
    match (explicit, current_exe) {
        (Some(explicit), _) => {
            let path = Path::new(explicit);
            if path.is_absolute() {
                admit(path)
            } else {
                Err(OracleCompilerError::NotAbsolute {
                    path: path.display().to_string(),
                })
            }
        }
        (None, Some(exe)) => admit_beside(exe),
        (None, None) => Err(OracleCompilerError::NoCandidate {
            exe: "the running executable (unknown)".to_owned(),
        }),
    }
}

/// Admit the `trustc` in the directory of `exe`'s canonical path: the rule
/// for the running executable, and the way a test names its own toolchain's
/// compiler (`$CARGO`'s sibling).
pub fn admit_beside(exe: &Path) -> Result<OracleCompiler, OracleCompilerError> {
    let no_candidate = || OracleCompilerError::NoCandidate {
        exe: exe.display().to_string(),
    };
    let sibling = exe
        .canonicalize()
        .map_err(|_| no_candidate())?
        .with_file_name(format!("trustc{}", std::env::consts::EXE_SUFFIX));
    if sibling.exists() {
        admit(&sibling)
    } else {
        Err(no_candidate())
    }
}

/// Admit `candidate` as an oracle compiler by what it is (see the module
/// documentation), running it once with `-vV`.
pub(crate) fn admit(candidate: &Path) -> Result<OracleCompiler, OracleCompilerError> {
    let expected = host_toolchain_commit()?;
    admit_expecting(candidate, expected.as_deref())
}

/// [`admit`], with the current host's Trust identity supplied explicitly.
fn admit_expecting(
    candidate: &Path,
    expected: Option<&str>,
) -> Result<OracleCompiler, OracleCompilerError> {
    let shown = || candidate.display().to_string();
    let path = candidate
        .canonicalize()
        .map_err(|err| OracleCompilerError::Unresolvable {
            path: shown(),
            detail: err.to_string(),
        })?;
    let shown = path.display().to_string();
    if in_stock_install_dir(&path) {
        return Err(OracleCompilerError::StockInstallDir { path: shown });
    }
    if !path.is_file() {
        return Err(OracleCompilerError::NotAFile { path: shown });
    }
    if !has_executable_header(&path) {
        return Err(OracleCompilerError::NotAnExecutable { path: shown });
    }
    let probe =
        command_for(&path)
            .arg("-vV")
            .output()
            .map_err(|err| OracleCompilerError::ProbeFailed {
                path: shown.clone(),
                detail: err.to_string(),
            })?;
    if !probe.status.success() {
        return Err(OracleCompilerError::ProbeFailed {
            path: shown,
            detail: format!(
                "exited with {}: {}",
                probe.status,
                String::from_utf8_lossy(&probe.stderr).trim()
            ),
        });
    }
    let commit = trust_identity(&String::from_utf8_lossy(&probe.stdout)).map_err(|missing| {
        OracleCompilerError::NotTrust {
            path: shown.clone(),
            missing,
        }
    })?;
    if let Some(expected) = expected {
        if commit != expected {
            return Err(OracleCompilerError::CommitMismatch {
                path: shown,
                found: commit,
                expected: expected.to_owned(),
            });
        }
    }
    let Some(sysroot) = sysroot_of(&path) else {
        return Err(OracleCompilerError::NoSysroot {
            path: shown,
            detail: "it has no grandparent directory".to_owned(),
        });
    };
    if !sysroot.join("lib").join("rustlib").is_dir() {
        return Err(OracleCompilerError::NoSysroot {
            path: shown,
            detail: format!("{} has no lib/rustlib", sysroot.display()),
        });
    }
    Ok(OracleCompiler {
        path,
        sysroot,
        commit,
        spawns: Arc::default(),
    })
}

/// The sysroot of a compiler at `<sysroot>/bin/trustc`: its grandparent
/// directory, which a compiler at the filesystem root does not have.
fn sysroot_of(compiler: &Path) -> Option<PathBuf> {
    compiler
        .parent()
        .and_then(Path::parent)
        .map(Path::to_path_buf)
}

/// The commit of a Trust compiler's `-vV`, or the first identity line it
/// lacks.
fn trust_identity(version: &str) -> Result<String, &'static str> {
    let field = |key: &str| {
        version
            .lines()
            .find_map(|line| line.strip_prefix(key))
            .map(str::trim)
    };
    if field("binary:") != Some("trustc") {
        return Err("`binary: trustc` line");
    }
    if field("trust:").is_none_or(str::is_empty) {
        return Err("`trust:` line");
    }
    match field("commit-hash:") {
        Some(commit) if commit.len() == 40 && commit.bytes().all(|b| b.is_ascii_hexdigit()) => {
            Ok(commit.to_owned())
        }
        _ => Err("full `commit-hash:` line"),
    }
}

/// Under rustup's toolchains, cargo's `bin` (rustup's proxies) or Homebrew.
fn in_stock_install_dir(path: &Path) -> bool {
    let normal: Vec<&OsStr> = path
        .components()
        .filter_map(|component| match component {
            Component::Normal(part) => Some(part),
            _ => None,
        })
        .collect();
    let named_dir = normal.iter().any(|part| *part == ".rustup")
        || normal
            .windows(2)
            .any(|pair| pair[0] == ".cargo" && pair[1] == "bin");
    let homebrew = [
        "/opt/homebrew",
        "/usr/local/Cellar",
        "/usr/local/Homebrew",
        "/home/linuxbrew",
    ]
    .iter()
    .any(|prefix| path.starts_with(prefix));
    let configured = [("RUSTUP_HOME", None), ("CARGO_HOME", Some("bin"))]
        .into_iter()
        .filter_map(|(var, sub)| {
            let home = PathBuf::from(std::env::var_os(var)?);
            let dir = sub.map_or_else(|| home.clone(), |sub| home.join(sub));
            dir.canonicalize().ok()
        })
        .any(|dir| path.starts_with(dir));
    named_dir || homebrew || configured
}

/// Mach-O (thin or fat, either byte order), ELF or PE.
fn has_executable_header(path: &Path) -> bool {
    use std::io::Read;
    let mut magic = [0u8; 4];
    let read = std::fs::File::open(path).and_then(|mut file| file.read_exact(&mut magic));
    if read.is_err() {
        return false;
    }
    matches!(
        magic,
        [0xfe, 0xed, 0xfa, 0xce | 0xcf]
            | [0xce | 0xcf, 0xfa, 0xed, 0xfe]
            | [0xca, 0xfe, 0xba, 0xbe | 0xbf]
            | [0xbe | 0xbf, 0xba, 0xfe, 0xca]
            | [0x7f, b'E', b'L', b'F']
    ) || magic.starts_with(b"MZ")
}

#[cfg(test)]
#[path = "oracle_compiler_tests.rs"]
pub(crate) mod tests;
