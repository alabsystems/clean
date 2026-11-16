// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The process seam (`curl`, `git`) and the streaming checksum.
//!
//! Downloading and checking out cannot be pure Rust without new dependencies,
//! so the orchestration in the parent module goes through the [`Fetcher`]
//! trait. [`SystemFetcher`] shells out to `curl` and `git`; tests inject a fake
//! to prove a `--dry` run starts neither.

use std::fs::File;
use std::io::Read as _;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Output, Stdio};

use sha2::{Digest as _, Sha256};

use super::error::FetchError;
use crate::math_map::bundle::hex_lower;

/// Environment variables that would point `git -C <dir>` at another
/// repository than `<dir>` (they are set inside git hooks, for example).
const GIT_REDIRECT_VARS: &[&str] = &[
    "GIT_DIR",
    "GIT_WORK_TREE",
    "GIT_INDEX_FILE",
    "GIT_OBJECT_DIRECTORY",
    "GIT_ALTERNATE_OBJECT_DIRECTORIES",
    "GIT_COMMON_DIR",
];

/// What a directory holds, as far as the AFP pin is concerned.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CheckoutState {
    /// No `.git` at the directory, or the directory is not the top of the
    /// checkout that contains it.
    NotACheckout,
    /// A git checkout with no commit.
    NoHead,
    /// A git checkout at `head`.
    At {
        /// The checked-out commit.
        head: String,
        /// Whether any tracked file differs from `head` (untracked files are
        /// not counted: session builds write code-generator output there).
        tracked_changes: bool,
    },
}

/// Downloads files and checks out git revisions. Injected so the
/// orchestration is testable without the network.
pub(crate) trait Fetcher {
    /// Download `url` to `dest`, replacing whatever is there.
    ///
    /// # Errors
    /// [`FetchError::Spawn`] or [`FetchError::Download`].
    fn download(&self, url: &str, dest: &Path) -> Result<(), FetchError>;

    /// Make `dir` (an existing, empty directory) a checkout of `rev` from
    /// `repo`: `git init`, fetch exactly `rev` at `depth`, detached checkout.
    ///
    /// # Errors
    /// [`FetchError::Spawn`] or [`FetchError::Git`].
    fn checkout_rev(&self, repo: &str, rev: &str, depth: u32, dir: &Path)
        -> Result<(), FetchError>;

    /// Describe `dir` without changing it (git runs with
    /// `--no-optional-locks`).
    ///
    /// # Errors
    /// [`FetchError::Spawn`] or [`FetchError::Git`] if git cannot answer.
    fn inspect_checkout(&self, dir: &Path) -> Result<CheckoutState, FetchError>;
}

/// Whether `curl` and `git` show their own progress.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Progress {
    /// Let curl and git draw progress on the inherited stderr.
    Show,
    /// Run them quietly and keep their messages for the error.
    Hide,
}

/// The real fetcher: `curl` for archives, `git` for the AFP.
#[derive(Debug, Clone, Copy)]
pub(crate) struct SystemFetcher {
    /// Progress display.
    pub(crate) progress: Progress,
}

impl SystemFetcher {
    /// Show progress when stderr is a terminal, stay quiet otherwise.
    pub(crate) fn for_stderr() -> Self {
        use std::io::IsTerminal as _;
        let progress = if std::io::stderr().is_terminal() {
            Progress::Show
        } else {
            Progress::Hide
        };
        Self { progress }
    }

    fn git(&self, dir: &Path) -> Command {
        let mut cmd = Command::new("git");
        for var in GIT_REDIRECT_VARS {
            cmd.env_remove(var);
        }
        cmd.arg("-C").arg(dir).stdin(Stdio::null());
        cmd
    }

    /// Run `git -C dir <args>`; `inherit` lets git print to our stderr.
    fn run_git(&self, dir: &Path, args: &[&str], inherit: bool) -> Result<Output, FetchError> {
        let mut cmd = self.git(dir);
        cmd.args(args);
        if inherit {
            cmd.stderr(Stdio::inherit());
        }
        let out = cmd.output().map_err(|source| FetchError::Spawn {
            program: "git".to_string(),
            source,
        })?;
        if out.status.success() {
            return Ok(out);
        }
        Err(FetchError::Git {
            args: args.join(" "),
            dir: dir.to_path_buf(),
            status: describe_status(out.status),
            detail: detail(&out.stderr, inherit),
        })
    }
}

impl Fetcher for SystemFetcher {
    fn download(&self, url: &str, dest: &Path) -> Result<(), FetchError> {
        let mut cmd = Command::new("curl");
        // `-q` must come first: it stops curl reading `~/.curlrc`, whose
        // settings (a proxy, `--insecure`, an output template) would change
        // what this command downloads and where.
        cmd.args([
            "-q",
            "--fail",
            "--location",
            "--retry",
            "3",
            "--proto",
            "=https,http",
            "--noproxy",
            "localhost,127.0.0.1",
        ]);
        let inherit = self.progress == Progress::Show;
        if inherit {
            cmd.arg("--progress-bar").stderr(Stdio::inherit());
        } else {
            cmd.args(["--silent", "--show-error"]);
        }
        cmd.arg("--output")
            .arg(dest)
            .arg(url)
            .stdin(Stdio::null())
            .stdout(Stdio::null());
        let out = cmd.output().map_err(|source| FetchError::Spawn {
            program: "curl".to_string(),
            source,
        })?;
        if out.status.success() {
            return Ok(());
        }
        Err(FetchError::Download {
            url: url.to_string(),
            status: describe_status(out.status),
            detail: detail(&out.stderr, inherit),
        })
    }

    fn checkout_rev(
        &self,
        repo: &str,
        rev: &str,
        depth: u32,
        dir: &Path,
    ) -> Result<(), FetchError> {
        self.run_git(dir, &["init", "--quiet"], false)?;
        let depth_arg = format!("--depth={depth}");
        let show = self.progress == Progress::Show;
        let verbosity = if show { "--progress" } else { "--quiet" };
        self.run_git(
            dir,
            &[
                "fetch",
                verbosity,
                "--no-tags",
                depth_arg.as_str(),
                repo,
                rev,
            ],
            show,
        )?;
        self.run_git(
            dir,
            &[
                "-c",
                "advice.detachedHead=false",
                "checkout",
                "--quiet",
                "--detach",
                "FETCH_HEAD",
            ],
            false,
        )?;
        Ok(())
    }

    fn inspect_checkout(&self, dir: &Path) -> Result<CheckoutState, FetchError> {
        if !dir.join(".git").exists() {
            return Ok(CheckoutState::NotACheckout);
        }
        let top = self.run_git(
            dir,
            &["--no-optional-locks", "rev-parse", "--show-toplevel"],
            false,
        )?;
        let top = PathBuf::from(String::from_utf8_lossy(&top.stdout).trim());
        let same = match (std::fs::canonicalize(dir), std::fs::canonicalize(top)) {
            (Ok(a), Ok(b)) => a == b,
            _ => false,
        };
        if !same {
            return Ok(CheckoutState::NotACheckout);
        }
        // `rev-parse --verify --quiet` exits 1 with no output on an unborn HEAD.
        let head = self
            .git(dir)
            .args([
                "--no-optional-locks",
                "rev-parse",
                "--verify",
                "--quiet",
                "HEAD^{commit}",
            ])
            .output()
            .map_err(|source| FetchError::Spawn {
                program: "git".to_string(),
                source,
            })?;
        if !head.status.success() {
            return Ok(CheckoutState::NoHead);
        }
        let head = String::from_utf8_lossy(&head.stdout).trim().to_string();
        let status = self.run_git(
            dir,
            &[
                "--no-optional-locks",
                "status",
                "--porcelain",
                "--untracked-files=no",
            ],
            false,
        )?;
        Ok(CheckoutState::At {
            head,
            tracked_changes: !status.stdout.iter().all(u8::is_ascii_whitespace),
        })
    }
}

fn describe_status(status: ExitStatus) -> String {
    match status.code() {
        Some(code) => format!("exit status {code}"),
        None => "killed by a signal".to_string(),
    }
}

fn detail(stderr: &[u8], inherited: bool) -> String {
    if inherited {
        return "its message is printed above".to_string();
    }
    let text = String::from_utf8_lossy(stderr).trim().to_string();
    if text.is_empty() {
        "no message".to_string()
    } else {
        text
    }
}

/// How a file on disk compares with its pin.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum FileCheck {
    /// Nothing at the path.
    Missing,
    /// The pinned size and sha256.
    Match,
    /// A regular file that differs; the text says how (`N bytes` or
    /// `sha256 ...`).
    Differs(String),
}

/// Compare `path` with a pinned size and sha256. The size is checked first,
/// so a file of the wrong size is never hashed.
///
/// # Errors
/// [`FetchError::NotAFile`] if something other than a regular file is there;
/// [`FetchError::Io`] if it cannot be read.
pub(crate) fn check_file(path: &Path, bytes: u64, sha256: &str) -> Result<FileCheck, FetchError> {
    let meta = match std::fs::metadata(path) {
        Ok(meta) => meta,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(FileCheck::Missing),
        Err(source) => {
            return Err(FetchError::Io {
                path: path.to_path_buf(),
                source,
            })
        }
    };
    if !meta.is_file() {
        return Err(FetchError::NotAFile {
            path: path.to_path_buf(),
        });
    }
    if meta.len() != bytes {
        return Ok(FileCheck::Differs(format!("{} bytes", meta.len())));
    }
    let actual = sha256_file(path)?;
    if actual == sha256 {
        Ok(FileCheck::Match)
    } else {
        Ok(FileCheck::Differs(format!("sha256 {actual}")))
    }
}

/// The sha256 of a file, lowercase hex, read in 1 MiB chunks so a 1.7 GB
/// archive never sits in memory.
///
/// # Errors
/// [`FetchError::Io`] if the file cannot be opened or read.
pub(crate) fn sha256_file(path: &Path) -> Result<String, FetchError> {
    let io_err = |source| FetchError::Io {
        path: path.to_path_buf(),
        source,
    };
    let mut file = File::open(path).map_err(io_err)?;
    let mut hasher = Sha256::new();
    let mut buf = vec![0u8; 1 << 20];
    loop {
        let n = match file.read(&mut buf) {
            Ok(0) => break,
            Ok(n) => n,
            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => continue,
            Err(source) => return Err(io_err(source)),
        };
        hasher.update(&buf[..n]);
    }
    Ok(hex_lower(&hasher.finalize()[..]))
}

/// `<path>.part`: where a download or checkout is staged before it is
/// verified and renamed into place.
pub(crate) fn staging_path(path: &Path) -> PathBuf {
    let mut name = path.file_name().unwrap_or_default().to_os_string();
    name.push(".part");
    path.with_file_name(name)
}
