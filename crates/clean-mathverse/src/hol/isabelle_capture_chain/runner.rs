// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The injected process runner (shells out to `isabelle build`) and the
//! outcome classifier that reads its combined log.
//!
//! `isabelle build` cannot be a pure-Rust call, so the driver depends on the
//! [`IsabelleBuildRunner`] trait and the real [`SystemBuildRunner`] spawns
//! `nice -n 19 <isabelle_home>/bin/isabelle build …`. Tests inject a fake so
//! the whole response-ladder state machine runs WITHOUT a live build.

use std::path::PathBuf;
use std::process::Command;
use std::sync::LazyLock;

use regex::Regex;

use super::error::CaptureChainError;

/// A fully-resolved `isabelle build` invocation for one segment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BuildInvocation {
    /// The session to build.
    pub session: String,
    /// `record_proofs` recording level (passed as `-o record_proofs=<n>`).
    pub record_proofs: u32,
    /// Thread count (passed as `-o threads=<t>`).
    pub threads: usize,
    /// `$ISABELLE_HOME` whose `bin/isabelle` is invoked.
    pub isabelle_home: PathBuf,
    /// All `-d` directories (global dirs plus every segment dir), tilde-expanded.
    pub dirs: Vec<PathBuf>,
}

impl BuildInvocation {
    /// The argv passed to `/usr/bin/nice` (the leading `nice -n 19` prefix and
    /// the `isabelle` binary path are prepended by [`SystemBuildRunner`]).
    /// Exposed so tests and `--dry` can assert/print the exact command.
    #[must_use]
    pub fn isabelle_args(&self) -> Vec<String> {
        let mut args = vec![
            "build".to_string(),
            "-b".to_string(),
            "-o".to_string(),
            format!("record_proofs={}", self.record_proofs),
            "-o".to_string(),
            format!("threads={}", self.threads),
        ];
        for dir in &self.dirs {
            args.push("-d".to_string());
            args.push(dir.display().to_string());
        }
        args.push(self.session.clone());
        args
    }

    /// The absolute `isabelle` binary path under `$ISABELLE_HOME`.
    #[must_use]
    pub fn isabelle_bin(&self) -> PathBuf {
        self.isabelle_home.join("bin").join("isabelle")
    }
}

/// The captured result of one build (exit code + combined stdout/stderr).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BuildRun {
    /// Process exit code (`-1` if the process was killed by a signal).
    pub exit_code: i32,
    /// Combined stdout + stderr, in that order.
    pub output: String,
}

/// Runs one `isabelle build`. Injected so the driver's self-healing logic is
/// testable without a live Isabelle toolchain.
pub trait IsabelleBuildRunner {
    /// Run the build described by `inv`, returning its exit code and captured
    /// output. Returns [`CaptureChainError::Spawn`] only when the process
    /// cannot be started at all (a non-zero exit is a normal `BuildRun`, not an
    /// error — the driver classifies it).
    fn run_build(&self, inv: &BuildInvocation) -> Result<BuildRun, CaptureChainError>;
}

/// The real runner: spawns `nice -n 19 <isabelle> build …` and captures output.
#[derive(Clone, Copy, Debug, Default)]
pub struct SystemBuildRunner;

impl IsabelleBuildRunner for SystemBuildRunner {
    fn run_build(&self, inv: &BuildInvocation) -> Result<BuildRun, CaptureChainError> {
        let isabelle = inv.isabelle_bin();
        // On unix, spawn through /usr/bin/nice so the heavy build runs at the
        // lowest priority (a sibling Isabelle build / verify slice keeps the
        // CPU). Elsewhere, run isabelle directly (nice is unix-only).
        let output = if cfg!(unix) {
            let mut cmd = Command::new("/usr/bin/nice");
            cmd.arg("-n")
                .arg("19")
                .arg(&isabelle)
                .args(inv.isabelle_args());
            cmd.output().map_err(|source| CaptureChainError::Spawn {
                program: "/usr/bin/nice".to_string(),
                source,
            })?
        } else {
            let mut cmd = Command::new(&isabelle);
            cmd.args(inv.isabelle_args());
            cmd.output().map_err(|source| CaptureChainError::Spawn {
                program: isabelle.display().to_string(),
                source,
            })?
        };
        let mut combined = String::from_utf8_lossy(&output.stdout).into_owned();
        if !output.stderr.is_empty() {
            if !combined.is_empty() && !combined.ends_with('\n') {
                combined.push('\n');
            }
            combined.push_str(&String::from_utf8_lossy(&output.stderr));
        }
        Ok(BuildRun {
            exit_code: output.status.code().unwrap_or(-1),
            output: combined,
        })
    }
}

/// How a completed build is interpreted by the driver.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BuildOutcome {
    /// Exit code 0 — the segment built and its heap saved.
    Ok,
    /// The build ran out of the Poly/ML arm64_32 store. `theory` is the culprit
    /// theory (the qualified name from the segment list when it could be
    /// matched, else the bare basename, else `None`).
    OutOfStore {
        /// The theory that blew the store, if it could be identified.
        theory: Option<String>,
    },
    /// Any other non-zero exit — the driver halts (no auto-retry on unknowns).
    OtherFailure {
        /// The tail of the captured log, for triage.
        tail: String,
    },
}

/// The `Run out of store` sentinel Poly/ML prints when it exhausts the store.
const OUT_OF_STORE_MARKER: &str = "Run out of store";

/// `*** At command "…" (line N of "…/<Thy>.thy")` — the primary culprit line.
static AT_COMMAND_RE: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r#"line\s+\d+\s+of\s+"([^"]+\.thy)""#)
        .expect("invariant: literal at-command regex compiles")
});

/// `theory <Qualified.Name>` — the fallback "last started theory" progress line
/// (only present when isabelle build ran with progress verbosity).
static THEORY_PROGRESS_RE: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"(?m)^\s*theory\s+([A-Za-z0-9_.\-]+)\s*$")
        .expect("invariant: literal theory-progress regex compiles")
});

/// Classify a completed build against the segment's theory list.
#[must_use]
pub fn classify(run: &BuildRun, theories: &[String]) -> BuildOutcome {
    if run.exit_code == 0 {
        return BuildOutcome::Ok;
    }
    if run.output.contains(OUT_OF_STORE_MARKER) {
        return BuildOutcome::OutOfStore {
            theory: parse_oom_theory(&run.output, theories),
        };
    }
    BuildOutcome::OtherFailure {
        tail: log_tail(&run.output, 40),
    }
}

/// Parse the theory that blew the store: the last `At command … line N of
/// "…/<Thy>.thy"` path basename, mapped back to the segment's qualified theory
/// list when possible; else the last `theory <name>` progress line; else `None`.
#[must_use]
pub fn parse_oom_theory(log: &str, theories: &[String]) -> Option<String> {
    if let Some(cap) = AT_COMMAND_RE.captures_iter(log).last() {
        let path = &cap[1];
        let base = thy_basename(path);
        return Some(match_qualified(&base, theories).unwrap_or(base));
    }
    if let Some(cap) = THEORY_PROGRESS_RE.captures_iter(log).last() {
        let name = cap[1].to_string();
        // Prefer the exact qualified name from the segment if it is present.
        if theories.iter().any(|t| t == &name) {
            return Some(name);
        }
        let base = last_component(&name);
        return Some(match_qualified(&base, theories).unwrap_or(name));
    }
    None
}

/// The theory basename of a `.thy` path (`~~/src/HOL/Library/Interval.thy` →
/// `Interval`).
fn thy_basename(path: &str) -> String {
    let file = path.rsplit(['/', '\\']).next().unwrap_or(path);
    file.strip_suffix(".thy").unwrap_or(file).to_string()
}

/// The last dotted component of a qualified name (`HOL-Library.Interval` →
/// `Interval`).
fn last_component(qualified: &str) -> String {
    qualified
        .rsplit('.')
        .next()
        .unwrap_or(qualified)
        .to_string()
}

/// Find the qualified theory in `theories` whose last component equals `base`.
fn match_qualified(base: &str, theories: &[String]) -> Option<String> {
    theories.iter().find(|t| last_component(t) == base).cloned()
}

/// The last `n` non-empty lines of a log, joined with newlines.
fn log_tail(log: &str, n: usize) -> String {
    let lines: Vec<&str> = log.lines().filter(|l| !l.trim().is_empty()).collect();
    let start = lines.len().saturating_sub(n);
    lines[start..].join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    const THEORIES: &[&str] = &[
        "HOL-Library.Float",
        "HOL-Library.Going_To_Filter",
        "HOL-Library.Interval",
    ];

    fn theories() -> Vec<String> {
        THEORIES.iter().map(|s| (*s).to_string()).collect()
    }

    #[test]
    fn test_parse_oom_theory_real_at_command_line() {
        // The exact lines from ~/isabelle-work/zp_lib3_split2_build.log.
        let log = "Building ZP-Lib3c2 ...\n\
                   Run out of store - interrupting threads\n\
                   ZP-Lib3c2 FAILED (see also \"isabelle build_log -H Error ZP-Lib3c2\")\n\
                   *** exception Interrupt_Breakdown raised\n\
                   *** At command \"by\" (line 567 of \"~~/src/HOL/Library/Interval.thy\")\n\
                   Unfinished session(s): ZP-Lib3c2\n";
        assert_eq!(
            parse_oom_theory(log, &theories()),
            Some("HOL-Library.Interval".to_string()),
            "maps the .thy basename back to the qualified segment theory"
        );
    }

    #[test]
    fn test_parse_oom_theory_takes_last_at_command() {
        let log = "*** At command \"by\" (line 12 of \"~~/src/HOL/Library/Float.thy\")\n\
                   *** At command \"by\" (line 567 of \"~~/src/HOL/Library/Interval.thy\")\n";
        assert_eq!(
            parse_oom_theory(log, &theories()),
            Some("HOL-Library.Interval".to_string()),
            "the LAST culprit line wins"
        );
    }

    #[test]
    fn test_parse_oom_theory_afp_path() {
        let thys = vec!["Word_Lib.More_Divides".to_string()];
        let log = "*** At command \"by\" (line 282 of \"~/isabelle-work/afp/thys/Word_Lib/More_Divides.thy\")\n";
        assert_eq!(
            parse_oom_theory(log, &thys),
            Some("Word_Lib.More_Divides".to_string())
        );
    }

    #[test]
    fn test_parse_oom_theory_fallback_to_progress_line() {
        // No At-command line (the first real OOM in the log had none); fall back
        // to the last `theory <name>` progress line.
        let log = "Building ZP-Lib3c2 ...\n\
                   theory HOL-Library.Float\n\
                   theory HOL-Library.Interval\n\
                   Run out of store - interrupting threads\n";
        assert_eq!(
            parse_oom_theory(log, &theories()),
            Some("HOL-Library.Interval".to_string())
        );
    }

    #[test]
    fn test_parse_oom_theory_unknown_returns_none() {
        let log = "Building ZP-Lib3c2 ...\n\
                   Run out of store - interrupting threads\n\
                   Run out of store - interrupting threads\n\
                   Failed to recover - exiting\n";
        assert_eq!(parse_oom_theory(log, &theories()), None);
    }

    #[test]
    fn test_classify_ok_and_oom_and_other() {
        assert_eq!(
            classify(
                &BuildRun {
                    exit_code: 0,
                    output: "Finished ZP-Lib3c1 (…)".into()
                },
                &theories()
            ),
            BuildOutcome::Ok
        );
        assert_eq!(
            classify(
                &BuildRun {
                    exit_code: 1,
                    output:
                        "Run out of store - interrupting threads\n*** At command \"by\" (line 567 of \"~~/src/HOL/Library/Interval.thy\")\n"
                            .into()
                },
                &theories()
            ),
            BuildOutcome::OutOfStore {
                theory: Some("HOL-Library.Interval".to_string())
            }
        );
        match classify(
            &BuildRun {
                exit_code: 2,
                output: "*** Type unification failed\n*** Failed to finish proof\n".into(),
            },
            &theories(),
        ) {
            BuildOutcome::OtherFailure { tail } => {
                assert!(tail.contains("Type unification failed"));
            }
            other => panic!("expected OtherFailure, got {other:?}"),
        }
    }

    #[test]
    fn test_isabelle_args_shape() {
        let inv = BuildInvocation {
            session: "ZP-Lib3c2i".into(),
            record_proofs: 2,
            threads: 1,
            isabelle_home: "/opt/Isabelle2025".into(),
            dirs: vec!["/w/zp_lib2".into(), "/w/zp_lib3c2i".into()],
        };
        assert_eq!(
            inv.isabelle_args(),
            vec![
                "build",
                "-b",
                "-o",
                "record_proofs=2",
                "-o",
                "threads=1",
                "-d",
                "/w/zp_lib2",
                "-d",
                "/w/zp_lib3c2i",
                "ZP-Lib3c2i",
            ]
        );
        assert_eq!(
            inv.isabelle_bin(),
            PathBuf::from("/opt/Isabelle2025/bin/isabelle")
        );
    }
}
