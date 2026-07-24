// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! External checker abstraction for independent verification backends.

use clean_kernel::vc_protocol::{VcBatch, VcObligation};
use serde::{Deserialize, Serialize};
use std::collections::VecDeque;
use std::io::{Read, Write};
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::Mutex;
use std::thread;
use std::time::{Duration, Instant};

/// Verdict returned by an independent checker.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum CheckerVerdict {
    /// The obligation was independently verified.
    Verified,
    /// The checker rejected the obligation with an explanation.
    Rejected { reason: String },
    /// The checker timed out.
    Timeout,
    /// The checker does not support this obligation shape.
    Unsupported,
}

/// JSON response produced by an external checker process.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CheckerBatchResponse {
    /// Per-obligation verdicts in request order.
    pub verdicts: Vec<CheckerVerdict>,
}

/// Errors returned while invoking an external checker backend.
#[derive(Debug, thiserror::Error)]
pub enum CheckerError {
    /// Failed to encode the JSON request.
    #[error("failed to encode checker request: {0}")]
    Encode(#[source] serde_json::Error),
    /// Failed to decode the JSON response.
    #[error("failed to decode checker response: {0}")]
    Decode(#[source] serde_json::Error),
    /// Failed to spawn the checker process.
    #[error("failed to spawn checker `{program}`: {source}")]
    Spawn {
        /// Program path or name.
        program: String,
        /// Underlying OS error.
        #[source]
        source: std::io::Error,
    },
    /// StdIO communication with the checker failed.
    #[error("checker I/O failed: {0}")]
    Io(#[from] std::io::Error),
    /// The checker process exited unsuccessfully.
    #[error("checker exited with code {code:?}: {stderr}")]
    Exit {
        /// Exit status code, if available.
        code: Option<i32>,
        /// Stderr collected from the process.
        stderr: String,
    },
    /// The checker returned an invalid response shape.
    #[error("checker protocol error: {0}")]
    Protocol(String),
}

/// Pluggable interface for independent verification backends.
pub trait ExternalChecker: Send + Sync {
    /// Check a single obligation.
    fn check_obligation(&self, obligation: &VcObligation) -> Result<CheckerVerdict, CheckerError>;

    /// Check a batch of obligations.
    fn check_batch(&self, batch: &VcBatch) -> Result<Vec<CheckerVerdict>, CheckerError> {
        batch
            .obligations
            .iter()
            .map(|obligation| self.check_obligation(obligation))
            .collect()
    }
}

/// External checker backed by a subprocess speaking JSON over stdin/stdout.
#[derive(Clone, Debug)]
pub struct ProcessChecker {
    program: PathBuf,
    args: Vec<String>,
    timeout: Option<Duration>,
}

impl ProcessChecker {
    /// Create a checker that spawns `program`.
    #[must_use]
    pub fn new(program: impl Into<PathBuf>) -> Self {
        Self {
            program: program.into(),
            args: Vec::new(),
            timeout: None,
        }
    }

    /// Append a command-line argument.
    #[must_use]
    pub fn arg(mut self, arg: impl Into<String>) -> Self {
        self.args.push(arg.into());
        self
    }

    /// Set a wall-clock timeout for one process invocation.
    #[must_use]
    pub fn timeout(mut self, timeout: Duration) -> Self {
        self.timeout = Some(timeout);
        self
    }

    fn run_batch(&self, batch: &VcBatch) -> Result<Vec<CheckerVerdict>, CheckerError> {
        if batch.obligations.is_empty() {
            return Ok(Vec::new());
        }

        let payload = serde_json::to_string(batch).map_err(CheckerError::Encode)?;
        let mut child = Command::new(&self.program)
            .args(&self.args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|source| CheckerError::Spawn {
                program: self.program.display().to_string(),
                source,
            })?;

        let mut stdin = child
            .stdin
            .take()
            .ok_or_else(|| CheckerError::Protocol("checker stdin was not piped".to_string()))?;
        let mut stdout = child
            .stdout
            .take()
            .ok_or_else(|| CheckerError::Protocol("checker stdout was not piped".to_string()))?;
        let mut stderr = child
            .stderr
            .take()
            .ok_or_else(|| CheckerError::Protocol("checker stderr was not piped".to_string()))?;

        stdin.write_all(payload.as_bytes())?;
        stdin.write_all(b"\n")?;
        drop(stdin);

        let status = if let Some(timeout) = self.timeout {
            let deadline = Instant::now() + timeout;
            loop {
                match child.try_wait()? {
                    Some(status) => break status,
                    None if Instant::now() >= deadline => {
                        let _ = child.kill();
                        let _ = child.wait();
                        return Ok(vec![CheckerVerdict::Timeout; batch.obligations.len()]);
                    }
                    None => thread::sleep(Duration::from_millis(10)),
                }
            }
        } else {
            child.wait()?
        };

        let mut stdout_buf = String::new();
        let mut stderr_buf = String::new();
        stdout.read_to_string(&mut stdout_buf)?;
        stderr.read_to_string(&mut stderr_buf)?;

        if !status.success() {
            return Err(CheckerError::Exit {
                code: status.code(),
                stderr: stderr_buf.trim().to_string(),
            });
        }

        let response: CheckerBatchResponse =
            serde_json::from_str(stdout_buf.trim()).map_err(CheckerError::Decode)?;
        if response.verdicts.len() != batch.obligations.len() {
            return Err(CheckerError::Protocol(format!(
                "expected {} verdicts, got {}",
                batch.obligations.len(),
                response.verdicts.len()
            )));
        }
        Ok(response.verdicts)
    }
}

impl ExternalChecker for ProcessChecker {
    fn check_obligation(&self, obligation: &VcObligation) -> Result<CheckerVerdict, CheckerError> {
        let mut verdicts = self.run_batch(&VcBatch {
            obligations: vec![obligation.clone()],
        })?;
        verdicts
            .pop()
            .ok_or_else(|| CheckerError::Protocol("checker returned no verdict".to_string()))
    }

    fn check_batch(&self, batch: &VcBatch) -> Result<Vec<CheckerVerdict>, CheckerError> {
        self.run_batch(batch)
    }
}

/// In-memory checker for tests and higher-level flow wiring.
#[derive(Debug, Default)]
pub struct MockChecker {
    verdicts: Mutex<VecDeque<CheckerVerdict>>,
    seen: Mutex<Vec<VcObligation>>,
}

impl MockChecker {
    /// Create a mock checker seeded with queued verdicts.
    #[must_use]
    pub fn new(verdicts: impl IntoIterator<Item = CheckerVerdict>) -> Self {
        Self {
            verdicts: Mutex::new(verdicts.into_iter().collect()),
            seen: Mutex::new(Vec::new()),
        }
    }

    /// Push another queued verdict.
    pub fn push_verdict(&self, verdict: CheckerVerdict) {
        self.verdicts
            .lock()
            .expect("mock checker verdict queue poisoned")
            .push_back(verdict);
    }

    /// Return all obligations observed by this mock.
    #[must_use]
    pub fn seen_obligations(&self) -> Vec<VcObligation> {
        self.seen
            .lock()
            .expect("mock checker seen queue poisoned")
            .clone()
    }
}

impl ExternalChecker for MockChecker {
    fn check_obligation(&self, obligation: &VcObligation) -> Result<CheckerVerdict, CheckerError> {
        self.seen
            .lock()
            .expect("mock checker seen queue poisoned")
            .push(obligation.clone());

        Ok(self
            .verdicts
            .lock()
            .expect("mock checker verdict queue poisoned")
            .pop_front()
            .unwrap_or(CheckerVerdict::Unsupported))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{vc_protocol::VcHypothesis, Expr};

    fn obligation(name: &str) -> VcObligation {
        VcObligation {
            name: name.to_string(),
            goal_type: Expr::prop(),
            hypotheses: vec![VcHypothesis {
                name: "h".to_string(),
                type_: Expr::prop(),
            }],
            source_file: Some("src/demo.lean".to_string()),
            source_line: Some(7),
        }
    }

    #[test]
    fn checker_verdict_parses_from_json() {
        let cases = [
            (r#"{"kind":"verified"}"#, CheckerVerdict::Verified),
            (
                r#"{"kind":"rejected","reason":"counterexample"}"#,
                CheckerVerdict::Rejected {
                    reason: "counterexample".to_string(),
                },
            ),
            (r#"{"kind":"timeout"}"#, CheckerVerdict::Timeout),
            (r#"{"kind":"unsupported"}"#, CheckerVerdict::Unsupported),
        ];

        for (json, expected) in cases {
            let parsed: CheckerVerdict =
                serde_json::from_str(json).expect("verdict should deserialize");
            assert_eq!(parsed, expected);
        }
    }

    #[test]
    fn mock_checker_records_flow_and_uses_queued_verdicts() {
        let checker = MockChecker::new([
            CheckerVerdict::Verified,
            CheckerVerdict::Rejected {
                reason: "bad dependency".to_string(),
            },
        ]);
        let first = obligation("goal.one");
        let second = obligation("goal.two");

        assert_eq!(
            checker
                .check_obligation(&first)
                .expect("first verdict should be available"),
            CheckerVerdict::Verified
        );
        assert_eq!(
            checker
                .check_obligation(&second)
                .expect("second verdict should be available"),
            CheckerVerdict::Rejected {
                reason: "bad dependency".to_string(),
            }
        );
        assert_eq!(
            checker
                .check_obligation(&obligation("goal.three"))
                .expect("empty queue falls back to unsupported"),
            CheckerVerdict::Unsupported
        );

        let seen = checker.seen_obligations();
        assert_eq!(seen.len(), 3);
        assert_eq!(seen[0].name, "goal.one");
        assert_eq!(seen[1].name, "goal.two");
        assert_eq!(seen[2].name, "goal.three");
    }
}
