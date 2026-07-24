// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Durable capture-chain state file (JSON). It records the CURRENT working plan
//! (segments, possibly rewritten by bisect / proofless), each segment's status,
//! attempt history, and which response-ladder rungs have been taken — so
//! `--resume` picks up exactly where a crash or halt left off and never retries
//! a rung it already exhausted.

use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

use super::error::CaptureChainError;
use super::spec::{ChainSpec, Segment};

/// Terminal or in-progress status of one working segment.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SegStatus {
    /// Not yet built (or mid-ladder, awaiting a retry/proofless re-run).
    Pending,
    /// Built successfully at its current record_proofs.
    Ok,
    /// Built successfully after being demoted to a proofless (record_proofs=2)
    /// heap-bake — its theorems import proofless.
    Proofless,
    /// Halted on a non-OOM failure (the driver stops the chain here).
    Failed,
}

/// One recorded build attempt, for auditability and resume.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Attempt {
    /// Threads the attempt ran with.
    pub threads: usize,
    /// record_proofs the attempt ran with.
    pub record_proofs: u32,
    /// `"ok"` / `"out_of_store"` / `"other_failure"`.
    pub outcome: String,
    /// The OOM culprit theory, when the attempt ran out of store.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub theory: Option<String>,
    /// Unix seconds when the attempt finished.
    pub at: u64,
}

/// Which response-ladder rungs a segment has already taken (so a resume does
/// not repeat an exhausted rung).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct LadderTaken {
    /// Rung A: retried at threads=1 after a concurrent (threads>1) OOM.
    pub retry_threads1: bool,
    /// Rung B: bisected into two sub-segments (this segment is then replaced).
    pub bisected: bool,
    /// Rung C: demoted to record_proofs=2 (proofless heap-bake).
    pub made_proofless: bool,
}

/// The runtime state of one working segment.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SegmentState {
    /// The (possibly-rewritten) segment: bisect renames it, proofless lowers its
    /// record_proofs. ROOT generation reads this.
    pub segment: Segment,
    /// The effective thread count for this segment (lowered to 1 by rung A).
    pub threads: usize,
    /// Current status.
    pub status: SegStatus,
    /// The theory that forced a proofless demotion, when `status == Proofless`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub proofless_theory: Option<String>,
    /// Attempt history (most recent last).
    #[serde(default)]
    pub attempts: Vec<Attempt>,
    /// Ladder rungs already taken.
    #[serde(default)]
    pub ladder: LadderTaken,
}

impl SegmentState {
    /// A fresh, pending working segment from a spec segment at `global_threads`.
    #[must_use]
    pub fn fresh(segment: Segment, global_threads: usize) -> Self {
        Self {
            segment,
            threads: global_threads,
            status: SegStatus::Pending,
            proofless_theory: None,
            attempts: Vec::new(),
            ladder: LadderTaken::default(),
        }
    }

    /// Whether this segment is already resolved (built ok or proofless) and can
    /// be skipped on resume.
    #[must_use]
    pub fn is_resolved(&self) -> bool {
        matches!(self.status, SegStatus::Ok | SegStatus::Proofless)
    }
}

/// The whole durable state: spec hash + the current working plan.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ChainState {
    /// SHA-256 of the ORIGINAL spec, so a resume against a changed spec is
    /// refused.
    pub spec_hash: String,
    /// The current working segments (post any bisect/proofless rewrites).
    pub segments: Vec<SegmentState>,
    /// Total bisects performed across the run (durable audit counter).
    #[serde(default)]
    pub bisects: usize,
    /// Total threads>1 → threads=1 retries performed (durable audit counter).
    #[serde(default)]
    pub retries_threads1: usize,
}

impl ChainState {
    /// Initialize a fresh state from a spec.
    #[must_use]
    pub fn initial(spec: &ChainSpec) -> Self {
        Self {
            spec_hash: spec.content_hash(),
            segments: spec
                .segments
                .iter()
                .cloned()
                .map(|s| SegmentState::fresh(s, spec.threads))
                .collect(),
            bisects: 0,
            retries_threads1: 0,
        }
    }

    /// Load state from `path`.
    ///
    /// # Errors
    /// [`CaptureChainError::StateRead`] / [`CaptureChainError::StateParse`].
    pub fn load(path: &Path) -> Result<Self, CaptureChainError> {
        let bytes = std::fs::read(path).map_err(|source| CaptureChainError::StateRead {
            path: path.to_path_buf(),
            source,
        })?;
        serde_json::from_slice(&bytes).map_err(|source| CaptureChainError::StateParse {
            path: path.to_path_buf(),
            source,
        })
    }

    /// Atomically persist state to `path` (write a temp file, then rename) so a
    /// crash mid-write never truncates the authoritative state.
    ///
    /// # Errors
    /// [`CaptureChainError::StateWrite`] on any IO failure.
    pub fn save(&self, path: &Path) -> Result<(), CaptureChainError> {
        let json = serde_json::to_vec_pretty(self).map_err(|e| CaptureChainError::StateWrite {
            path: path.to_path_buf(),
            source: std::io::Error::other(e),
        })?;
        let tmp = tmp_sibling(path);
        std::fs::write(&tmp, &json).map_err(|source| CaptureChainError::StateWrite {
            path: tmp.clone(),
            source,
        })?;
        std::fs::rename(&tmp, path).map_err(|source| CaptureChainError::StateWrite {
            path: path.to_path_buf(),
            source,
        })
    }

    /// Confirm this loaded state matches `spec` (for `--resume`).
    ///
    /// # Errors
    /// [`CaptureChainError::SpecChanged`] if the recorded hash differs.
    pub fn ensure_matches(&self, spec: &ChainSpec) -> Result<(), CaptureChainError> {
        let spec_hash = spec.content_hash();
        if self.spec_hash != spec_hash {
            return Err(CaptureChainError::SpecChanged {
                state_hash: self.spec_hash.clone(),
                spec_hash,
            });
        }
        Ok(())
    }
}

/// A `.tmp` sibling path for atomic writes.
fn tmp_sibling(path: &Path) -> PathBuf {
    let mut name = path.file_name().map_or_else(
        || std::ffi::OsString::from("state"),
        std::ffi::OsStr::to_os_string,
    );
    name.push(".tmp");
    path.with_file_name(name)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hol::isabelle_capture_chain::spec::CollectSpec;

    fn spec() -> ChainSpec {
        ChainSpec {
            segments: vec![
                Segment {
                    session: "ZP-A".into(),
                    dir: "zp_a".into(),
                    theories: vec!["HOL-Library.Foo".into()],
                    parent: "ZP-Base".into(),
                    record_proofs: 4,
                    note: None,
                },
                Segment {
                    session: "ZP-B".into(),
                    dir: "zp_b".into(),
                    theories: vec!["HOL-Library.Bar".into()],
                    parent: "ZP-A".into(),
                    record_proofs: 4,
                    note: None,
                },
            ],
            isabelle_home: "/opt".into(),
            dirs: vec!["zp_base".into()],
            threads: 1,
            collect: CollectSpec {
                from_dir: "f".into(),
                to_dir: "t".into(),
                glob: "*.jsonl".into(),
            },
            comment: None,
        }
    }

    #[test]
    fn test_initial_state_all_pending_with_spec_threads() {
        let s = ChainState::initial(&spec());
        assert_eq!(s.segments.len(), 2);
        assert!(s.segments.iter().all(|x| x.status == SegStatus::Pending));
        assert!(s.segments.iter().all(|x| x.threads == 1));
        assert_eq!(s.spec_hash.len(), 64);
    }

    #[test]
    fn test_save_load_roundtrip_and_resume_skip() {
        let dir = std::env::temp_dir().join(format!("cc_state_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("mk tmp");
        let path = dir.join("state.json");
        let mut s = ChainState::initial(&spec());
        s.segments[0].status = SegStatus::Ok;
        s.save(&path).expect("save state");
        let loaded = ChainState::load(&path).expect("load state");
        assert_eq!(loaded, s, "roundtrip is lossless");
        assert!(loaded.segments[0].is_resolved(), "ok segment is resolved");
        assert!(
            !loaded.segments[1].is_resolved(),
            "pending segment is not resolved"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_ensure_matches_detects_changed_spec() {
        let s = ChainState::initial(&spec());
        s.ensure_matches(&spec()).expect("same spec matches");
        let mut changed = spec();
        changed.threads = 6;
        assert!(matches!(
            s.ensure_matches(&changed),
            Err(CaptureChainError::SpecChanged { .. })
        ));
    }
}
