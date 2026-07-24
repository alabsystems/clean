// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Per-tactic heartbeat profiling for the extended tactic interpreter.
//!
//! This module defines [`TacticHeartbeatProfile`]: a compact per-bucket
//! heartbeat breakdown produced by `tactic_interp_ext` when the config flag
//! `profile_heartbeats` is enabled. On a heartbeat overflow the interpreter
//! formats a ranked top-N breakdown and embeds it in the returned
//! `ElabError` so proof authors can see which tactic (by name) or
//! structural combinator dominated the cost.
//!
//! Part of #3399.

use std::collections::HashMap;

/// Build a `TacticHeartbeatProfile` from a bucket map and totals.
///
/// Buckets are sorted by count descending, with name-ascending tie-breaks
/// for deterministic output.
#[must_use]
pub(crate) fn build_profile(
    buckets: &HashMap<String, u64>,
    total: u64,
    limit: u64,
) -> TacticHeartbeatProfile {
    let mut top: Vec<(String, u64)> = buckets.iter().map(|(n, c)| (n.clone(), *c)).collect();
    top.sort_by(|(ln, lc), (rn, rc)| rc.cmp(lc).then_with(|| ln.cmp(rn)));
    TacticHeartbeatProfile {
        total,
        limit,
        top_buckets: top,
    }
}

/// Per-tactic heartbeat profile collected by the extended tactic interpreter.
///
/// Records how many heartbeats each named bucket consumed and the total
/// count. When the interpreter exceeds its budget with
/// `profile_heartbeats = true`, the formatted top-N breakdown is attached to
/// the `ElabError` message so proof authors can see which tactic dominated
/// the cost.
#[derive(Debug, Clone, Default)]
pub(crate) struct TacticHeartbeatProfile {
    /// Total heartbeats consumed (across all buckets).
    pub(crate) total: u64,
    /// Configured heartbeat limit (for percentage display).
    pub(crate) limit: u64,
    /// Ordered list of `(bucket_name, heartbeats)` sorted descending.
    pub(crate) top_buckets: Vec<(String, u64)>,
}

impl TacticHeartbeatProfile {
    /// Format a compact top-N breakdown suitable for embedding in errors.
    ///
    /// The `n` parameter caps how many buckets appear. Returns an empty
    /// string when no buckets have been recorded (profiling disabled), so
    /// callers can unconditionally concatenate it into error messages.
    #[must_use]
    pub(crate) fn format_top(&self, n: usize) -> String {
        if self.top_buckets.is_empty() {
            return String::new();
        }
        let mut out = format!(
            "\n\nTactic heartbeat profile ({}/{})",
            self.total, self.limit
        );
        let top = self.top_buckets.iter().take(n);
        for (bucket, count) in top {
            let pct = if self.total > 0 {
                (*count as f64 / self.total as f64) * 100.0
            } else {
                0.0
            };
            out.push_str(&format!(
                "\n  {:<24} {:>10} hb ({:.1}%)",
                bucket, count, pct
            ));
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `format_top` caps output at N buckets.
    #[test]
    fn test_format_top_caps_at_n() {
        let profile = TacticHeartbeatProfile {
            total: 6,
            limit: 100,
            top_buckets: vec![("a".into(), 3), ("b".into(), 2), ("c".into(), 1)],
        };
        let out = profile.format_top(2);
        assert!(out.contains("Tactic heartbeat profile (6/100)"));
        assert!(out.contains("a"));
        assert!(out.contains("b"));
        assert!(
            !out.contains("\n  c "),
            "c should be truncated when n=2, got: {out}"
        );
    }

    /// `format_top` returns an empty string when no buckets were recorded.
    #[test]
    fn test_format_top_empty_when_no_buckets() {
        let profile = TacticHeartbeatProfile {
            total: 0,
            limit: 100,
            top_buckets: vec![],
        };
        assert_eq!(profile.format_top(10), "");
    }

    /// `format_top` still emits a header when buckets are present but total
    /// is zero (degenerate case — shouldn't happen in practice).
    #[test]
    fn test_format_top_zero_total_with_buckets_emits_header() {
        let profile = TacticHeartbeatProfile {
            total: 0,
            limit: 100,
            top_buckets: vec![("a".into(), 0)],
        };
        let out = profile.format_top(10);
        assert!(out.contains("Tactic heartbeat profile (0/100)"));
        assert!(out.contains("(0.0%)"));
    }
}
