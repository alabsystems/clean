// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! RAM-aware default worker count for the PARAGON `--parallel` verifier
//! (Track B2).
//!
//! PARAGON's peak RSS is `base + jobs * (one module's shard buffer + its
//! reconstructed terms)`. Defaulting `jobs` to `nproc` (logical CPU count)
//! ignores RAM entirely, so on a many-core but memory-limited host the heavy
//! subtrees (Analysis / Topology / CategoryTheory / SetTheory) over-subscribe
//! memory and the OS jetsam-kills the run (SetTheory already fails rc=138 that
//! way). Clamping `jobs` caps the peak.
//!
//! This mirrors the proven clamp the corpus-sharded driver uses
//! (`mathverse_shard verify-kernel --corpus-sharded`): `min(cpus, max(1,
//! ram_gib / PER_WORKER_GIB))`. The clamp applies ONLY to the default — an
//! explicit `--jobs N` is always honored verbatim, so an operator with headroom
//! can still raise it.
//!
//! Soundness-neutral: scheduling only. The number of workers never changes any
//! constant's verdict — each worker runs the identical read-only
//! `check_decl_readonly` against the same shared base.

/// Per-worker RAM budget in GiB. Each PARAGON worker holds, at peak, one
/// module's reconstructed term forest plus its shard buffer on top of the shared
/// base; 12 GiB is the conservative figure the corpus-sharded driver settled on
/// after the 2026-06-22 OOM/jetsam incident.
pub const PER_WORKER_GIB: u64 = 12;

/// Clamp a default worker count to what physical RAM can hold.
///
/// Pure function of `cpus` and `ram_gib` so it is unit-testable without touching
/// the host. `ram_gib == None` means "RAM unknown" — we stay conservative
/// (`min(cpus, 4)`) rather than trust `nproc`. With a known RAM figure the bound
/// is `max(1, ram_gib / PER_WORKER_GIB)`; the result is always `>= 1`.
#[must_use]
pub fn clamp_jobs_for_ram(cpus: usize, ram_gib: Option<u64>) -> usize {
    let cpus = cpus.max(1);
    match ram_gib {
        None => cpus.min(4),
        Some(ram_gib) => {
            let ram_bound = std::cmp::max(1, (ram_gib / PER_WORKER_GIB) as usize);
            cpus.min(ram_bound)
        }
    }
}

/// The RAM-aware default worker count for PARAGON `--parallel` (used only when
/// the user did NOT pass `--jobs`).
#[must_use]
pub fn ram_aware_default_jobs() -> usize {
    let cpus = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4);
    clamp_jobs_for_ram(cpus, total_ram_gib())
}

/// Best-effort total physical RAM in GiB (macOS `hw.memsize`, Linux
/// `/proc/meminfo`). Returns `None` if it cannot be determined. Identical recipe
/// to the corpus-sharded driver's `total_ram_gib`.
fn total_ram_gib() -> Option<u64> {
    #[cfg(target_os = "macos")]
    {
        let out = std::process::Command::new("sysctl")
            .args(["-n", "hw.memsize"])
            .output()
            .ok()?;
        let bytes: u64 = String::from_utf8_lossy(&out.stdout).trim().parse().ok()?;
        Some(bytes / (1024 * 1024 * 1024))
    }
    #[cfg(not(target_os = "macos"))]
    {
        let text = std::fs::read_to_string("/proc/meminfo").ok()?;
        text.lines()
            .find_map(|line| line.strip_prefix("MemTotal:"))
            .and_then(|rest| rest.split_whitespace().next())
            .and_then(|kb| kb.parse::<u64>().ok())
            .map(|kb| kb / (1024 * 1024))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_clamp_jobs_low_ram_caps_below_cpus() {
        // 24 GiB host, 16 cores: 24/12 = 2 jobs (NOT 16) — the SetTheory-jetsam
        // case the clamp exists to prevent.
        assert_eq!(clamp_jobs_for_ram(16, Some(24)), 2);
        // 15 GiB host (this validation box): 15/12 = 1 job.
        assert_eq!(clamp_jobs_for_ram(16, Some(15)), 1);
    }

    #[test]
    fn test_clamp_jobs_high_ram_uses_all_cpus() {
        // 256 GiB host, 8 cores: RAM bound 21 >> 8, so all 8 cores are used.
        assert_eq!(clamp_jobs_for_ram(8, Some(256)), 8);
    }

    #[test]
    fn test_clamp_jobs_always_at_least_one() {
        // Tiny RAM must never yield 0 workers (would deadlock the pool).
        assert_eq!(clamp_jobs_for_ram(8, Some(1)), 1);
        assert_eq!(clamp_jobs_for_ram(8, Some(0)), 1);
        assert_eq!(clamp_jobs_for_ram(0, Some(64)), 1);
    }

    #[test]
    fn test_clamp_jobs_unknown_ram_is_conservative() {
        // RAM unknown -> min(cpus, 4), never trust raw nproc.
        assert_eq!(clamp_jobs_for_ram(32, None), 4);
        assert_eq!(clamp_jobs_for_ram(2, None), 2);
    }

    #[test]
    fn test_clamp_jobs_exact_multiple() {
        // 48 GiB / 12 = 4; with 4 cores that is exactly 4.
        assert_eq!(clamp_jobs_for_ram(4, Some(48)), 4);
        // 36 GiB / 12 = 3, clamps 8 cores down to 3.
        assert_eq!(clamp_jobs_for_ram(8, Some(36)), 3);
    }
}
