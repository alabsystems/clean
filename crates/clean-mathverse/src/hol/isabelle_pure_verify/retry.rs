// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Verdict-cache retry re-measure** (P2 of
//! `designs/2026-07-07-isabelle-100pct-industrial-import.md`): after a
//! *strictly-additive* translator change, re-verify **only the former reject
//! lines** against the snapshotted accepted-prefix state, instead of replaying
//! the whole multi-GB corpus.
//!
//! # Why this is sound and what it does NOT claim
//!
//! A grand replay re-verifies every line; that is the authority. This driver is
//! an *accelerator* for the iterate-on-the-translator loop. It rests on ONE
//! discipline, enforced separately by the slice gates, never by this code:
//!
//! > **Strictly-additive translator changes.** Every engine round proves "0
//! > former-KV lost" (KV name+serial dumps at slice scale) — an accepted line
//! > stays accepted, with the *same* declaration and the *same* closure entry,
//! > across the change.
//!
//! Granting that, a line the snapshot ACCEPTED is unaffected by the change, so
//! only the REJECT lines can flip. This driver:
//!
//! 1. loads the snapshot's accepted-prefix state (env + closure + registries +
//!    counters) — trusted per the discipline above, NOT per fingerprint
//!    identity, so a fingerprint mismatch is expected and merely warned
//!    ([`super::snapshot::load_snapshot_retry`]);
//! 2. re-verifies exactly the former reject lines, **in serial (= line) order**,
//!    with the CURRENT translator, on the kernel master thread — so a former
//!    reject that now verifies is inserted into the closure *before* its
//!    still-rejected consumers are translated, and flips propagate transitively
//!    in one pass (the same Kahn-ordered parallel-translate / serial-kernel
//!    split as [`super::parallel_streaming`], restricted to the reject sub-DAG);
//! 3. merges counters (the accepted set's KV count + names are kept from the
//!    snapshot; the reject-side tallies are recomputed from scratch by the
//!    pass) and writes an updated snapshot.
//!
//! The kernel is still the sole verdict mint — every accept here is a fresh
//! `add_decl` + foundational-closure check on the master, identical to the grand
//! driver. Nothing accepted is *trusted* into KV; only the accepted-prefix env
//! and closure entries (which the discipline holds invariant) are carried over.
//!
//! # Equivalence
//!
//! With the SAME translator (fingerprint match), the reject lines re-reject
//! identically (equal inputs, pure translation, same kernel), so a retry
//! reproduces the full replay's verdicts exactly — the fixture-scale gate in
//! `tests/isabelle_snapshot_resume.rs` asserts this bit-for-bit.
//!
//! # Ledger burn-down mode (`ISA_RETRY_LEDGER`)
//!
//! The plain retry above re-attempts only the *former reject* lines. A run of the
//! two-tier trusted-ledger lane ([`super::batch`]) additionally leaves behind
//! **trusted-ledger axioms** (statement-only restatements of lines that failed
//! every reconstruction arm) and **tier-2** `KernelCheckedConditional` lines
//! (kernel-re-checked *modulo* those axioms) and **bridged** lines. Every such
//! entry is a piece of standing trust surface: the instant a newly-landed prover
//! arm can prove a ledgered line *genuinely*, that line should move to tier-1
//! `KernelVerified` and its axiom should disappear — shrinking the trust surface —
//! and any tier-2 line whose support thereby collapses to the KV closure should
//! itself become KV. Re-running the whole ~30 h grand to harvest that is wasteful;
//! [`retry_ledger_enabled`] makes it an incremental pass.
//!
//! When `ISA_RETRY_LEDGER` is set, this driver re-attempts **every non-KV line of
//! the prefix** — the former rejects *and* the ledger axioms / tier-2 / bridged
//! lines — in serial order, against the byte-invariant accepted KV prefix. The
//! authoritative re-attempt set is the **corpus prefix minus the KV-closure keys**
//! (derived by a single cheap prefix scan; see the "authoritative source" note
//! on [`import_proven_theorems_retry`]), *not* the stored reject index (which omits
//! ledger/tier-2 lines) nor the `.ledger.tsv` report (which omits rejects). The KV
//! closure is the tier-1 set the two-tier design makes byte-invariant BY
//! CONSTRUCTION; everything else a fresh grand rebuilds in phase 2, so it is
//! discarded and recomputed here from a clean slate:
//!
//!  * the ledger-axiom / tier-2 / bridged **declarations are removed from the env**
//!    (they are referenced only by other non-KV lines, all of which are re-attempted,
//!    so no KV verification is lost — [`Environment::forget_decl`]'s contract) and
//!    their ledger-side closure + counters are cleared;
//!  * each non-KV line is then re-verified by the **same [`verify_one_with_translations`]
//!    path a grand uses** — phase 1 mints tier-1 KV against the KV closure ONLY
//!    (the sole KV path), phase 2 (ledger lane) re-registers a still-failing line
//!    as a ledger axiom or classifies it tier-2/bridged. A flip to KV is therefore
//!    minted by exactly the kernel path a fresh grand would take.
//!
//! CRITICAL INVARIANT preserved: the accepted KV prefix (env KV decls + KV closure
//! + KV names/count) is never touched, so **tier-1 KV byte-invariance holds
//! exactly as the two-tier design guarantees**. A ledgered line moves to tier-1
//! only via the same kernel-minted `add_decl` a grand would use; a line that still
//! fails stays ledger. Because the re-attempt set is *all* non-KV lines processed
//! in serial order against the full KV prefix (and no KV line ever depends on a
//! non-KV line — a KV proof resolves only against the KV closure), a ledger retry
//! reproduces a fresh grand's classification of the non-KV sub-corpus exactly. The
//! `tests/isabelle_ledger_retry.rs` gate asserts this equivalence at fixture scale.
//! The run reports `{ledger_attempted, ledger_flipped_to_kv, tier2_promoted}`
//! ([`LedgerRetryStats`]). Requires the ledger lane ([`super::ledger_enabled`]) ON.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::io::{Read as _, Seek as _, SeekFrom};
use std::path::{Path, PathBuf};
use std::sync::mpsc;
use std::sync::{Arc, Condvar, Mutex, RwLock};

use clean_kernel::Environment;

use super::super::isabelle_pure::{parse_proven_theorem, IsaProvenTheorem};
use super::super::isabelle_pure_translate::{
    ClassRegistry, Closure, InstanceOpRegistry, ListFnRegistry, MethodRegistry, PolyInstRegistry,
};
use super::batch::{translate_all_modes, verify_one_with_translations, ModeTranslations};
use super::parallel_streaming::{INFLIGHT_BYTE_CAP, MIN_READAHEAD, WORKER_STACK};
use super::snapshot::RejectRecord;
use super::{PureVerifiedImport, StreamError};
use crate::shard::ShardWriter;

/// The five frozen PASS-1 registries, passed by reference to the verify path.
/// Grouping them keeps the driver/helper signatures under the argument lints
/// without changing any semantics.
struct Registries<'a> {
    class: &'a ClassRegistry,
    method: &'a MethodRegistry,
    instance_op: &'a InstanceOpRegistry,
    list_fn: &'a ListFnRegistry,
    poly_inst: &'a PolyInstRegistry,
}

/// Periodic-visibility configuration for the re-attempt pass — the SAME two
/// insurances the streaming driver ([`super::streaming`]) has, wired into the
/// retry driver so a near-grand-scale ledger burn-down (which re-verifies up to
/// ~277k non-KV lines) is monitorable AND crash-recoverable instead of running
/// blind with no checkpoint. Bundled so the two re-attempt paths take one extra
/// parameter, not five. Built once by [`import_proven_theorems_retry_impl`] from
/// `ISA_PROGRESS_EVERY` / `ISA_SNAPSHOT_EVERY` + the loaded snapshot's fixed
/// prefix identity.
struct RetryVisibility<'a> {
    /// `ISA_PROGRESS_EVERY` re-attempted-line interval for the `PROGRESS:` line
    /// (0 = off; the exact format the streaming path prints so monitors work
    /// identically).
    progress_every: usize,
    /// `ISA_SNAPSHOT_EVERY` re-attempted-line interval for the `.ckpt` write
    /// (0 = off).
    snapshot_every: usize,
    /// `<ISA_SNAPSHOT_OUT>.ckpt` — `None` when checkpoints are off or no output
    /// path is configured.
    checkpoint_path: Option<PathBuf>,
    /// The snapshot prefix identity, unchanged by a retry (a retry re-verifies
    /// lines WITHIN the prefix and moves some reject→KV, but never moves the
    /// prefix boundary), so a checkpoint is a NORMAL v6 snapshot over the whole
    /// prefix at the current accepted state.
    prefix_lines: usize,
    /// See [`Self::prefix_lines`].
    prefix_bytes: u64,
    /// The loaded prefix BLAKE3, reused verbatim per checkpoint (no re-hash of
    /// the multi-GB prefix — it is byte-invariant under a retry).
    prefix_blake3: [u8; 32],
    /// The UNSEEDED non-KV records retained untouched under `ISA_RETRY_SEED`
    /// (empty without a seed). A checkpoint's reject index must carry them too, so
    /// a resume re-attempts everything still non-KV (the seed only bounds THIS
    /// pass's attempts, not the durable reject index).
    retained: &'a [RejectRecord],
}

impl RetryVisibility<'_> {
    /// After re-attempting `processed` non-KV lines (1-based), emit the periodic
    /// `PROGRESS:` line and/or write the resumable `.ckpt` checkpoint at their
    /// configured intervals. Pure telemetry + crash insurance — it never touches
    /// a verdict.
    ///
    /// `still_rejected` is the reject index accumulated so far (the residual
    /// still-rejected lines among the first `processed`) and `remaining` is the
    /// not-yet-attempted tail; together they are the complete non-KV reject index
    /// a resume from this checkpoint must carry, so a killed retry resumes from
    /// the last checkpoint (the flips already made are in the loaded env/closure;
    /// the residual + tail get re-attempted) and reaches the SAME final verdicts.
    #[allow(clippy::too_many_arguments)]
    fn tick(
        &self,
        processed: usize,
        out: &PureVerifiedImport,
        env: &Environment,
        closure: &Arc<RwLock<Closure>>,
        regs: &Registries<'_>,
        still_rejected: &[RejectRecord],
        remaining: &[RejectRecord],
    ) {
        // Periodic PROGRESS (env-gated): the SAME line the streaming path prints
        // (`super::streaming`), so a killed run still leaves a readable last
        // checkpoint in its captured stderr and monitors/dashboards parse both
        // paths identically. `processed` counts re-attempted lines.
        if self.progress_every != 0 && processed.is_multiple_of(self.progress_every) {
            eprintln!(
                "PROGRESS: processed={} KernelVerified={} rejected={}",
                processed, out.kernel_verified, out.rejected
            );
        }
        let Some(ckpt) = &self.checkpoint_path else {
            return;
        };
        if self.snapshot_every == 0 || !processed.is_multiple_of(self.snapshot_every) {
            return;
        }
        // Residual reject index for a resume: the still-rejected attempted lines
        // PLUS every not-yet-attempted line PLUS the seed-retained unseeded lines
        // — all remain non-KV in this checkpoint. Sorted ascending (= serial order)
        // so a resumed parallel retry's ascending-serial dep scheduling stays valid.
        let mut residual: Vec<RejectRecord> =
            Vec::with_capacity(still_rejected.len() + remaining.len() + self.retained.len());
        residual.extend_from_slice(still_rejected);
        residual.extend_from_slice(remaining);
        residual.extend_from_slice(self.retained);
        residual.sort_by_key(|r| r.offset);
        let closure_guard = closure.read().expect("closure read");
        let res = super::snapshot::write_checkpoint(
            ckpt,
            self.prefix_lines,
            self.prefix_bytes,
            self.prefix_blake3,
            out,
            env,
            &closure_guard,
            regs.class,
            regs.method,
            regs.instance_op,
            regs.list_fn,
            regs.poly_inst,
            &residual,
        );
        drop(closure_guard);
        match res {
            Ok(()) => eprintln!(
                "SNAPSHOT CHECKPOINT: {} ({} lines / {} bytes, KV {})",
                ckpt.display(),
                self.prefix_lines,
                self.prefix_bytes,
                out.kernel_verified
            ),
            Err(e) => eprintln!(
                "WARNING: periodic retry checkpoint at re-attempt {processed} not written to {}: {e}",
                ckpt.display()
            ),
        }
    }
}

/// One former-reject line, resolved for re-verification: its byte address (from
/// the snapshot's reject index or derived from the corpus), its serial, and its
/// in-corpus dependencies that are THEMSELVES former rejects (accepted deps are
/// already final in the preloaded closure, so they never gate scheduling).
struct RejNode {
    /// Corpus line number (the kernel anon-naming / progress index).
    line: u64,
    /// Byte offset of the line's first byte.
    offset: u64,
    /// Byte length including trailing delimiter(s).
    len: u64,
    /// Indices (into the reject-node vector) of reject-node dependencies.
    dep_nodes: Vec<u32>,
}

/// Worker → master result for one reject node.
enum RetryMsg {
    Parsed {
        idx: usize,
        thm: Box<IsaProvenTheorem>,
        translations: ModeTranslations,
    },
    ParseError {
        idx: usize,
    },
}

/// Scheduler state (mirrors [`super::parallel_streaming`], reject-node indexed).
struct Sched {
    lines: Vec<Option<String>>,
    indeg: Vec<u32>,
    dispatched: Vec<bool>,
    ready: VecDeque<usize>,
    inflight_bytes: usize,
    master_pos: usize,
    done_reading: bool,
}

/// Read exactly `len` bytes at `offset` from `file` and return the line with any
/// trailing `\n`/`\r` stripped.
fn read_line_at(file: &mut std::fs::File, offset: u64, len: u64) -> std::io::Result<String> {
    file.seek(SeekFrom::Start(offset))?;
    let len = usize::try_from(len).unwrap_or(usize::MAX);
    let mut buf = vec![0u8; len];
    file.read_exact(&mut buf)?;
    let s = String::from_utf8_lossy(&buf);
    Ok(s.trim_end_matches(['\n', '\r']).to_string())
}

/// Extract the leading `{"serial":<digits>` serial from a corpus line, or `None`.
fn leading_serial(line: &str) -> Option<i64> {
    let rest = line.strip_prefix("{\"serial\":")?;
    let digits: String = rest.chars().take_while(char::is_ascii_digit).collect();
    digits.parse::<i64>().ok()
}

/// Byte-scan a line for `"k":"thm","id":<serial>` dependency serials (the same
/// textual superset the parallel driver's index pass uses).
fn scan_dep_serials(line: &str) -> Vec<i64> {
    let needle = "\"k\":\"thm\",\"id\":";
    let mut deps = Vec::new();
    let mut start = 0usize;
    while let Some(pos) = line[start..].find(needle) {
        let at = start + pos + needle.len();
        let digits: String = line[at..]
            .chars()
            .take_while(|c| c.is_ascii_digit() || *c == '-')
            .collect();
        if let Ok(s) = digits.parse::<i64>() {
            deps.push(s);
        }
        start = at;
    }
    deps
}

/// Whether a parsed theorem's kernel name is already a declared constant in
/// `env` — i.e. this line is (contrary to the reject index) already part of the
/// trusted accepted prefix. Only reachable via the best-effort v2 derivation; a
/// genuine reject is never already declared.
fn already_declared(env: &Environment, thm: &IsaProvenTheorem, line: u64) -> bool {
    let kernel_name = if thm.serial != 0 {
        format!("isabelle.s{}", thm.serial)
    } else {
        format!("isabelle.anon.{line}")
    };
    env.get_const(&clean_kernel::name::Name::from_string(&kernel_name))
        .is_some()
}

/// After a single reject line's verdict, push it into `new_rejects` iff it STILL
/// rejected (so the updated snapshot's reject index is the residual set). A line
/// that flipped to KV bumped `kernel_verified`; a still-reject bumped `rejected`.
fn record_residual(
    out: &PureVerifiedImport,
    rejected_before: usize,
    accepted_before: usize,
    rec: RejectRecord,
    new_rejects: &mut Vec<RejectRecord>,
) {
    let flipped = out.kernel_verified > accepted_before;
    let still_reject = out.rejected > rejected_before;
    debug_assert!(
        !(flipped && still_reject),
        "a line cannot both flip and reject"
    );
    if still_reject && !flipped {
        new_rejects.push(rec);
    }
}

/// Derive the former-reject line set from a snapshot whose stored reject index
/// is empty (a v2-migrated snapshot). A corpus line is a reject candidate iff
/// its serial is NOT an accepted closure key. This over-approximates — it may
/// include serial-0 anonymous accepts — but the master's already-declared guard
/// and the empty-line check make over-inclusion harmless (a candidate that is
/// really an accept is guarded out, never recounted). Best-effort; warned.
fn derive_rejects(
    corpus: &Path,
    prefix_bytes: u64,
    closure: &Closure,
) -> Result<Vec<RejectRecord>, StreamError> {
    use std::io::BufRead as _;
    let file = std::fs::File::open(corpus)?;
    let mut reader = std::io::BufReader::new(file);
    let mut raw: Vec<u8> = Vec::new();
    let mut pos: u64 = 0;
    let mut line_no: u64 = 0;
    let mut out = Vec::new();
    loop {
        raw.clear();
        let n = reader.read_until(b'\n', &mut raw)?;
        if n == 0 || pos >= prefix_bytes {
            break;
        }
        let line_off = pos;
        pos += n as u64;
        let cur = line_no;
        line_no += 1;
        let lossy = String::from_utf8_lossy(&raw);
        let line = lossy.trim_end_matches(['\n', '\r']);
        if line.trim().is_empty() {
            continue;
        }
        let serial = leading_serial(line);
        let accepted = matches!(serial, Some(s) if s != 0 && closure.contains_key(&s));
        if !accepted {
            out.push(RejectRecord {
                line: cur,
                offset: line_off,
                len: n as u64,
            });
        }
    }
    Ok(out)
}

/// Read only the first ≤128 bytes at `offset` (bounded by the record's `len`) and
/// extract the leading `{"serial":<digits>` serial — WITHOUT materializing a
/// (potentially multi-MB) full proof line, which the seed intersection would
/// otherwise pay for every one of up to ~277k reject records. The serial sits at
/// the very start of every corpus line, so the window always covers it.
fn probe_leading_serial(
    file: &mut std::fs::File,
    offset: u64,
    len: u64,
) -> std::io::Result<Option<i64>> {
    const PROBE: u64 = 128;
    let want = usize::try_from(len.min(PROBE)).unwrap_or(0);
    if want == 0 {
        return Ok(None);
    }
    file.seek(SeekFrom::Start(offset))?;
    let mut buf = vec![0u8; want];
    file.read_exact(&mut buf)?;
    let s = String::from_utf8_lossy(&buf);
    Ok(leading_serial(s.trim_start()))
}

/// Partition `reject_records` by seed membership: the `attempt` records (leading
/// serial ∈ `seed`), the `retained` records (everything else, kept untouched so it
/// holds its snapshot verdict), and the `attempt` serial set (for the scoped ledger
/// reset). A record whose serial cannot be probed, or is `0` (anonymous), is
/// RETAINED — never attempted on a best-effort miss. Each record's serial is read
/// from a bounded 128-byte probe, so the intersection is a cheap scan even at grand
/// scale. Order within each partition is preserved (ascending, as `reject_records`
/// already is).
fn partition_by_seed(
    corpus: &Path,
    reject_records: &[RejectRecord],
    seed: &BTreeSet<i64>,
) -> Result<(Vec<RejectRecord>, Vec<RejectRecord>, BTreeSet<i64>), StreamError> {
    let mut file = std::fs::File::open(corpus)?;
    let mut attempt = Vec::new();
    let mut retained = Vec::new();
    let mut attempt_serials = BTreeSet::new();
    for rec in reject_records {
        let serial = probe_leading_serial(&mut file, rec.offset, rec.len)?;
        match serial {
            Some(s) if s != 0 && seed.contains(&s) => {
                attempt.push(*rec);
                attempt_serials.insert(s);
            }
            _ => retained.push(*rec),
        }
    }
    Ok((attempt, retained, attempt_serials))
}

/// Load the targeted re-attempt SEED (`ISA_RETRY_SEED=<file>`), if set: a set of
/// Isabelle proof-term serials, one per line, `#` starts a comment. When present,
/// [`import_proven_theorems_retry`] INTERSECTS the re-attempt set with it — only
/// these serials (that are non-KV in the snapshot) are re-verified; every OTHER
/// non-KV line RETAINS its snapshot verdict (ledger stays ledger, reject stays
/// reject). The seeded run is therefore a PARTIAL burn-down — the seed's flips are
/// the only new verdicts — and must NOT be read as a full re-measure. Efficiency
/// lever: it turns "did my narrow arm flip its target family at corpus scale,
/// 0-loss" from a full ~30 h burn-down into a minutes-scale attempt of just that
/// family. Unset (default) ⇒ `None`, the historical full re-attempt.
///
/// # Errors
/// [`StreamError::Io`] if the seed file cannot be read.
fn load_retry_seed_from_env() -> Result<Option<BTreeSet<i64>>, StreamError> {
    let Some(path) = std::env::var_os("ISA_RETRY_SEED") else {
        return Ok(None);
    };
    let path = std::path::PathBuf::from(path);
    if path.as_os_str().is_empty() {
        return Ok(None);
    }
    let content = std::fs::read_to_string(&path)?;
    let mut seed = BTreeSet::new();
    let mut bad = 0usize;
    for raw in content.lines() {
        let line = raw.split('#').next().unwrap_or("").trim();
        if line.is_empty() {
            continue;
        }
        match line.parse::<i64>() {
            Ok(s) => {
                seed.insert(s);
            }
            Err(_) => bad += 1,
        }
    }
    if bad > 0 {
        eprintln!(
            "RETRY-SEED: ignored {bad} non-integer line(s) in {}",
            path.display()
        );
    }
    Ok(Some(seed))
}

/// **Scoped** ledger-substrate reset for a SEEDED ledger retry: forget ONLY the
/// seeded attempt serials' ledger / tier-2 / bridged decls and remove their counted
/// contributions, so the re-attempt pass rebuilds exactly those from a clean slate
/// while every UNSEEDED ledger/tier-2/bridged entry is retained untouched. The
/// wholesale (non-seed) reset clears everything and re-attempts ALL non-KV lines;
/// this clears only the attempt set (the seed's partial-burn-down contract). The
/// accepted KV prefix is never touched ⇒ tier-1 KV byte-invariance holds exactly as
/// in the wholesale path.
///
/// The per-class decrements are computed from the PRE-removal classification
/// (`ledger_size == out.ledger.len()`, `kernel_bridged` counts `bridged_serials`,
/// `kernel_checked_ledger` counts the ledger-closure tier-2 keys) so each counter
/// stays exact; the re-attempt pass then re-increments for whichever seeded lines
/// re-register. Attempt serials are all non-zero (probed from real corpus lines),
/// so the serial-0 anon edge cases the whole-closure counters carry never apply.
fn scoped_ledger_reset(
    attempt_serials: &BTreeSet<i64>,
    env: &mut Environment,
    out: &mut PureVerifiedImport,
) {
    // Pre-removal ledger-serial set, so an attempted key is classified exactly.
    let led_serials: BTreeSet<i64> = out.ledger.iter().map(|e| e.serial).collect();
    let mut removed_ledger = 0usize;
    let mut removed_bridged = 0usize;
    let mut removed_tier2 = 0usize;
    for (serial, entry) in &out.ledger_closure {
        if !attempt_serials.contains(serial) {
            continue;
        }
        // Shrink the trust surface: forget this seeded line's ledger axiom / tier-2
        // / bridged decl so a flip removes it (and a still-fail re-registers it
        // cleanly). A KV proof never references these names, so no KV is lost.
        env.forget_decl(&clean_kernel::name::Name::from_string(&entry.name));
        if led_serials.contains(serial) {
            removed_ledger += 1;
        } else if out.bridged_serials.contains(serial) {
            removed_bridged += 1;
        } else {
            removed_tier2 += 1;
        }
    }
    out.ledger.retain(|e| !attempt_serials.contains(&e.serial));
    out.ledger_closure
        .retain(|s, _| !attempt_serials.contains(s));
    out.bridged_serials.retain(|s| !attempt_serials.contains(s));
    out.ledger_size = out.ledger_size.saturating_sub(removed_ledger);
    out.kernel_bridged = out.kernel_bridged.saturating_sub(removed_bridged);
    out.kernel_checked_ledger = out.kernel_checked_ledger.saturating_sub(removed_tier2);
    // `written_constants` is publish-only (a retry never publishes a shard), so it
    // is left as-is; a future full retry's wholesale reset clears it regardless.
}

/// Whether the **ledger burn-down** retry mode is enabled (env `ISA_RETRY_LEDGER`,
/// any value but `0`; default OFF). When ON, [`import_proven_theorems_retry`]
/// re-attempts every NON-KV line of the snapshot prefix — the former rejects AND
/// the two-tier trusted-ledger axioms / tier-2 conditionals / bridged lines — so a
/// ledger entry a newly-landed prover arm can now prove genuinely flips to tier-1
/// `KernelVerified` (shrinking the trusted-ledger support set), exactly as a fresh
/// grand would classify it. Requires the ledger lane itself
/// ([`super::ledger_enabled`], `ISA_TRUSTED_LEDGER`) to be ON so a still-failing
/// ledger line re-registers as a trusted-ledger axiom (rather than a bare reject);
/// the driver warns if it is not. See the module docs.
#[must_use]
pub fn retry_ledger_enabled() -> bool {
    matches!(std::env::var("ISA_RETRY_LEDGER"), Ok(v) if v != "0")
}

/// The flip report for a ledger burn-down retry: how many trusted-ledger axioms
/// and tier-2 conditionals were re-attempted, and how many the new arm promoted to
/// genuine tier-1 `KernelVerified` (each such promotion shrinks the trust surface).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct LedgerRetryStats {
    /// Former trusted-ledger axioms re-attempted (= the snapshot's ledger size).
    pub ledger_attempted: usize,
    /// Former ledger axioms now minted tier-1 `KernelVerified` by the kernel.
    pub ledger_flipped_to_kv: usize,
    /// Former tier-2 (`KernelCheckedConditional`) lines re-attempted.
    pub tier2_attempted: usize,
    /// Former tier-2 lines now minted tier-1 `KernelVerified` (their support shrank
    /// to the KV closure, so the kernel accepts them foundationally).
    pub tier2_promoted: usize,
}

/// Compute the [`LedgerRetryStats`] from the pre-retry ledger / tier-2 serial sets
/// and the POST-retry KV closure. A former ledger/tier-2 serial "flipped" exactly
/// when it now resides in the KV closure — the sole tier-1 mint. Pure: the kernel
/// already made every verdict; this only counts which former non-KV serials became
/// KV, so it needs no environment and is trivially unit-testable.
#[must_use]
pub fn compute_ledger_retry_stats(
    former_ledger_serials: &BTreeSet<i64>,
    former_tier2_serials: &BTreeSet<i64>,
    final_kv_closure: &Closure,
) -> LedgerRetryStats {
    let flipped = |set: &BTreeSet<i64>| {
        set.iter()
            .filter(|s| final_kv_closure.contains_key(s))
            .count()
    };
    LedgerRetryStats {
        ledger_attempted: former_ledger_serials.len(),
        ledger_flipped_to_kv: flipped(former_ledger_serials),
        tier2_attempted: former_tier2_serials.len(),
        tier2_promoted: flipped(former_tier2_serials),
    }
}

/// Verdict-cache retry re-measure. Re-verify only the snapshot's former reject
/// lines against its accepted-prefix state, with the current translator, and
/// write an updated snapshot. See the module docs for the trust model and the
/// equivalence guarantee.
///
/// `workers <= 1` runs the serial fallback (parse + inline-translate + verify on
/// one thread) — used by the deterministic equivalence gate. `workers > 1` fans
/// parse+translate out over the reject sub-DAG; kernel verdicts stay serial.
///
/// # Ledger burn-down mode (`ISA_RETRY_LEDGER`)
///
/// When [`retry_ledger_enabled`], the re-attempt set is widened from "former
/// rejects" to "every non-KV line of the prefix" so trusted-ledger axioms and
/// tier-2 conditionals a new arm can now prove flip to tier-1 KV. **Authoritative
/// re-attempt set:** the corpus prefix MINUS the KV-closure keys (derived from the
/// snapshot's KV closure by [`derive_rejects`]), because the KV closure is the
/// byte-invariant tier-1 set and every non-KV serial (reject, ledger, tier-2,
/// bridged) is recomputable. This is chosen over the two other candidate sources:
/// the snapshot's stored reject index (omits ledger/tier-2/bridged lines, which do
/// not increment `rejected`) and the `.ledger.tsv` report (omits plain rejects).
/// The ledger / tier-2 / bridged env decls and their ledger-side closure are reset
/// first, then the full [`verify_one_with_translations`] path (phase 1 + phase 2)
/// re-classifies each line; the accepted KV prefix is never touched, so tier-1 KV
/// stays byte-invariant. See the module docs.
///
/// # Errors
/// [`StreamError::Io`] / [`StreamError::Snapshot`] on file / snapshot failures.
pub fn import_proven_theorems_retry(
    corpus: impl AsRef<Path>,
    snapshot_path: impl AsRef<Path>,
    writer: &mut ShardWriter,
    workers: usize,
) -> Result<PureVerifiedImport, StreamError> {
    import_proven_theorems_retry_impl(
        corpus.as_ref(),
        snapshot_path.as_ref(),
        None,
        writer,
        workers,
    )
}

/// **Incremental retry** — the verdict-cache retry ([`import_proven_theorems_retry`])
/// widened for a corpus **version bump**. `corpus` is the NEW corpus version,
/// `snapshot_path` is the OLD version's completed-grand snapshot, and
/// `corpus_diff` is the [`super::super::isabelle_corpus_diff`] report between
/// them. The re-attempt set becomes: the former non-KV prefix lines (as usual)
/// **plus** the diff's NEW and CHANGED lines (the increment), all re-verified
/// against the trusted OLD-version snapshot prefix.
///
/// # Soundness — the trusted-prefix boundary
///
/// The snapshot's accepted prefix (env + KV closure + counters) is trusted only
/// if the OLD corpus's first `prefix_bytes` bytes are byte-identical in the NEW
/// corpus. This function REFUSES incremental mode (loud
/// [`StreamError::IncrementalRefused`], fall back to a full grand) the instant
/// the diff shows any CHANGED / REMOVED / INSERTED line inside that span — it
/// never silently trusts a stale prefix. For the append-only growth the AFP wave
/// produces (new declarations land as new high-serial lines after the identical
/// prefix), the check passes and only the increment is kernel-verified.
///
/// # Errors
/// [`StreamError::IncrementalRefused`] when the diff violates the trusted-prefix
/// boundary; [`StreamError::Io`] / [`StreamError::Snapshot`] on file / snapshot
/// failures.
pub fn import_proven_theorems_retry_with_diff(
    corpus: impl AsRef<Path>,
    snapshot_path: impl AsRef<Path>,
    corpus_diff: impl AsRef<Path>,
    writer: &mut ShardWriter,
    workers: usize,
) -> Result<PureVerifiedImport, StreamError> {
    import_proven_theorems_retry_impl(
        corpus.as_ref(),
        snapshot_path.as_ref(),
        Some(corpus_diff.as_ref()),
        writer,
        workers,
    )
}

/// Shared body of the plain ([`import_proven_theorems_retry`]) and incremental
/// ([`import_proven_theorems_retry_with_diff`]) retry drivers. `corpus_diff`
/// `Some` widens the re-attempt set with the diff's NEW + CHANGED lines and
/// enforces the trusted-prefix refusal.
fn import_proven_theorems_retry_impl(
    corpus: &Path,
    snapshot_path: &Path,
    corpus_diff: Option<&Path>,
    writer: &mut ShardWriter,
    workers: usize,
) -> Result<PureVerifiedImport, StreamError> {
    // Install THIS run's verify config (parsed once from env) on the master
    // thread. `retry_serial` runs inline here; `retry_parallel` installs a COPY
    // on each of its worker threads (below). See
    // [`super::super::isabelle_verify_config`].
    let cfg = crate::hol::isabelle_verify_config::VerifyConfig::from_env();
    let _cfg = cfg.install();

    // 1) Load the snapshot with RETRY fingerprint policy (mismatch is expected
    //    and warned, never fatal — see the module + snapshot docs).
    let snap = super::snapshot::load_snapshot_retry(snapshot_path)?;
    // Same corpus, unchanged bytes: the prefix hash must still match (a real
    // guard — only the translator changed, not the corpus). `ISA_SNAPSHOT_
    // SKIP_PREFIX_HASH=1` bypasses it for trusted local loops.
    super::snapshot::validate_prefix(corpus, &snap)?;

    let super::snapshot::ReplaySnapshot {
        mut out,
        mut env,
        closure,
        mut class_registry,
        mut method_registry,
        mut instance_op_registry,
        mut list_fn_registry,
        mut poly_inst_registry,
        prefix_lines,
        prefix_bytes,
        prefix_blake3,
        rejects: stored_rejects,
        ..
    } = snap;

    // INCREMENTAL mode (`--corpus-diff`): load the OLD→NEW corpus diff and enforce
    // the trusted-prefix boundary BEFORE any kernel work. `validate_prefix` above
    // already byte-checks the new corpus's `[0, prefix_bytes)` against the stored
    // hash (unless `ISA_SNAPSHOT_SKIP_PREFIX_HASH=1`); this is the *precise* guard
    // that names the offending serials and holds even when that hash is skipped.
    // A CHANGED/REMOVED/INSERTED line inside the trusted prefix ⇒ the accepted
    // prefix is stale ⇒ REFUSE (loud), never silently trust it. See the fn docs.
    let diff_seed = if let Some(diff_path) = corpus_diff {
        let diff = super::super::isabelle_corpus_diff::load_diff(diff_path).map_err(|e| {
            StreamError::IncrementalRefused(format!(
                "loading corpus-diff {}: {e}",
                diff_path.display()
            ))
        })?;
        let violations =
            super::super::isabelle_corpus_diff::incremental_prefix_violations(&diff, prefix_bytes);
        if !violations.is_empty() {
            let shown: Vec<String> = violations
                .iter()
                .take(16)
                .map(|v| format!("{} s{}@{}", v.kind, v.serial, v.offset))
                .collect();
            let more = violations.len().saturating_sub(shown.len());
            return Err(StreamError::IncrementalRefused(format!(
                "corpus-diff {} shows {} line(s) CHANGED/REMOVED/INSERTED INSIDE the snapshot's \
                 trusted accepted prefix (first {prefix_bytes} bytes): the old version's accepted \
                 prefix is NOT byte-identical in the new corpus, so an incremental retry would \
                 trust a stale snapshot. Run a FULL grand replay on the new corpus instead. \
                 Offending [{}{}]",
                diff_path.display(),
                violations.len(),
                shown.join(", "),
                if more > 0 {
                    format!(", +{more} more")
                } else {
                    String::new()
                }
            )));
        }
        eprintln!(
            "RETRY-INCREMENTAL: corpus-diff {} accepted — append-only over the {prefix_bytes}-byte \
             trusted prefix ({} new + {} changed line(s) to attempt beyond it)",
            diff_path.display(),
            diff.summary.new,
            diff.summary.changed
        );
        Some(diff)
    } else {
        None
    };

    // ALWAYS re-register the built-in def-consts onto the loaded snapshot env.
    // They are STATIC (built from Rust, no corpus scan), so this is cheap and
    // cannot alter the trusted accepted-prefix registries; but a snapshot minted
    // by a PRIOR translator predates any def-const this build added (e.g. a new
    // bnf-opaque combinator). Without this the new `_def`'s `is_bnf_def` `Eq.refl`
    // would reference an unregistered const and spuriously kernel-reject on
    // resume. `add_decl` is fail-silent for already-present decls (idempotent).
    // Kept unconditional so the fast-path (skip-refresh) branch below still gains
    // the new def-consts.
    super::streaming::register_builtin_def_consts(&mut env);

    // Additive registry refresh — **default ON** (retry-parity fix, ITEM 1 of
    // `docs/analysis/zproof-retry-parity.md`). A *registration-altering* round —
    // one that makes a new def-const, and the five PASS-1 registry entries that
    // depend on it, registrable — must recover its dependent former-reject lines
    // through `--retry-from` EXACTLY as a fresh replay does. The five registries
    // are frozen in the snapshot by the PRIOR translator, so a poly-inst entry
    // (e.g. `power_int`) that only becomes registrable once the new `HOL.If`
    // def-const exists stays absent unless we re-run the pre-passes here. This
    // mirrors the streaming RESUME path, which refreshes UNCONDITIONALLY
    // (`streaming::import_proven_theorems_streaming`) — so retry now reproduces
    // fresh/resume verdicts for the reject sub-DAG. The pre-passes are cheap
    // byte-prefiltered streams over the corpus (NOT the expensive per-line kernel
    // re-verification the retry avoids), and refresh is additive/idempotent for
    // the trusted accepted-prefix entries (`add_decl` duplicates non-fatal,
    // re-inserts overwrite equal values), so no former-KV registry entry is lost.
    //
    // Opt-out (`ISA_RETRY_SKIP_REGISTRY_REFRESH=1`): the historical fast path for
    // a PURE translation-logic change the caller KNOWS did not alter registration
    // — re-measure directly against the frozen registries, no corpus rescan.
    if std::env::var("ISA_RETRY_SKIP_REGISTRY_REFRESH").as_deref() != Ok("1") {
        super::streaming::refresh_registries(
            corpus,
            &mut env,
            &mut class_registry,
            &mut method_registry,
            &mut instance_op_registry,
            &mut list_fn_registry,
            &mut poly_inst_registry,
        )?;
    }

    // LEDGER BURN-DOWN mode (`ISA_RETRY_LEDGER`): also re-attempt the trusted
    // ledger axioms / tier-2 conditionals / bridged lines, so a ledgered line a
    // new arm can now prove flips to genuine tier-1 KV. See the module docs.
    let ledger_mode = retry_ledger_enabled();
    if ledger_mode && !super::ledger_enabled() {
        eprintln!(
            "RETRY-LEDGER WARNING: ISA_RETRY_LEDGER is set but the ledger lane \
             (ISA_TRUSTED_LEDGER) is OFF — a still-failing ledger line will fall to a bare \
             reject instead of re-registering as a trusted-ledger axiom, so the re-attempt \
             will NOT reproduce a fresh grand's classification. Set ISA_TRUSTED_LEDGER=1."
        );
    }
    // TARGETED RE-ATTEMPT SEED (`ISA_RETRY_SEED=<file>`): a caller-supplied set of
    // serials the re-attempt set is INTERSECTED with, so "did my narrow arm flip
    // its target family at corpus scale, 0-loss" is a MINUTES attempt of just that
    // family instead of the full ~30h burn-down of every non-KV line (the v3.2
    // incident: ~277k lines re-attempted to find ~54 flips from one narrow arm).
    // See [`load_retry_seed_from_env`]. `None` = the historical full re-attempt.
    let seed = load_retry_seed_from_env()?;

    // Capture the former ledger / tier-2 serial sets BEFORE any reset, for the
    // flip report ([`LedgerRetryStats`]). Ledger serials are the registered
    // trusted-ledger axioms; tier-2 serials are the remaining ledger-closure keys
    // that are neither ledger nor bridged (bridged lines carry their own tier).
    let (mut former_ledger_serials, mut former_tier2_serials): (BTreeSet<i64>, BTreeSet<i64>) =
        if ledger_mode {
            let led: BTreeSet<i64> = out.ledger.iter().map(|e| e.serial).collect();
            let tier2: BTreeSet<i64> = out
                .ledger_closure
                .keys()
                .copied()
                .filter(|s| !led.contains(s) && !out.bridged_serials.contains(s))
                .collect();
            (led, tier2)
        } else {
            (BTreeSet::new(), BTreeSet::new())
        };
    // With a seed, only the seeded ledger/tier-2 serials are actually attempted, so
    // the flip report ([`LedgerRetryStats`]) must count over the seeded subset for
    // an honest `attempted` (a ledger/tier-2 serial is non-KV by construction, so a
    // seeded one is always in the attempt set).
    if let Some(seed) = &seed {
        former_ledger_serials.retain(|s| seed.contains(s));
        former_tier2_serials.retain(|s| seed.contains(s));
    }

    // 2) Resolve the re-attempt set. In ledger mode the authoritative set is EVERY
    //    non-KV prefix line (corpus prefix MINUS the KV-closure keys) — the reject
    //    index would omit the ledger/tier-2/bridged lines. Otherwise: the stored v3
    //    index, or a derive from a v2-migrated snapshot (empty index).
    let mut reject_records: Vec<RejectRecord> = if ledger_mode {
        derive_rejects(corpus, prefix_bytes, &closure)?
    } else if stored_rejects.is_empty() {
        if out.rejected > 0 {
            eprintln!(
                "RETRY: snapshot carries no reject index (v2-migrated); deriving the \
                 former-reject set from the corpus + closure keys (best-effort — \
                 accepted lines are guarded out on the master)"
            );
            derive_rejects(corpus, prefix_bytes, &closure)?
        } else {
            Vec::new()
        }
    } else {
        stored_rejects
    };

    // INCREMENTAL seeding: append the corpus-diff's NEW + CHANGED lines (in
    // NEW-corpus coordinates) to the former non-KV prefix set. The refusal check
    // above proved every seeded line sits OUTSIDE the byte-identical accepted
    // prefix, so the former-reject records (valid in the identical prefix) and the
    // increment's new-corpus records address the SAME bytes of the new corpus —
    // coordinate-consistent. Re-sort by offset (= serial order for a serial-sorted
    // corpus, the invariant `retry_parallel`'s ascending-serial dep scheduling
    // relies on) and dedup so a line is attempted at most once.
    if let Some(diff) = &diff_seed {
        for a in &diff.new_lines {
            reject_records.push(RejectRecord {
                line: a.line,
                offset: a.offset,
                len: a.len,
            });
        }
        for c in &diff.changed_lines {
            reject_records.push(RejectRecord {
                line: c.new.line,
                offset: c.new.offset,
                len: c.new.len,
            });
        }
        reject_records.sort_by_key(|r| r.offset);
        reject_records.dedup_by_key(|r| r.offset);
        eprintln!(
            "RETRY-INCREMENTAL: re-attempt set widened to {} lines (former non-KV prefix + {} new \
             + {} changed from corpus-diff)",
            reject_records.len(),
            diff.summary.new,
            diff.summary.changed
        );
    }

    // SEED INTERSECTION: restrict the re-attempt set to the seeded serials, keeping
    // the UNSEEDED non-KV records so they RETAIN their snapshot verdict (ledger
    // stays ledger, reject stays reject).
    //
    // SOUNDNESS: a seeded line still gets the FULL real kernel re-verification
    // against the trusted prefix ([`verify_one_with_translations`], no shortcut on
    // the verdict); the seed bounds only WHICH lines are attempted, never how a
    // verdict is minted. The unseeded records are re-appended to the reject index
    // below, so a subsequent FULL retry still re-attempts them — the seeded output
    // is a PARTIAL burn-down (only the seed's flips are new), NOT a re-measure.
    let mut retained_records: Vec<RejectRecord> = Vec::new();
    let mut seeded_attempt_serials: BTreeSet<i64> = BTreeSet::new();
    if let Some(seed) = &seed {
        let total_before = reject_records.len();
        let (attempt, retained, attempt_serials) =
            partition_by_seed(corpus, &reject_records, seed)?;
        seeded_attempt_serials = attempt_serials;
        retained_records = retained;
        reject_records = attempt;
        eprintln!(
            "RETRY-SEED: {} seed serial(s) ⇒ re-attempting {} of {} non-KV line(s); {} retained \
             (verdict unchanged). PARTIAL burn-down — only the seed's flips are new, NOT a full \
             re-measure.",
            seed.len(),
            reject_records.len(),
            total_before,
            retained_records.len()
        );
    }

    let prefix_kv = out.kernel_verified;
    eprintln!(
        "RETRY{}: {prefix_lines} accepted-prefix lines trusted (KV {prefix_kv}), \
         re-verifying {} non-KV lines{}",
        if ledger_mode { "-LEDGER" } else { "" },
        reject_records.len(),
        if ledger_mode {
            format!(
                " (incl. {} ledger axioms + {} tier-2 conditionals)",
                former_ledger_serials.len(),
                former_tier2_serials.len()
            )
        } else {
            String::new()
        },
    );

    // 3) Reset the reject-side counters: the accepted set's KV count + names are
    //    kept (trusted, invariant under the additive discipline); every
    //    rejection tally is recomputed from scratch by the pass below. This makes
    //    the merged counters equal a full new-translator replay's exactly.
    out.rejected = 0;
    out.rejection_reasons.clear();
    out.rejection_specifics.clear();

    if ledger_mode && seed.is_some() {
        // SEEDED ledger reset — scope the reset to ONLY the seeded attempt serials,
        // so every UNSEEDED ledger/tier-2/bridged entry is retained untouched (the
        // seed's partial-burn-down contract: ledger stays ledger). A seeded ledger
        // line that flips has its stale axiom forgotten (trust shrinks); one that
        // still fails re-registers cleanly. See [`scoped_ledger_reset`].
        scoped_ledger_reset(&seeded_attempt_serials, &mut env, &mut out);
    } else if ledger_mode {
        // Reset the recomputed (non-KV) substrate: a fresh grand under the new arm
        // rebuilds the ledger axioms / tier-2 / bridged lines from scratch in
        // phase 2, so discard them and let the re-attempt below recompute them from
        // a clean slate. The accepted KV prefix (env KV decls + KV closure + KV
        // names/count) is deliberately NOT touched ⇒ tier-1 KV byte-invariance.
        //
        // SOUNDNESS: each removed decl is a ledger axiom (`isabelle.trusted.s*`),
        // referenced ONLY by phase-2 lines, or a tier-2 / bridged theorem
        // (`isabelle.s*`), referenced ONLY by other non-KV lines — every one of
        // which is in the re-attempt set. A KV proof resolves solely against the KV
        // closure and can never reference one of these names, so removing them
        // loses no KV verification ([`Environment::forget_decl`]'s contract) and
        // lets a still-failing ledger line re-register its axiom cleanly instead of
        // colliding with the stale one.
        for entry in out.ledger_closure.values() {
            env.forget_decl(&clean_kernel::name::Name::from_string(&entry.name));
        }
        out.kernel_checked_ledger = 0;
        out.ledger_size = 0;
        out.ledger.clear();
        out.kernel_bridged = 0;
        out.ledger_closure.clear();
        out.bridged_serials.clear();
        out.written_constants.clear();
    }

    let elide = super::elide_proofs_enabled();
    let closure = Arc::new(RwLock::new(closure));
    let regs = Registries {
        class: &class_registry,
        method: &method_registry,
        instance_op: &instance_op_registry,
        list_fn: &list_fn_registry,
        poly_inst: &poly_inst_registry,
    };

    // VISIBILITY PARITY with the streaming driver (the v3.2 burn-down incident
    // fix): a retry re-verifies up to ~277k non-KV lines — a near-grand-scale run
    // that MUST be monitorable and crash-recoverable. Read the same two intervals
    // the streaming path reads (`ISA_PROGRESS_EVERY` progress lines,
    // `ISA_SNAPSHOT_EVERY` resumable `.ckpt` checkpoints; each 0 = off). The
    // checkpoint reuses the loaded snapshot's fixed prefix identity — a retry never
    // moves the prefix boundary — so no multi-GB re-hash per checkpoint.
    let progress_every: usize = std::env::var("ISA_PROGRESS_EVERY")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0);
    let snapshot_every: usize = std::env::var("ISA_SNAPSHOT_EVERY")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0);
    let checkpoint_path: Option<PathBuf> = if snapshot_every == 0 {
        None
    } else {
        match std::env::var("ISA_SNAPSHOT_OUT")
            .ok()
            .filter(|s| !s.is_empty())
        {
            Some(out_path) => Some(PathBuf::from(format!("{out_path}.ckpt"))),
            None => {
                eprintln!(
                    "WARNING: ISA_SNAPSHOT_EVERY={snapshot_every} set but ISA_SNAPSHOT_OUT is \
                     unset — periodic retry checkpoints disabled (no output path)."
                );
                None
            }
        }
    };
    let vis = RetryVisibility {
        progress_every,
        snapshot_every,
        checkpoint_path,
        prefix_lines,
        prefix_bytes,
        prefix_blake3,
        retained: &retained_records,
    };

    // 4) Re-verify the reject set. Both paths run kernel verdicts on THIS thread
    //    in serial reject order; the still-rejected lines are recorded as the
    //    updated snapshot's reject index.
    let mut new_rejects: Vec<RejectRecord> = Vec::new();
    if workers <= 1 {
        retry_serial(
            corpus,
            &reject_records,
            &mut env,
            &closure,
            &regs,
            writer,
            &mut out,
            elide,
            &mut new_rejects,
            &vis,
        )?;
    } else {
        retry_parallel(
            corpus,
            &reject_records,
            workers,
            cfg,
            &mut env,
            &closure,
            &regs,
            writer,
            &mut out,
            elide,
            &mut new_rejects,
            &vis,
        )?;
    }

    eprintln!(
        "RETRY DONE: KV {} (was {prefix_kv} accepted-prefix; +{} recovered), still-rejected {}",
        out.kernel_verified,
        out.kernel_verified - prefix_kv,
        new_rejects.len()
    );

    // SEED: re-append the unseeded records to the reject index so a subsequent FULL
    // retry still re-attempts them (the seed bounded only THIS pass, not the durable
    // index). In LEDGER mode a resume re-derives the non-KV set from the KV closure
    // (`derive_rejects`), so the retained records need not — and, being a mix of
    // ledger/tier-2/bridged non-rejects, must not — pad the bare-reject index. Sort
    // ascending so a future parallel retry's ascending-serial dep scheduling holds.
    if !ledger_mode && !retained_records.is_empty() {
        new_rejects.extend(retained_records.iter().copied());
        new_rejects.sort_by_key(|r| r.offset);
    }

    // Ledger burn-down flip report: how many former ledger axioms / tier-2
    // conditionals the new arm promoted to genuine tier-1 KV (each shrinks the
    // trust surface). Read the POST-retry KV closure (still Arc-shared here; the
    // save block below unwraps it).
    if ledger_mode {
        let stats = {
            let kv_final = closure.read().expect("closure read");
            compute_ledger_retry_stats(&former_ledger_serials, &former_tier2_serials, &kv_final)
        };
        eprintln!(
            "RETRY-LEDGER DONE: ledger_attempted={} ledger_flipped_to_kv={} \
             tier2_attempted={} tier2_promoted={} (residual: still-ledger {}, tier-2 {})",
            stats.ledger_attempted,
            stats.ledger_flipped_to_kv,
            stats.tier2_attempted,
            stats.tier2_promoted,
            out.ledger_size,
            out.kernel_checked_ledger,
        );
    }

    // 5) Save the updated snapshot (v3) unless suppressed. Same corpus prefix
    //    (bytes/hash unchanged); the fingerprint becomes the CURRENT translator's
    //    and the reject index becomes the still-rejected set, so a subsequent
    //    retry/resume builds on the re-measured state.
    if let Some(out_path) = std::env::var("ISA_SNAPSHOT_OUT")
        .ok()
        .filter(|s| !s.is_empty())
    {
        let closure_inner = match Arc::try_unwrap(closure) {
            Ok(l) => l
                .into_inner()
                .unwrap_or_else(std::sync::PoisonError::into_inner),
            Err(arc) => arc.read().expect("closure read").clone(),
        };
        let snap = super::snapshot::ReplaySnapshot {
            fingerprint: super::snapshot::current_fingerprint(),
            prefix_lines,
            prefix_bytes,
            prefix_blake3,
            rejection_reasons: out.rejection_reasons.clone().into_iter().collect(),
            out: out.clone(),
            env,
            closure: closure_inner,
            class_registry,
            method_registry,
            instance_op_registry,
            list_fn_registry,
            poly_inst_registry,
            rejects: new_rejects,
        };
        // `None`: env-driven library path has no threaded build identity; the
        // sidecar records `"unknown"` SHA and pairs via `current_exe`.
        super::snapshot::save_snapshot(Path::new(&out_path), &snap, None)?;
        eprintln!(
            "RETRY SNAPSHOT SAVED: {out_path} (KV {})",
            out.kernel_verified
        );
    }

    Ok(out)
}

/// Serial retry: parse + translate inline + verify, one reject line at a time in
/// serial order. Transitive flips propagate through the shared closure.
#[allow(clippy::too_many_arguments)]
fn retry_serial(
    corpus: &Path,
    reject_records: &[RejectRecord],
    env: &mut Environment,
    closure: &Arc<RwLock<Closure>>,
    regs: &Registries<'_>,
    writer: &mut ShardWriter,
    out: &mut PureVerifiedImport,
    elide: bool,
    new_rejects: &mut Vec<RejectRecord>,
    vis: &RetryVisibility<'_>,
) -> Result<(), StreamError> {
    let mut file = std::fs::File::open(corpus)?;
    for (i, rec) in reject_records.iter().enumerate() {
        let processed = i + 1;
        let line = read_line_at(&mut file, rec.offset, rec.len)?;
        // An empty line and a guarded-out accept both fall through to the
        // visibility tick (never `continue`) so a checkpoint due exactly on this
        // re-attempt index is not silently skipped.
        if !line.trim().is_empty() {
            let rejected_before = out.rejected;
            let accepted_before = out.kernel_verified;
            match parse_proven_theorem(&line) {
                Err(_) => {
                    out.reject("parse-error");
                    record_residual(out, rejected_before, accepted_before, *rec, new_rejects);
                }
                Ok(thm) => {
                    if already_declared(env, &thm, rec.line) {
                        // A guarded-out accept (only reachable via v2 derivation)
                        // — already counted in the trusted prefix; do not recount.
                    } else {
                        let mut cg = closure.write().expect("closure write");
                        verify_one_with_translations(
                            &thm,
                            rec.line as usize,
                            None,
                            env,
                            &mut cg,
                            regs.class,
                            regs.method,
                            regs.instance_op,
                            regs.list_fn,
                            regs.poly_inst,
                            writer,
                            out,
                            elide,
                        );
                        drop(cg);
                        record_residual(out, rejected_before, accepted_before, *rec, new_rejects);
                    }
                }
            }
        }
        vis.tick(
            processed,
            out,
            env,
            closure,
            regs,
            new_rejects.as_slice(),
            &reject_records[processed..],
        );
    }
    Ok(())
}

/// Parallel retry: Kahn-scheduled parse+translate over the reject sub-DAG,
/// serial kernel verdicts on this thread. Structurally identical to
/// [`super::parallel_streaming`], restricted to reject nodes.
#[allow(clippy::too_many_arguments)]
fn retry_parallel(
    corpus: &Path,
    reject_records: &[RejectRecord],
    workers: usize,
    cfg: crate::hol::isabelle_verify_config::VerifyConfig,
    env: &mut Environment,
    closure: &Arc<RwLock<Closure>>,
    regs: &Registries<'_>,
    writer: &mut ShardWriter,
    out: &mut PureVerifiedImport,
    elide: bool,
    new_rejects: &mut Vec<RejectRecord>,
    vis: &RetryVisibility<'_>,
) -> Result<(), StreamError> {
    // === Index pass: read each reject line once to learn its serial + the
    // reject-node deps. Discard the line text (bounded memory). ===
    let mut nodes: Vec<RejNode> = Vec::with_capacity(reject_records.len());
    let mut dependents: Vec<Vec<u32>> = Vec::with_capacity(reject_records.len());
    {
        let mut serial_to_idx: std::collections::HashMap<i64, u32> =
            std::collections::HashMap::new();
        let mut file = std::fs::File::open(corpus)?;
        for (idx, rec) in reject_records.iter().enumerate() {
            let line = read_line_at(&mut file, rec.offset, rec.len)?;
            if let Some(serial) = leading_serial(&line) {
                if serial != 0 {
                    serial_to_idx.insert(serial, idx as u32);
                }
            }
            // Reject-node deps only: a dep serial that maps to an earlier reject
            // node (accepted deps are already final in the preloaded closure and
            // never gate scheduling). Serials are ascending, so a real dep is an
            // earlier node already in the map.
            let mut deps: Vec<u32> = scan_dep_serials(&line)
                .into_iter()
                .filter_map(|s| serial_to_idx.get(&s).copied())
                .filter(|&d| d != idx as u32)
                .collect();
            deps.sort_unstable();
            deps.dedup();
            nodes.push(RejNode {
                line: rec.line,
                offset: rec.offset,
                len: rec.len,
                dep_nodes: deps,
            });
            dependents.push(Vec::new());
        }
        for (idx, node) in nodes.iter().enumerate() {
            for &d in &node.dep_nodes {
                dependents[d as usize].push(idx as u32);
            }
        }
    }
    let n = nodes.len();

    let sched = Arc::new((
        Mutex::new(Sched {
            lines: vec![None; n],
            indeg: nodes.iter().map(|nd| nd.dep_nodes.len() as u32).collect(),
            dispatched: vec![false; n],
            ready: VecDeque::new(),
            inflight_bytes: 0,
            master_pos: 0,
            done_reading: false,
        }),
        Condvar::new(),
        Condvar::new(),
    ));
    let (tx, rx) = mpsc::sync_channel::<RetryMsg>(workers * 4);

    // Byte address of each node, for verdict recording + inflight accounting.
    let node_addr: Vec<(u64, u64, u64)> = nodes
        .iter()
        .map(|nd| (nd.line, nd.offset, nd.len))
        .collect();

    std::thread::scope(|scope| -> Result<(), StreamError> {
        // === Producer: seek+read each reject line into the scheduler. ===
        {
            let sched = Arc::clone(&sched);
            let addrs: Vec<(u64, u64)> = nodes.iter().map(|nd| (nd.offset, nd.len)).collect();
            let corpus = corpus.to_path_buf();
            scope.spawn(move || {
                let mut file = match std::fs::File::open(&corpus) {
                    Ok(f) => f,
                    Err(_) => return,
                };
                let (lock, cv_work, cv_cap) = &*sched;
                for (idx, (offset, len)) in addrs.into_iter().enumerate() {
                    let Ok(line) = read_line_at(&mut file, offset, len) else {
                        break;
                    };
                    let mut s = lock.lock().expect("scheduler lock");
                    while s.inflight_bytes > INFLIGHT_BYTE_CAP && idx > s.master_pos + MIN_READAHEAD
                    {
                        s = cv_cap.wait(s).expect("capacity wait");
                    }
                    // Account by the record's on-disk byte length (delimiter
                    // included) so the finalize-time release below is exact.
                    s.inflight_bytes += len as usize;
                    s.lines[idx] = Some(line);
                    if s.indeg[idx] == 0 && !s.dispatched[idx] {
                        s.ready.push_back(idx);
                        cv_work.notify_one();
                    }
                }
                let mut s = lock.lock().expect("scheduler lock");
                s.done_reading = true;
                cv_work.notify_all();
            });
        }

        // === Workers: parse + translate-all-modes against a dep snapshot. ===
        for _ in 0..workers {
            let sched = Arc::clone(&sched);
            let closure = Arc::clone(closure);
            let tx = tx.clone();
            let class = regs.class;
            let method = regs.method;
            let instance_op = regs.instance_op;
            let list_fn = regs.list_fn;
            let poly_inst = regs.poly_inst;
            std::thread::Builder::new()
                .stack_size(WORKER_STACK)
                .spawn_scoped(scope, move || {
                    // Install the run's verify config on this worker thread so its
                    // `translate_all_modes` budget/Miller reads match the run.
                    let _wg = cfg.install();
                    let (lock, cv_work, _cv_cap) = &*sched;
                    loop {
                        let (idx, line) = {
                            let mut s = lock.lock().expect("scheduler lock");
                            loop {
                                if let Some(idx) = s.ready.pop_front() {
                                    s.dispatched[idx] = true;
                                    let line =
                                        s.lines[idx].take().expect("ready line must be stored");
                                    break (idx, line);
                                }
                                if s.done_reading && s.master_pos >= s.lines.len() {
                                    return;
                                }
                                if s.done_reading
                                    && s.ready.is_empty()
                                    && s.dispatched.iter().all(|d| *d)
                                {
                                    return;
                                }
                                s = cv_work.wait(s).expect("work wait");
                            }
                        };
                        let msg = match parse_proven_theorem(&line) {
                            Err(_) => RetryMsg::ParseError { idx },
                            Ok(thm) => {
                                drop(line);
                                let mut dep_serials: Vec<i64> = Vec::new();
                                thm.proof.thm_deps(&mut dep_serials);
                                dep_serials.sort_unstable();
                                dep_serials.dedup();
                                let mini: Closure = {
                                    let g = closure.read().expect("closure read");
                                    dep_serials
                                        .iter()
                                        .filter_map(|s| g.get(s).map(|e| (*s, e.clone())))
                                        .collect()
                                };
                                let translations = translate_all_modes(
                                    &thm,
                                    &mini,
                                    class,
                                    method,
                                    instance_op,
                                    list_fn,
                                    poly_inst,
                                );
                                RetryMsg::Parsed {
                                    idx,
                                    thm: Box::new(thm),
                                    translations,
                                }
                            }
                        };
                        if tx.send(msg).is_err() {
                            return;
                        }
                    }
                })
                .expect("spawn worker");
        }
        drop(tx);

        // === Master: strict serial-order kernel verdicts over reject nodes. ===
        let (lock, cv_work, cv_cap) = &*sched;
        let mut buffer: BTreeMap<usize, RetryMsg> = BTreeMap::new();
        for idx in 0..n {
            while !buffer.contains_key(&idx) {
                match rx.recv() {
                    Ok(msg) => {
                        let key = match &msg {
                            RetryMsg::Parsed { idx, .. } | RetryMsg::ParseError { idx } => *idx,
                        };
                        buffer.insert(key, msg);
                    }
                    Err(_) => {
                        return Err(StreamError::Io(std::io::Error::other(
                            "retry replay: worker pool ended early",
                        )));
                    }
                }
            }
            let rejected_before = out.rejected;
            let accepted_before = out.kernel_verified;
            let mut counted = true;
            match buffer.remove(&idx).expect("buffered") {
                RetryMsg::ParseError { .. } => out.reject("parse-error"),
                RetryMsg::Parsed {
                    thm, translations, ..
                } => {
                    if already_declared(env, &thm, nodes[idx].line) {
                        counted = false;
                    } else {
                        let mut cg = closure.write().expect("closure write");
                        verify_one_with_translations(
                            &thm,
                            nodes[idx].line as usize,
                            Some(&translations),
                            env,
                            &mut cg,
                            regs.class,
                            regs.method,
                            regs.instance_op,
                            regs.list_fn,
                            regs.poly_inst,
                            writer,
                            out,
                            elide,
                        );
                    }
                }
            }
            if counted {
                let (line, offset, len) = node_addr[idx];
                record_residual(
                    out,
                    rejected_before,
                    accepted_before,
                    RejectRecord { line, offset, len },
                    new_rejects,
                );
            }
            // Finalize `idx`: advance the frontier, release capacity, wake deps.
            {
                let mut s = lock.lock().expect("scheduler lock");
                s.master_pos = idx + 1;
                s.inflight_bytes = s.inflight_bytes.saturating_sub(node_addr[idx].2 as usize);
                for &d in &dependents[idx] {
                    let d = d as usize;
                    s.indeg[d] -= 1;
                    if s.indeg[d] == 0 && s.lines[d].is_some() && !s.dispatched[d] {
                        s.ready.push_back(d);
                        cv_work.notify_one();
                    }
                }
                cv_cap.notify_all();
            }
            // Periodic PROGRESS / `.ckpt` (env-gated), AFTER the scheduler lock is
            // released — the checkpoint clones env/closure under a shared read lock
            // (concurrent with the workers' own reads), never blocking them beyond a
            // pause. `reject_records[idx + 1..]` is the not-yet-verified tail (node
            // idx maps to `reject_records[idx]` by construction).
            vis.tick(
                idx + 1,
                out,
                env,
                closure,
                regs,
                new_rejects.as_slice(),
                &reject_records[idx + 1..],
            );
        }
        {
            let _s = lock.lock().expect("scheduler lock");
            cv_work.notify_all();
        }
        Ok(())
    })?;
    Ok(())
}

#[cfg(test)]
mod ledger_retry_stats_tests {
    use super::*;
    use crate::hol::isabelle_pure_translate::ClosureEntry;
    use clean_kernel::Expr;

    /// A minimal KV closure containing exactly `serials` (the entry shape is
    /// irrelevant to [`compute_ledger_retry_stats`], which only reads the keys).
    fn kv_closure(serials: &[i64]) -> Closure {
        serials
            .iter()
            .map(|&s| {
                (
                    s,
                    ClosureEntry {
                        name: format!("isabelle.s{s}"),
                        ty: Expr::sort(clean_kernel::Level::zero()),
                        type_param_keys: Vec::new(),
                        term_param_keys: Vec::new(),
                    },
                )
            })
            .collect()
    }

    #[test]
    fn test_compute_stats_counts_only_flipped_serials_as_kv() {
        // Ledger serials {100, 200, 300}; tier-2 serials {400, 500}. After the
        // retry, the KV closure holds {100, 400} plus an unrelated KV prefix line
        // {50} — so exactly one ledger (100) and one tier-2 (400) flipped.
        let ledger: BTreeSet<i64> = [100, 200, 300].into_iter().collect();
        let tier2: BTreeSet<i64> = [400, 500].into_iter().collect();
        let kv = kv_closure(&[50, 100, 400]);
        let stats = compute_ledger_retry_stats(&ledger, &tier2, &kv);
        assert_eq!(stats.ledger_attempted, 3);
        assert_eq!(stats.ledger_flipped_to_kv, 1, "only serial 100 became KV");
        assert_eq!(stats.tier2_attempted, 2);
        assert_eq!(stats.tier2_promoted, 1, "only serial 400 became KV");
    }

    #[test]
    fn test_compute_stats_no_flips_when_kv_closure_disjoint() {
        let ledger: BTreeSet<i64> = [100, 200].into_iter().collect();
        let tier2: BTreeSet<i64> = [300].into_iter().collect();
        // KV prefix untouched by any former non-KV serial.
        let kv = kv_closure(&[1, 2, 3]);
        let stats = compute_ledger_retry_stats(&ledger, &tier2, &kv);
        assert_eq!(stats.ledger_attempted, 2);
        assert_eq!(stats.ledger_flipped_to_kv, 0);
        assert_eq!(stats.tier2_promoted, 0);
    }

    #[test]
    fn test_compute_stats_empty_sets_are_zero() {
        let stats =
            compute_ledger_retry_stats(&BTreeSet::new(), &BTreeSet::new(), &kv_closure(&[7]));
        assert_eq!(stats, LedgerRetryStats::default());
    }
}
