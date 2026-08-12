// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Closure-replay driver: translate a batch of Pure-proof theorems, re-check
//! each with clean's kernel **in dependency order**, and write the genuinely
//! verified ones into a `.mathverse` shard as [`ImportConfidence::KernelVerified`].
//!
//! This is the importer that turns real Isabelle/HOL library proofs into
//! kernel-verified Mathverse entries. Unlike the per-primitive
//! [`super::isabelle_verified`] path, it consumes whole-theorem **Pure proof
//! terms** (`record_proofs=2`) and resolves each theorem's `PThm` dependencies
//! against the **accumulating environment** of already-verified theorems — the
//! "closure replay". A theorem is stamped `KernelVerified` only if:
//!
//! 1. its proof translates ([`super::isabelle_pure_translate::translate_theorem`]),
//! 2. clean's kernel `add_decl` accepts `value : type` in the accumulating env,
//!    and
//! 3. its transitive axiom closure is `⊆ FOUNDATIONAL_AXIOMS`.
//!
//! Anything that fails — an unmapped base axiom, an oracle hole, an unresolved
//! dependency, or a rejected proof — is counted (and optionally surfaced) but
//! **never** stamped verified. Nothing is `KernelVerified` the kernel did not
//! accept.

use std::collections::{BTreeMap, BTreeSet};

use super::isabelle_pure_translate::{Closure, TranslateError};
use crate::shard::ShardWriter;
#[cfg(test)]
use crate::types::ImportConfidence;

mod batch;
mod bridge_witness;
mod dump;
mod parallel_streaming;
mod register;
mod retry;
pub mod shard_group;
pub mod shard_mathverse;
pub mod shard_verify;
pub mod snapshot;
mod streaming;
pub mod verify_lock;

pub use batch::import_proven_theorems;
pub use parallel_streaming::import_proven_theorems_parallel;
pub use retry::{
    compute_ledger_retry_stats, import_proven_theorems_retry,
    import_proven_theorems_retry_with_diff, retry_ledger_enabled, LedgerRetryStats,
};
pub use shard_group::{
    run_shard_group_in_process, run_shard_group_subprocess, ChildCommand, ShardGroupError,
    ShardGroupOpts,
};
pub use shard_mathverse::{import_proven_theorems_streaming_shard_emit, merge_shard_mathverse};
pub use shard_verify::{
    export_prepass_snapshot, import_proven_theorems_streaming_shard,
    import_proven_theorems_streaming_shard_prepass, merge_shard_verdicts, MergedVerdicts,
    ShardSpec, ShardVerdicts,
};
pub use streaming::import_proven_theorems_streaming;
pub use verify_lock::{SideLeaseError, SideVerifyLease, VerifyLease, VerifyLock};

use std::path::Path;

use crate::hol::isabelle_pure::IsaProvenTheorem;

/// Opaque single-line verify-time state (kernel [`Environment`], serial-keyed
/// [`Closure`], the five PASS-1 registries, and the elision flag) — the
/// substrate behind `clean mathverse isabelle-verify-one`. Built either
/// minimally from the corpus ([`Self::minimal`]) or restored from a completed
/// replay snapshot ([`Self::from_snapshot`]).
pub struct SingleLineState {
    inner: streaming::VerifyState,
}

impl SingleLineState {
    /// Minimal state: prelude + built-in def-consts + the five PASS-1 registries
    /// scanned from `corpus`. Matches a fresh full replay's setup (no snapshot),
    /// so a line with an all-accepted-in-corpus dependency set reproduces the
    /// full replay's verdict. Scans the corpus for the registries (bounded by
    /// corpus size — use a snapshot to skip it).
    ///
    /// # Errors
    /// [`StreamError`] on I/O failure building the registries.
    pub fn minimal(corpus: &Path) -> Result<Self, StreamError> {
        Ok(Self {
            inner: streaming::build_verify_state(corpus)?,
        })
    }

    /// Restore the complete accepted state from a loaded replay snapshot
    /// (env + closure + the five registries). The proof-value elision flag
    /// follows the current process env ([`elide_proofs_enabled`]).
    #[must_use]
    pub fn from_snapshot(snap: snapshot::ReplaySnapshot) -> Self {
        Self {
            inner: streaming::VerifyState {
                env: snap.env,
                closure: snap.closure,
                class_registry: snap.class_registry,
                method_registry: snap.method_registry,
                instance_op_registry: snap.instance_op_registry,
                list_fn_registry: snap.list_fn_registry,
                poly_inst_registry: snap.poly_inst_registry,
                elide: elide_proofs_enabled(),
            },
        }
    }

    /// Whether serial `s` is an accepted (`KernelVerified`, closure-resident)
    /// entry — the basis of the missing-dependency diagnostic. A rejected /
    /// absent dependency is NOT in the closure, so `verify_one` cannot resolve
    /// its `PThm` reference.
    #[must_use]
    pub fn closure_has(&self, s: i64) -> bool {
        self.inner.closure.contains_key(&s)
    }
}

/// Verify EXACTLY ONE parsed theorem against `state`, returning its single-line
/// outcome (`kernel_verified == 1` on accept, else `rejected == 1` with a
/// recorded reason). The kernel `add_decl` verdict is the sole mint, identical
/// to the full-replay path — this is the diagnostic entry point that runs the
/// real `verify_one` on one line instead of a whole corpus. Any env mutation is
/// local to `state` (a fresh in-process value), never shared.
#[must_use]
pub fn verify_single_line(
    thm: &IsaProvenTheorem,
    state: &mut SingleLineState,
    writer: &mut ShardWriter,
) -> PureVerifiedImport {
    let mut out = PureVerifiedImport::default();
    let vs = &mut state.inner;
    batch::verify_one(
        thm,
        0,
        &mut vs.env,
        &mut vs.closure,
        &vs.class_registry,
        &vs.method_registry,
        &vs.instance_op_registry,
        &vs.list_fn_registry,
        &vs.poly_inst_registry,
        writer,
        &mut out,
        vs.elide,
    );
    out
}

/// Outcome of a closure-replay import batch.
#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct PureVerifiedImport {
    /// Theorems the kernel accepted with a foundational-only axiom closure —
    /// written to the shard as `KernelVerified`.
    pub kernel_verified: usize,
    /// Theorems dropped (unmapped axiom, hole, unresolved dep, or kernel
    /// rejection). Never written as verified.
    pub rejected: usize,
    /// Names of the kernel-verified theorems written.
    pub names: Vec<String>,
    /// Per-reason rejection tally (the `TranslateError` discriminant or
    /// `"kernel-reject"` / `"non-foundational-axiom"`), for honest reporting of
    /// what is not yet covered.
    pub rejection_reasons: BTreeMap<String, usize>,
    /// **Opt-in** fine-grained rejection tally keyed by a *normalized full
    /// message prefix* of the underlying [`TranslateError`] — the specific
    /// unsupported-shape string, the specific unmapped-axiom name, or the
    /// `unresolved-dep` serial pattern (serial digits normalized to `<serial>`
    /// so distinct serials collapse to one bucket). Populated **only** when the
    /// `ISA_REJECT_SPECIFICS` environment variable is set; empty otherwise, so
    /// the default path keeps the exact historical behaviour and cost. This is
    /// the concrete "what to support next" list when ranked by count.
    pub rejection_specifics: BTreeMap<String, usize>,

    // --- Two-tier trusted-ledger counters (env-gated `ISA_TRUSTED_LEDGER=1`,
    // default OFF; see [`ledger_enabled`]). All three are `0`/empty on a
    // non-ledger run, so a run that never turns the flag on is byte-identical.
    /// **Tier-2** count: lines whose recorded proof the kernel re-checked
    /// (`value : type` accepted) but whose transitive axiom closure includes at
    /// least one trusted-ledger axiom. Stamped [`ImportConfidence::KernelCheckedConditional`],
    /// **never** `KernelVerified`. Disjoint from [`Self::kernel_verified`].
    #[serde(default)]
    pub kernel_checked_ledger: usize,
    /// **Tier-LEDGER** count: statement-only trusted-ledger axioms registered
    /// (`isabelle.trusted.s<serial>`) for lines that failed every
    /// reconstruction/reprove arm but whose statement embedded cleanly. A
    /// ledger axiom is a RESTATEMENT (CLAUDE.md: `Theorem` wrapping `Axiom` is
    /// NOT a proof) — it is counted here and NOWHERE in any proved/verified
    /// metric. Equals `self.ledger.len()`.
    #[serde(default)]
    pub ledger_size: usize,
    /// **Tier-BRIDGE** count: lines discharged by the opt-in cross-lane kernel
    /// bridge (`ISA_BRIDGE_DISCHARGE=<manifest>`). Each is a line phase 1 could
    /// NOT verify whose embedded statement bridges — via a foundational
    /// connective iso — to a named Mathlib-KV witness constant, so a real
    /// `Iff.mpr bridge witness : stmt` proof was `add_decl`-accepted with a
    /// foundational closure. Stamped [`ImportConfidence::KernelBridged`], **never**
    /// `KernelVerified` (the statement arrived via the bridge, not a re-checked
    /// native value). `0` when the manifest env var is unset ⇒ byte-identical.
    #[serde(default)]
    pub kernel_bridged: usize,
    /// The trusted-ledger records (one per registered ledger axiom), for the
    /// per-run report file. Serial-ascending write order is enforced by the
    /// report writer, not here.
    #[serde(default)]
    pub ledger: Vec<LedgerEntry>,
    /// Every constant written to the shard on a **ledger run**, in shard-write
    /// order, with its shard index / confidence / provenance note — so the
    /// publish step can stamp KernelVerified, tier-2, AND ledger constants at
    /// their correct indices. Empty on a non-ledger run (the publish step then
    /// uses the historical [`Self::names`] loop unchanged).
    #[serde(default)]
    pub written_constants: Vec<WrittenConstant>,
    /// **Ledger-side closure** — the by-serial closure of the trusted-ledger
    /// axioms and tier-2 (`KernelCheckedConditional`) theorems, kept STRICTLY
    /// SEPARATE from the main `KernelVerified` closure. This separation is the
    /// entire soundness mechanism of the two-tier lane:
    ///
    /// - **Phase 1** (tier-1 classification) resolves `PThm` references against
    ///   the KV closure ONLY — never this one — so it is byte-for-byte identical
    ///   to a no-ledger run. A line is `KernelVerified` iff phase 1 accepts it
    ///   foundationally, exactly as today ⇒ `KernelVerified` is invariant ON/OFF.
    /// - **Phase 2** (only for lines phase 1 could NOT verify) re-resolves
    ///   against the KV closure UNIONED with this ledger closure. Any kernel
    ///   accept there is tier-2 (its verification required the ledger), never
    ///   KV. Ledgered primaries and tier-2 theorems land here so their
    ///   dependents cascade — a dependent references a serial that lives only in
    ///   this closure, so phase 1 fails for it and phase 2 makes it tier-2 too.
    ///
    /// Empty on a non-ledger run (phase 2 is never entered). Rides the snapshot
    /// inside `out` so a resumed two-tier run continues its cascade.
    #[serde(default)]
    pub ledger_closure: Closure,
    /// The serials minted [`ImportConfidence::KernelBridged`] — every cross-lane
    /// bridge discharge (a direct `try_bridge_discharge`) **and** every inherited
    /// bridged dependent (a phase-2 line that kernel-re-checked its own native
    /// proof against a bridged serial with a still-foundational closure). This set
    /// is the **provenance frontier**: a phase-2-accepted line whose dependency set
    /// intersects it is classified `KernelBridged` (inherited), never
    /// `KernelVerified` — the bridged provenance propagates transitively even
    /// though the trust (foundational-only closure) is KV-grade. Bridged serials
    /// live only in [`Self::ledger_closure`] (never the KV closure), so a bridged
    /// line's dependents fail phase 1 and route through phase 2 where this
    /// classification runs — keeping `KernelVerified` byte-identical ON vs OFF.
    /// Empty unless the bridge lane (`ISA_BRIDGE_DISCHARGE`) is active.
    #[serde(default)]
    pub bridged_serials: BTreeSet<i64>,
}

/// One registered trusted-ledger axiom: an Isabelle line that failed every
/// reconstruction/reprove arm but whose STATEMENT embedded cleanly, so the
/// embedded statement TYPE was registered as a kernel `Axiom`
/// (`isabelle.trusted.s<serial>`) to unblock its downstream cascade. This is a
/// restatement, never a proof.
#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct LedgerEntry {
    /// The Isabelle proof-term serial of the ledgered line.
    pub serial: i64,
    /// The Isabelle theorem name (may be empty for anonymous nodes).
    pub isabelle_name: String,
    /// Best-effort theory name (the leading dotted segment of the name).
    pub theory: String,
    /// The honest reject bucket the line WOULD have carried without the ledger
    /// (`unmapped-axiom`, `unresolved-dep`, `kernel-reject`, …).
    pub reject_reason: String,
    /// The kernel axiom name registered (`isabelle.trusted.s<serial>`).
    pub axiom_name: String,
}

/// One constant written to the shard during a ledger run, recorded so the
/// publish step can attach per-constant provenance at the right shard index.
#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct WrittenConstant {
    /// The catalog (shard string-table) name of the constant.
    pub name: String,
    /// Its index in the shard's constant table.
    pub shard_idx: u32,
    /// [`ImportConfidence`] byte (`KernelVerified` / `KernelCheckedConditional`
    /// / `Axiomatized`).
    pub confidence: u8,
    /// A provenance note (for tier-2 / ledger constants, names the ledger
    /// dependence); `None` for a plain KernelVerified constant.
    pub ledger_note: Option<String>,
}

/// The kernel-name prefix every trusted-ledger axiom carries. A dependent's
/// non-foundational axiom closure is classified tier-2 exactly when it contains
/// a name with this prefix.
pub(crate) const LEDGER_AXIOM_PREFIX: &str = "isabelle.trusted.";

/// Whether the **two-tier trusted-ledger** lane is enabled, gated behind the
/// `ISA_TRUSTED_LEDGER` environment variable (default OFF — byte-identical to
/// the historical single-tier importer). When ON, a line that fails every
/// reconstruction/reprove arm but whose statement embeds cleanly is registered
/// as a trusted-ledger kernel `Axiom` (tier-LEDGER) so its downstream cascade
/// can kernel-check; any dependent whose closure then touches a ledger axiom is
/// classified tier-2 ([`ImportConfidence::KernelCheckedConditional`]) rather
/// than rejected — never `KernelVerified`.
#[must_use]
pub fn ledger_enabled() -> bool {
    std::env::var_os("ISA_TRUSTED_LEDGER").is_some()
}

impl PureVerifiedImport {
    fn reject(&mut self, reason: &str) {
        self.rejected += 1;
        *self
            .rejection_reasons
            .entry(reason.to_string())
            .or_insert(0) += 1;
    }

    /// Reject and ALSO, when the opt-in `ISA_REJECT_SPECIFICS` env flag is set,
    /// tally the normalized full-message prefix of the originating
    /// [`TranslateError`] in [`Self::rejection_specifics`]. `discriminant` is the
    /// coarse bucket recorded in [`Self::rejection_reasons`] (kept bit-identical
    /// to the historical [`Self::reject`] path); `specific` is the fine-grained
    /// payload-bearing key.
    fn reject_with_specific(&mut self, discriminant: &str, err: &TranslateError) {
        self.reject(discriminant);
        if specifics_enabled() {
            let key = normalize_specific(err);
            *self.rejection_specifics.entry(key).or_insert(0) += 1;
        }
    }
}

/// Whether the opt-in fine-grained rejection-specifics tally is enabled. Reads
/// the **installed [`VerifyConfig`](crate::hol::isabelle_verify_config::VerifyConfig)**
/// for the current run when one is installed (the entry points and the
/// single-line probe install it), else the historical `ISA_REJECT_SPECIFICS`
/// env check — byte-identical for an un-instrumented caller. Only ever reached on
/// the (rejection) cold path.
fn specifics_enabled() -> bool {
    crate::hol::isabelle_verify_config::active_reject_specifics_enabled()
}

/// Whether **opaque proof-value elision** is enabled, gated behind the
/// `ISA_ELIDE_PROOFS` environment variable (default OFF — the exact historical
/// full-resident behaviour).
///
/// When set, each theorem's resident proof VALUE is dropped from the accumulating
/// kernel [`Environment`](clean_kernel::Environment) immediately AFTER it has been
/// stamped [`ImportConfidence::KernelVerified`] (kernel-accepted + foundational
/// closure). Only its TYPE is kept — enough for later `PThm`/`ZConstp(ZThm)`
/// references, which resolve the theorem BY NAME and never δ-unfold it. This
/// bounds peak memory so the full zproof corpus replays without OOM, while every
/// verdict is unchanged (the `KernelVerified` set is identical with elision on or
/// off; see [`super::batch::verify_one`]'s SOUNDNESS note and the scale-run gate).
///
/// Read once per driver invocation (not per theorem), so the hot loop pays no
/// repeated env lookup.
#[must_use]
pub fn elide_proofs_enabled() -> bool {
    std::env::var_os("ISA_ELIDE_PROOFS").is_some()
}

/// Normalize a [`TranslateError`] into a stable, frequency-rankable key that
/// preserves the *specific* payload but collapses high-cardinality numeric
/// fields so distinct instances of the same shape land in one bucket:
///
/// - `unsupported-shape: <static str>` — the exact (bounded) shape string.
/// - `unmapped-axiom: <axiom name>` — the exact base-axiom name.
/// - `hole: <static str>` — the exact (bounded) hole reason.
/// - `unresolved-dep: serial <serial>` — the serial digits are normalized to the
///   literal `<serial>` so all unresolved-dep misses collapse to one pattern
///   (the serial is per-theorem noise, not a distinguishing shape).
fn normalize_specific(err: &TranslateError) -> String {
    match err {
        TranslateError::Hole(s) => format!("hole: {s}"),
        TranslateError::UnmappedAxiom(name) => format!("unmapped-axiom: {name}"),
        TranslateError::UnresolvedThm(_) => "unresolved-dep: serial <serial>".to_string(),
        TranslateError::Unsupported(s) => format!("unsupported-shape: {s}"),
        TranslateError::BudgetExceeded(_) => "translate-budget: node budget exceeded".to_string(),
        TranslateError::PremiseBudgetExceeded(_) => {
            "premise-budget-cut: search step budget exceeded".to_string()
        }
    }
}

fn translate_error_tag(e: &TranslateError) -> &'static str {
    match e {
        TranslateError::Hole(_) => "hole",
        TranslateError::UnmappedAxiom(_) => "unmapped-axiom",
        TranslateError::UnresolvedThm(_) => "unresolved-dep",
        TranslateError::Unsupported(_) => "unsupported-shape",
        TranslateError::BudgetExceeded(_) => "translate-budget",
        TranslateError::PremiseBudgetExceeded(_) => "premise-budget-cut",
    }
}

/// Error opening or reading the serial-sorted closure file in the streaming
/// driver. (Per-theorem translate/kernel rejections are *not* errors — they are
/// tallied in [`PureVerifiedImport::rejection_reasons`]; only I/O failures abort
/// the run.)
#[derive(Debug, thiserror::Error)]
pub enum StreamError {
    /// The serial-sorted closure file could not be opened or read.
    #[error("reading serial-sorted closure file: {0}")]
    Io(#[from] std::io::Error),
    /// Snapshot save/load/validate failure (resume runs).
    #[error("snapshot: {0}")]
    Snapshot(#[from] snapshot::SnapshotError),
    /// An incremental (`--corpus-diff`) retry was REFUSED because the corpus-diff
    /// shows the old corpus's accepted prefix is not byte-identical in the new
    /// corpus — trusting the snapshot's prefix state would trust a stale region.
    /// Run a full grand replay on the new corpus instead.
    #[error("incremental retry refused: {0}")]
    IncrementalRefused(String),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::shard::ShardReader;

    const AEQA: &str = r#"{"name":"Demo.a_eq_a","serial":100,"prop":{"k":"App","f":{"k":"Const","n":"HOL.Trueprop","t":{"k":"Type","n":"fun","a":[{"k":"Type","n":"HOL.bool","a":[]},{"k":"Type","n":"prop","a":[]}]}},"a":{"k":"App","f":{"k":"App","f":{"k":"Const","n":"HOL.eq","t":{"k":"Type","n":"fun","a":[{"k":"TFree","n":"'a"},{"k":"Type","n":"fun","a":[{"k":"TFree","n":"'a"},{"k":"Type","n":"HOL.bool","a":[]}]}]}},"a":{"k":"Free","n":"a","t":{"k":"TFree","n":"'a"}}},"a":{"k":"Free","n":"a","t":{"k":"TFree","n":"'a"}}}},"proof":{"k":"appt","f":{"k":"axm","name":"HOL.refl"},"a":{"k":"Free","n":"a","t":{"k":"TFree","n":"'a"}}}}"#;

    // A second equational theorem (different free var) — exercises the batch
    // writer and topological pass with independent theorems.
    const BEQB: &str = r#"{"name":"Demo.b_eq_b","serial":101,"prop":{"k":"App","f":{"k":"Const","n":"HOL.Trueprop","t":{"k":"Type","n":"fun","a":[{"k":"Type","n":"HOL.bool","a":[]},{"k":"Type","n":"prop","a":[]}]}},"a":{"k":"App","f":{"k":"App","f":{"k":"Const","n":"HOL.eq","t":{"k":"Type","n":"fun","a":[{"k":"TFree","n":"'b"},{"k":"Type","n":"fun","a":[{"k":"TFree","n":"'b"},{"k":"Type","n":"HOL.bool","a":[]}]}]}},"a":{"k":"Free","n":"b","t":{"k":"TFree","n":"'b"}}},"a":{"k":"Free","n":"b","t":{"k":"TFree","n":"'b"}}}},"proof":{"k":"appt","f":{"k":"axm","name":"HOL.refl"},"a":{"k":"Free","n":"b","t":{"k":"TFree","n":"'b"}}}}"#;

    // Unverifiable: an oracle hole — must be rejected, never KernelVerified.
    const HOLE: &str = r#"{"name":"Demo.bad","serial":102,"prop":{"k":"App","f":{"k":"Const","n":"HOL.Trueprop","t":{"k":"Type","n":"fun","a":[]}},"a":{"k":"Free","n":"p","t":{"k":"Type","n":"HOL.bool","a":[]}}},"proof":{"k":"min"}}"#;

    #[test]
    fn imports_proven_theorems_as_kernel_verified() {
        let aeqa = crate::hol::isabelle_pure::parse_proven_theorem(AEQA).unwrap();
        let beqb = crate::hol::isabelle_pure::parse_proven_theorem(BEQB).unwrap();
        let hole = crate::hol::isabelle_pure::parse_proven_theorem(HOLE).unwrap();

        let mut writer = ShardWriter::new();
        let result = import_proven_theorems(&[aeqa, beqb, hole], &mut writer);

        assert_eq!(result.kernel_verified, 2, "both refl theorems verify");
        assert_eq!(result.rejected, 1, "the oracle hole is rejected");
        assert_eq!(result.rejection_reasons.get("hole"), Some(&1));

        // Persist + round-trip: the stamps are genuinely KernelVerified.
        let mut buf = Vec::new();
        writer.write(&mut buf).expect("shard write");
        let reader = ShardReader::from_bytes(&buf).expect("shard read");
        assert_eq!(reader.header.constant_count, 2);
        for name in &result.names {
            let (_, hdr) = reader.lookup_name(name).expect("verified name present");
            assert_eq!(
                hdr.import_confidence,
                ImportConfidence::KernelVerified as u8
            );
            assert_ne!(hdr.value_idx, u32::MAX, "proof value stored, not NO_VALUE");
        }
    }

    /// REAL Isabelle export: `Int.power_int_def`, a **polymorphic instance-operation**
    /// definition `power_int ?x ?n ≡ if 0 ≤ ?n then ?x ^ nat ?n else inverse ?x ^ nat (- ?n)`
    /// whose body uses the overloaded class operations `power`/`inverse`/`uminus`/`zero`/
    /// `less_eq` over `'a` (gated behind the `OFCLASS('a, inverse_class)`/`OFCLASS('a,
    /// power_class)` premises). Verifies ONLY through the polymorphic-instance-op handler
    /// (`register_poly_inst_def` + the reflexive `@Eq` arm): the `'a`-generic constant is
    /// registered as a clean `Definition` abstracting `α`, the class operations, and the
    /// `int` arg-type, so the `_def` axiom is genuinely reflexive — kernel-accepted iff the
    /// LHS δ-unfolds to the body, with a foundational-only closure (the `if` uses the
    /// classical `HOL.If` def-const).
    const POWER_INT_DEF: &str = include_str!("../../../tests/fixtures/isabelle/power_int_def.json");

    #[test]
    fn kernel_verifies_polymorphic_instance_op_power_int_def() {
        let thm = crate::hol::isabelle_pure::parse_proven_theorem(POWER_INT_DEF.trim())
            .expect("parse power_int_def export");
        let mut writer = ShardWriter::new();
        let result = import_proven_theorems(&[thm], &mut writer);
        assert_eq!(
            result.kernel_verified, 1,
            "power_int_def must KernelVerify via the polymorphic-instance-op handler; \
             rejected={} reasons={:?}",
            result.rejected, result.rejection_reasons
        );
    }

    #[test]
    fn streaming_matches_batch_on_serial_sorted_corpus() {
        use std::io::Write as _;

        // A small serial-ascending corpus (the streaming driver's precondition).
        // The same three fixtures as the batch test: two verifiable refl theorems
        // and one oracle hole.
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("corpus.serial_sorted.txt");
        let mut f = std::fs::File::create(&path).expect("create corpus");
        for line in [AEQA, BEQB, HOLE] {
            writeln!(f, "{line}").expect("write line");
        }
        f.flush().expect("flush");
        drop(f);

        let mut writer = ShardWriter::new();
        let result =
            import_proven_theorems_streaming(&path, &mut writer).expect("streaming verify I/O");

        // Identical outcome to the batch driver: closure replay is
        // order-independent given deps-before-uses.
        assert_eq!(result.kernel_verified, 2, "both refl theorems verify");
        assert_eq!(result.rejected, 1, "the oracle hole is rejected");
        assert_eq!(result.rejection_reasons.get("hole"), Some(&1));
        assert_eq!(result.kernel_verified, result.names.len());

        // The shard round-trips with both theorems stamped KernelVerified.
        let mut buf = Vec::new();
        writer.write(&mut buf).expect("shard write");
        let reader = ShardReader::from_bytes(&buf).expect("shard read");
        assert_eq!(reader.header.constant_count, 2);
        for name in &result.names {
            let (_, hdr) = reader.lookup_name(name).expect("verified name present");
            assert_eq!(
                hdr.import_confidence,
                ImportConfidence::KernelVerified as u8
            );
        }
    }
}
