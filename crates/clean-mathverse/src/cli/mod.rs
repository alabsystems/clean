// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean mathverse <verb>` — unified CLI surface for the Mathverse Library.
//!
//! Exposes clap argument structs, the descriptor array used by
//! `clean features`/`clean help`, and the dispatch entry point [`run`].
//! Phase 1 (#3440) absorbed `search`/`info`/`stats`/`systems` as typed
//! clap derive args; Phase 3.5 (#3512) absorbed the browse verbs
//! (`list`/`sample`/`deps`/`version`) the same way, then re-absorbed the
//! remaining 7 verbs (`find`/`graph`/`diff`/`verify`/`download`/`export`/
//! `release`) via `PassthroughArgs` delegation after a regression between
//! `ae3772027` (original passthrough absorption) and `f43429751` (partial
//! re-type) dropped them. All verbs call the library-hosted functions in
//! [`crate::mathverse_bin_cmds::commands`] so `clean mathverse <verb>` and the
//! standalone `mathverse` binary stay byte-for-byte identical by construction.

mod browse_common;
mod browse_dispatch;
mod build_library_dispatch;
mod closure_load;
mod closure_shards_dispatch;
mod descriptors;
mod descriptors_browse;
mod descriptors_passthrough;
mod dispatch;
mod format;
mod graduate_closure_cache;
mod graduate_dispatch;
mod import_cache;
mod isabelle_capture_chain_dispatch;
mod isabelle_doctor_dispatch;
mod isabelle_flip_gate_dispatch;
mod isabelle_import_dispatch;
mod isabelle_sessions_dispatch;
mod isabelle_snapshot_preserve_dispatch;
mod kv_cache;
mod kv_guardrail_dispatch;
mod operator_tools;
mod parallel_verify;
mod passthrough_dispatch;
mod per_constant_load;
/// RAM-aware default worker count, shared by the PARAGON `--parallel` verifier
/// and the `mathverse_shard --corpus-sharded` driver binary (single source of
/// truth for the `min(cpus, max(1, ram_gib / PER_WORKER_GIB))` clamp).
pub mod ram_budget;
mod replay_dispatch;
mod stamp_verified_dispatch;
mod trust_receipt_cmd;

use std::path::PathBuf;

use clap::{Args, Subcommand, ValueEnum};

pub use crate::hol::isabelle_doctor::BuildIdentity;
pub use descriptors::FEATURES;
pub use descriptors_browse::BROWSE_FEATURES;
pub use descriptors_passthrough::PASSTHROUGH_FEATURES;
pub use graduate_dispatch::{
    EvidenceClassArg, GraduateArgs, GraduateEnvKind, GraduationRecordArgs, IndexBuildArgs,
    IndexTreeScoreArgs, OnDuplicateArg,
};
pub use isabelle_doctor_dispatch::run_isabelle_doctor;
pub use isabelle_snapshot_preserve_dispatch::run_isabelle_snapshot_preserve;
pub use operator_tools::OPERATOR_TOOLS_FEATURES;

/// `clean mathverse <subcommand>` argument tree.
#[derive(Debug, Args)]
pub struct MathverseArgs {
    #[command(subcommand)]
    pub command: MathverseCommands,
}

/// Every verb under `clean mathverse`.
///
/// Marked `#[non_exhaustive]` so future verbs can be added without breaking
/// downstream tooling.
#[derive(Debug, Subcommand)]
#[non_exhaustive]
pub enum MathverseCommands {
    /// Search declarations by name, type (discrimination tree),
    /// structural-equivalence (rewrite-canonical digest), or BM25 semantic match.
    Search(SearchArgs),
    /// Show full details of a single declaration by exact name.
    Info(InfoArgs),
    /// Print library-wide statistics (counts by system, confidence, domain).
    Stats(StatsArgs),
    /// List every source system represented in the loaded shards with counts.
    Systems(SystemsArgs),
    /// Enumerate declarations with system/limit/offset filtering.
    List(ListArgs),
    /// Draw a deterministic sample of declarations matching optional filters.
    Sample(SampleArgs),
    /// Print direct (or transitive) dependencies of a named declaration.
    Deps(DepsArgs),
    /// Reverse dependencies: the declarations that USE a named declaration
    /// (its users / blast radius), ranked by impact. Alias for `deps --reverse`.
    Uses(DepsArgs),
    /// Show the Mathverse Library release version and live summary stats.
    Version(VersionArgs),
    /// Unified search: name/tags/similarity/cross-system/domain/BM25.
    Find(PassthroughArgs),
    /// Cross-system knowledge graph: `graph search|overlap|stats`.
    Graph(PassthroughArgs),
    /// Symmetric diff of two `.mathverse` shards by declaration name.
    Diff(PassthroughArgs),
    /// Verify a shard directory or release manifest.
    Verify(PassthroughArgs),
    /// Download a corpus from a GitHub release (default) or a running server
    /// (`--from <url>`), landing it to `--out <dir>` and blake3-verifying it.
    Download(PassthroughArgs),
    /// Publish a local corpus to a destination: `upload <dir> --to
    /// release:<tag>|gcs:<bucket/path>|server:<url> --version <V>`.
    Upload(PassthroughArgs),
    /// Turnkey distribution server over a local Core: `serve [--core <dir>]
    /// [--port <N>] [--download-base <url>]`.
    Serve(PassthroughArgs),
    /// Export library data: `export clean-native|arxiv|all`.
    Export(PassthroughArgs),
    /// Release management: `release build|package|verify|download|info`.
    Release(PassthroughArgs),
    /// Graduate kernel-verified project theorems (with carried definition
    /// dependencies) into a Cake-tagged shard with a digest-bound
    /// `mathverse-graduation-v2` record.
    Graduate(GraduateArgs),
    /// Build a persistent novelty-baseline index (`MVBIDX01`) over a
    /// release's `.mathverse` shards so `graduate --baseline-index` can pin
    /// the full corpus in seconds instead of hours.
    IndexBuild(IndexBuildArgs),
    /// Kernel-confirmed tree-score / uniqueness probe over KERNEL-VERIFIED
    /// shards: bucket KernelVerified decls by the kernel-confirmed defeq
    /// tree-signature, then CONFIRM every "same object, different form"
    /// candidate with the kernel `is_def_eq` arbiter.
    IndexTreeScore(IndexTreeScoreArgs),
    /// Project a full `mathverse-graduation-v3.x` `.graduation.json` + its
    /// `.mathverse` shard into the COMPACT `mathverse-graduation-record-v1`
    /// git artifact (statement / axiom-closure / novelty + gate verdict +
    /// carried COUNTS + provenance + the shard blake3 pin). Pure projection —
    /// no kernel, gate, or proof is touched.
    GraduationRecord(GraduationRecordArgs),
    /// Generate deterministic fail-closed Mathverse replay production corpus evidence.
    ReplayCorpus(ReplayCorpusArgs),
    /// Validate the Mathverse replay replacement report and corpus artifact.
    ValidateReplayReport(ValidateReplayReportArgs),
    /// Convert `.olean` input(s) to `.mathverse` shards, re-verify the corpus
    /// in Clean's kernel, and stamp every genuinely kernel-verified constant
    /// into the shard bytes on disk (`KernelVerified`). Prints a JSON summary.
    StampVerified(StampVerifiedArgs),
    /// Assemble raw Isabelle zproof exports (the capture hook's per-theory
    /// `.jsonl` files) into ONE serial-sorted deduplicated corpus, then replay
    /// it through the kernel with snapshot resume/save — the standing
    /// re-import pipeline (P3).
    IsabelleImport(IsabelleImportArgs),
    /// Extract a closure-complete, serial-sorted SLICE of an Isabelle corpus
    /// (seeds by serial / name substring / reject-dump rows + their transitive
    /// proof dependencies) — the fast-iteration input for engine rounds.
    IsabelleSlice(IsabelleSliceArgs),
    /// Rank every REJECTED corpus line by the cascade it transitively gates:
    /// the blocking-weight targeting table (blocked / exclusive per frontier
    /// primary) so rounds attack the top gatekeepers, not families.
    IsabelleTargets(IsabelleTargetsArgs),
    /// Build the `<corpus>.idx` sidecar (serial-sorted offset/len table + name +
    /// registration flag + byte-scan dep edges) in one streaming pass, so
    /// `isabelle-slice` / `isabelle-verify-one` / `isabelle-targets` seek
    /// straight to the lines they need instead of scanning the (52 GB) corpus.
    IsabelleIndex(IsabelleIndexArgs),
    /// Diff two corpus versions off their `.idx` sidecars (no full-corpus read):
    /// classify every line UNCHANGED / NEW / CHANGED / REMOVED and emit a typed
    /// JSON report. The substrate of the **incremental grand** — feed the report
    /// to `isabelle-import --retry-from … --corpus-diff` to re-verify only the
    /// added/changed lines against the old version's standing snapshot instead of
    /// a fresh multi-hour grand.
    IsabelleCorpusDiff(IsabelleCorpusDiffArgs),
    /// Verify EXACTLY ONE corpus line with full diagnostics (per-mode /
    /// expected-vs-got traces, rejection specifics, and the crisp missing-
    /// dependency list) against a restored replay snapshot — the seconds-scale
    /// tweak-and-check loop the engine rounds lacked.
    IsabelleVerifyOne(IsabelleVerifyOneArgs),
    /// Translate an Isabelle theorem STATEMENT to a Lean 4 goal (Path-B
    /// translation harness). `--serial`/`--name` prints one faithful Lean
    /// statement (or an honest `UNSUPPORTED` verdict) read via the `.idx`
    /// sidecar; `--candidates <file> --out-dir <d>` batch-preps per-theorem Lean
    /// submission stubs + a manifest, marking the unsupported tail for
    /// human/agent curation. Never emits a plausible-but-unfaithful statement.
    IsabelleLeanGoal(IsabelleLeanGoalArgs),
    /// Emit checkpointed Isabelle session-ROOT fragments for the AFP capture
    /// waves: `--mode afp` per-entry fragments (Wave A/C), `--mode spine` the
    /// six HOL-* Wave-B spine heaps, `--mode wavec` the AFP-on-AFP topo DAG.
    /// Byte-parity port of the retired `scripts/isabelle/afp_session_gen.py`.
    IsabelleSessions(IsabelleSessionsArgs),
    /// Self-healing capture-chain driver: build a chained sequence of
    /// `record_proofs` capture sessions from a typed JSON spec, shelling out to
    /// `isabelle build -b` per segment, and auto-recover from the Poly/ML
    /// arm64_32 "Run out of store" OOM via the response ladder (retry at
    /// threads=1 → bisect the theory list → proofless heap-bake). Durable state
    /// makes `--resume` pick up exactly where a crash/halt left off; `--dry`
    /// prints the plan and generated ROOTs.
    IsabelleCaptureChain(IsabelleCaptureChainArgs),
    /// Standing FLIP-GATE CI: `--check` replays each registered closure slice
    /// through the real library stream-verify driver and asserts its pinned
    /// serial lands `KernelVerified` (PASS/FAIL per gate, nonzero on any FAIL) —
    /// the corpus-routing proof that a claimed flip actually happens, in minutes
    /// before any grand. `--add --corpus <c> --serial <s>` builds the minimal
    /// closure slice, confirms it flips under the current binary, pins its
    /// blake3 + line count, and appends the registry entry.
    IsabelleFlipGate(IsabelleFlipGateArgs),
    /// Ops preflight / health doctor: check the running binary's build identity,
    /// concurrent-verify locks/processes, dead `.claude/worktrees` script refs,
    /// corpus↔`.idx` coherence, snapshot ENV-LAYOUT drift, `/tmp` durability, and
    /// disk headroom — so a re-import fails LOUD before burning hours. Exits
    /// nonzero on any FAIL; `--json` emits a machine-readable report.
    IsabelleDoctor(IsabelleDoctorArgs),
    /// Preserve the CURRENT binary into a durable binaries dir named by its git
    /// SHA, so a replay snapshot stays resumable (a snapshot only loads under a
    /// binary whose ENV-LAYOUT matches its builder). One command instead of the
    /// manual `cp` dance; reports the snapshot↔binary pairing from the sidecar.
    IsabelleSnapshotPreserve(IsabelleSnapshotPreserveArgs),
    /// PER-CONSTANT streaming closure loader: kernel-verify ONE target constant
    /// by demand-loading only its transitive CONSTANT closure (not the whole
    /// module-import closure). Orders of magnitude less Expr reconstruction than
    /// `stamp-verified --closure-root` for a single leaf lemma.
    PerConstantVerify(PerConstantVerifyArgs),
    /// Build the v3 fail-closed `.mathverse` closure-shard cache for a target
    /// module (or directory of modules) so a later `stamp-verified
    /// --closure-root` re-import serves the closure LAZILY from mmap'd shards
    /// instead of eagerly reconstructing the whole `.olean` import closure.
    BuildClosureShards(BuildClosureShardsArgs),
    /// Build a Mathverse Library archive: install prereqs, clone the configured
    /// upstream proof system sources (incl. Lean 3 mathlib3), run the converter
    /// pipeline, package into `mathverse-library-v*.tar.zst`, and optionally
    /// publish as a GitHub Release.
    BuildLibrary(BuildLibraryArgs),
    /// Axiom-audit invariant gates — release-check, recompute-aggregates, etc.
    ///
    /// Nested aggregator so sibling verbs can drop in without re-shaping the
    /// top-level `clean mathverse` clap tree. Bucket-B script migrations
    /// (`docs/SCRIPTS_MIGRATION.md`) target this subtree: `release-check`
    /// landed in Wave 87, `recompute` is queued next.
    AxiomAudit {
        #[command(subcommand)]
        command: AxiomAuditCommands,
    },
    /// Monotonic-UP ratchet over `stamp-verified` KernelVerified counts:
    /// `ratchet check|update`.
    ///
    /// Pure guardrail over a saved `stamp-verified --json` summary — re-asserts
    /// the `heuristic_kernel_verified == 0` soundness floor and fails closed if
    /// a stamp run's KernelVerified count regressed below the ratcheted
    /// baseline. Nested aggregator (mirrors `AxiomAudit`) so `check` and
    /// `update` read as siblings. Subsumes the retired
    /// `scripts/check_kv_ratchet.py`.
    Ratchet {
        #[command(subcommand)]
        command: RatchetCommands,
    },
    /// Elision soundness gate: KV(opaque) must be a subset of
    /// KV(opaque-and-theorem).
    ///
    /// `opaque-and-theorem` proof-value elision is NOT statically sound for this
    /// kernel (theorems CAN be δ-unfolded), so its only safe contract is that it
    /// may ADD KernelVerified constants relative to the statically-sound
    /// `opaque` floor — never DROP one. Fails (naming the offenders) if any
    /// constant the `opaque` run kernel-verified is missing from the
    /// `opaque-and-theorem` run. Subsumes the retired
    /// `scripts/check_kv_elision_subset.py`.
    ElisionGate(ElisionGateArgs),
    /// Print the recorded reproducibility `StampEnvFingerprint` from a
    /// kernel-verified manifest.
    ///
    /// Pure read of the `env_fingerprint` metadata a `stamp-verified --manifest`
    /// run recorded (kernel/toolchain/heartbeat/elision-policy/closure ceiling/
    /// prelude variant); fails closed if the manifest carries none (a legacy
    /// manifest written before the field existed).
    Fingerprint(FingerprintArgs),
    /// Build, audit, or prove membership in a Merkle **trust receipt** (P4) over
    /// a kernel-verified declaration set — a single root hash certifying "these N
    /// named decls type-check", independently re-derivable from the published
    /// leaves. Mint one with `per-constant-verify --receipt`.
    #[command(subcommand)]
    TrustReceipt(TrustReceiptCommands),
}

/// Verbs under `clean mathverse trust-receipt <verb>`.
#[derive(Debug, clap::Subcommand)]
#[non_exhaustive]
pub enum TrustReceiptCommands {
    /// (Re)build a receipt from a published leaves manifest.
    Build(TrustReceiptBuildArgs),
    /// Independently re-derive the root from the leaves and confirm every claim
    /// (root, leaf count, axiom closure, TCB verdict). Fails closed on mismatch.
    Verify(TrustReceiptVerifyArgs),
    /// Emit + self-check an O(log N) membership proof for one named theorem.
    Prove(TrustReceiptProveArgs),
    /// Merge many per-module leaves manifests into ONE whole-corpus receipt: the
    /// union of all `(name, content_hash)` leaves under a single root, the union
    /// axiom closure, complete iff every input is complete. The composable path
    /// to `Mathlib@<sha> → root` — run `--all-declared` per module (in parallel),
    /// then merge.
    Merge(TrustReceiptMergeArgs),
    /// End-to-end library certification: kernel-verify EVERY value-bearing
    /// constant of EVERY module under a directory (`--all-declared` per module),
    /// then union into ONE corpus receipt with a provenance record. The turnkey
    /// `Mathlib@<sha> → root, N decls, axioms ⊆ TCB` artifact.
    Corpus(TrustReceiptCorpusArgs),
    /// Build a receipt directly from a stamped `.mathverse` shard directory (the
    /// Mathverse-native path): certify exactly the constants the shards stamped
    /// `KernelVerified`, reading their content + axiom closure straight from the
    /// shards — no re-verification, no `.olean` re-walk.
    FromShards(TrustReceiptFromShardsArgs),
}

/// Arguments for `clean mathverse trust-receipt from-shards`.
#[derive(Debug, Args)]
pub struct TrustReceiptFromShardsArgs {
    /// Directory of stamped `.mathverse` shards (e.g. a `stamp-verified --out-dir`).
    #[arg(long = "shard-dir")]
    pub shard_dir: PathBuf,
    /// Source identity to certify (e.g. `Mathlib@<git-sha>`).
    #[arg(long = "source-id")]
    pub source_id: Option<String>,
    /// Write the receipt JSON here.
    #[arg(long)]
    pub out: Option<PathBuf>,
    /// Write the auditable union leaves manifest here.
    #[arg(long = "out-leaves")]
    pub out_leaves: Option<PathBuf>,
    /// Write the provenance record (root, counts, within_tcb, source) here.
    #[arg(long = "out-provenance")]
    pub out_provenance: Option<PathBuf>,
}

/// Arguments for `clean mathverse trust-receipt corpus`.
#[derive(Debug, Args)]
pub struct TrustReceiptCorpusArgs {
    /// Directory of `.olean` modules to certify (scanned recursively). Each
    /// module's value-bearing declarations are kernel-verified.
    #[arg(long = "modules-dir")]
    pub modules_dir: PathBuf,
    /// `.olean` search root used to resolve every module's transitive closure
    /// (sibling packages + toolchain discovered automatically).
    #[arg(long = "closure-root")]
    pub closure_root: PathBuf,
    /// Source identity to certify (e.g. `Mathlib@<git-sha>`) — recorded in the
    /// receipt and the provenance record.
    #[arg(long = "source-id")]
    pub source_id: Option<String>,
    /// Per-check kernel step budget (`0` = unlimited). A resource limit only.
    #[arg(long, default_value_t = 0)]
    pub heartbeat: u32,
    /// Stop after this many modules (0 = all) — for a bounded run over a large
    /// tree.
    #[arg(long, default_value_t = 0)]
    pub limit: usize,
    /// Write the corpus receipt JSON here.
    #[arg(long)]
    pub out: Option<PathBuf>,
    /// Write the merged (union) leaves manifest here — needed to audit the corpus
    /// root and prove membership of any theorem in it.
    #[arg(long = "out-leaves")]
    pub out_leaves: Option<PathBuf>,
    /// Write the provenance record (per-module counts + totals + root) here.
    #[arg(long = "out-provenance")]
    pub out_provenance: Option<PathBuf>,
    /// RESUMABLE checkpoint file (JSONL, one line per module). Appended after each
    /// module verifies; on restart, modules already recorded are replayed from the
    /// checkpoint instead of re-verified — so a long full-Mathlib run survives
    /// interruption. Sound: the root is a Merkle over the canonical UNION of leaves,
    /// identical whether a module's leaves come from cache or fresh verification.
    #[arg(long)]
    pub checkpoint: Option<PathBuf>,
}

/// Arguments for `clean mathverse trust-receipt merge`.
#[derive(Debug, Args)]
pub struct TrustReceiptMergeArgs {
    /// Per-module leaves manifests to union (repeat `--leaves`). A directory is
    /// scanned recursively for `*.leaves.json` / `*_leaves.json`.
    #[arg(long, required = true)]
    pub leaves: Vec<PathBuf>,
    /// Source identity for the corpus receipt (e.g. `Mathlib@<sha>`).
    #[arg(long = "source-id")]
    pub source_id: Option<String>,
    /// Write the corpus receipt JSON here.
    #[arg(long)]
    pub out: Option<PathBuf>,
    /// Write the merged (union) leaves manifest here — needed to audit the corpus
    /// root and prove membership of any theorem in it.
    #[arg(long = "out-leaves")]
    pub out_leaves: Option<PathBuf>,
}

/// Arguments for `clean mathverse trust-receipt build`.
#[derive(Debug, Args)]
pub struct TrustReceiptBuildArgs {
    /// The leaves manifest (`(name, content_hash)` set + axiom closure).
    #[arg(long)]
    pub leaves: PathBuf,
    /// Optional override for the receipt's source identity.
    #[arg(long = "source-id")]
    pub source_id: Option<String>,
    /// Write the receipt JSON here (else just print the summary).
    #[arg(long)]
    pub out: Option<PathBuf>,
}

/// Arguments for `clean mathverse trust-receipt verify`.
#[derive(Debug, Args)]
pub struct TrustReceiptVerifyArgs {
    /// The receipt JSON to audit.
    #[arg(long)]
    pub receipt: PathBuf,
    /// The companion leaves manifest to re-derive the root from.
    #[arg(long)]
    pub leaves: PathBuf,
}

/// Arguments for `clean mathverse trust-receipt prove`.
#[derive(Debug, Args)]
pub struct TrustReceiptProveArgs {
    /// The receipt JSON whose root the proof is against.
    #[arg(long)]
    pub receipt: PathBuf,
    /// The companion leaves manifest.
    #[arg(long)]
    pub leaves: PathBuf,
    /// Fully-qualified declaration name to prove membership of.
    #[arg(long)]
    pub name: String,
    /// Write the membership proof JSON here (else just print the summary).
    #[arg(long)]
    pub out: Option<PathBuf>,
}

/// Verbs under `clean mathverse ratchet <verb>`.
///
/// Marked `#[non_exhaustive]` so future sibling verbs can be added without
/// breaking downstream tooling.
#[derive(Debug, clap::Subcommand)]
#[non_exhaustive]
pub enum RatchetCommands {
    /// Compare a saved `stamp-verified --json` summary against the ratcheted
    /// baseline. SKIPs green when the summary is absent (so dev pushes stay
    /// green until an operator stamps the real corpus); else fails closed on a
    /// soundness-floor breach, a malformed summary, or a KernelVerified-count
    /// regression.
    Check(RatchetCheckArgs),
    /// Raise the ratchet baseline from a saved `stamp-verified --json` summary.
    /// Requires the summary (does NOT skip) and re-asserts the soundness floor,
    /// then rewrites the baseline JSON preserving the existing operator notes.
    Update(RatchetUpdateArgs),
}

/// Verbs under `clean mathverse axiom-audit <verb>`.
///
/// Marked `#[non_exhaustive]` so future sibling verbs (e.g. `recompute`) can
/// be added without breaking downstream tooling.
#[derive(Debug, clap::Subcommand)]
#[non_exhaustive]
pub enum AxiomAuditCommands {
    /// Non-mutating release-check for the checked-in axiom audit evidence.
    ///
    /// Wraps `scripts/axiom_audit_release_check.sh` (Wave 87, bucket B).
    #[command(name = "release-check")]
    ReleaseCheck(AxiomAuditReleaseCheckArgs),
}

/// Arguments for `clean mathverse axiom-audit release-check`.
///
/// The underlying `scripts/axiom_audit_release_check.sh` script takes no
/// arguments; this empty `Args` struct keeps the variant uniform with sibling
/// verbs and reserves a place for future options.
#[derive(Debug, Clone, Default, Args)]
pub struct AxiomAuditReleaseCheckArgs {}

/// Generic passthrough: capture every remaining token verbatim and forward
/// it to the standalone-binary command implementation in
/// [`crate::mathverse_bin_cmds::commands`]. This guarantees byte-for-byte flag
/// parity with the standalone `mathverse` binary for every absorbed verb.
///
/// Issue #3512 lists ~15 flags across the 7 passthrough verbs
/// (`--semantic`, `--tag`, `--similar`, `--cross-system`, `--system`,
/// `--domain`, `--format`, `--limit`, `--force`, `--version`, `--depth`,
/// `--transitive`, …). Rather than re-declare each as a typed clap field
/// — which would duplicate the parser already in the standalone binary —
/// we capture them as `Vec<String>` and delegate. This is the same
/// technique the top-level `clean` CLI uses for `VerifyC` passthrough in
/// the `verify-c` dispatch shim.
#[derive(Debug, Args)]
pub struct PassthroughArgs {
    /// Verb-specific arguments forwarded to the standalone `mathverse <verb>`
    /// implementation. Use `--help` on the standalone `mathverse` binary to
    /// see the full per-verb flag list while migration is in progress.
    #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
    pub rest: Vec<String>,
}

/// Bounded-memory closure-loading policy (WS3): which never-unfolded proof
/// VALUES to drop from the TRUSTED imported closure env after it is built, to
/// cap resident memory when re-verifying a target module against it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, ValueEnum)]
pub enum ClosureElide {
    /// Keep every proof value resident (legacy full-resident behavior).
    None,
    /// Drop only `Opaque`-kind values. STATICALLY SOUND: the kernel never
    /// δ-unfolds an `Opaque` value, so no verdict can change. The default.
    #[default]
    Opaque,
    /// Drop `Opaque`- AND `Theorem`-kind values. Larger memory win, but NOT
    /// statically sound for this kernel (theorems can be δ-unfolded); only use
    /// when the unchanged kernel-verified-count gate has been confirmed.
    OpaqueAndTheorem,
}

impl ClosureElide {
    /// Map the CLI policy to the kernel's [`ProofValueElision`].
    #[must_use]
    pub fn to_kernel(self) -> clean_kernel::env::ProofValueElision {
        match self {
            ClosureElide::None => clean_kernel::env::ProofValueElision::None,
            ClosureElide::Opaque => clean_kernel::env::ProofValueElision::OpaqueOnly,
            ClosureElide::OpaqueAndTheorem => {
                clean_kernel::env::ProofValueElision::OpaqueAndTheorem
            }
        }
    }
}

/// Search mode: name substring, type-directed (discrimination tree),
/// structural-equivalence (rewrite-canonical digest), or BM25.
#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
pub enum SearchMode {
    /// Case-insensitive substring match on declaration names (fast).
    Name,
    /// Type-directed search through the discrimination tree: find declarations
    /// whose type structurally matches/unifies with a reference declaration's
    /// already-interned type. The reference declaration is named by `--like`
    /// (or, when `--like` is omitted, by the positional pattern). This is a
    /// real structural query — NOT a name substring or lexical match.
    Type,
    /// Structural-equivalence search: find declarations whose type is equal
    /// *up to commutative-operand rewrite* to a reference declaration's
    /// (`a + b` / `b + a`, `P ∧ Q` / `Q ∧ P`, …) — the "is this theorem
    /// already proven, differently stated?" dedup / premise-selection query.
    /// The reference declaration is named by the positional pattern. With
    /// `--index <baseline.mvix>` the corpus-wide canonical representative is
    /// looked up in microseconds via the graduation gate's semantic table;
    /// without it, the full equivalence class within the loaded shards is
    /// scanned. A hit is a candidate match, never a soundness claim.
    Structural,
    /// BM25 lexical search over names and types (higher recall, not structural).
    Semantic,
}

/// Arguments for `clean mathverse search`.
#[derive(Debug, Args)]
pub struct SearchArgs {
    /// Query pattern. Required for `--mode name` (case-insensitive substring)
    /// and `--mode semantic` (BM25 query). For `--mode type` it is interpreted
    /// as the reference declaration name when `--like` is omitted.
    pub pattern: Option<String>,
    /// Search mode selector.
    #[arg(long, value_enum, default_value_t = SearchMode::Name)]
    pub mode: SearchMode,
    /// Reference declaration name for type-directed search: return declarations
    /// whose type structurally matches this declaration's (already-interned)
    /// type via the discrimination tree. Supplying `--like` forces a
    /// type-directed query regardless of `--mode`.
    #[arg(long)]
    pub like: Option<String>,
    /// Optional `baseline.mvix` index for `--mode structural`: when present, the
    /// query's rewrite-canonical digest is looked up in the index's semantic
    /// table for the corpus-wide canonical representative in microseconds
    /// (instead of scanning the loaded shards for the full equivalence class).
    #[arg(long)]
    pub index: Option<PathBuf>,
    /// Path to the `.mathverse` shard directory.
    #[arg(long, default_value = "data/mathverse-shards")]
    pub shard_dir: PathBuf,
    /// Maximum number of results to return.
    #[arg(long, default_value_t = 20)]
    pub limit: usize,
    /// Emit JSON instead of the human-readable table.
    #[arg(long)]
    pub json: bool,
}

/// Arguments for `clean mathverse info`.
#[derive(Debug, Args)]
pub struct InfoArgs {
    /// Exact declaration name (e.g. `Nat.add_comm`).
    pub name: String,
    /// Path to the `.mathverse` shard directory.
    #[arg(long, default_value = "data/mathverse-shards")]
    pub shard_dir: PathBuf,
    /// Emit JSON instead of the human-readable view.
    #[arg(long)]
    pub json: bool,
}

/// Arguments for `clean mathverse stats`.
#[derive(Debug, Args)]
pub struct StatsArgs {
    /// Path to the `.mathverse` shard directory.
    #[arg(long, default_value = "data/mathverse-shards")]
    pub shard_dir: PathBuf,
    /// Emit JSON instead of the human-readable view.
    #[arg(long)]
    pub json: bool,
}

/// Arguments for `clean mathverse systems`.
#[derive(Debug, Args)]
pub struct SystemsArgs {
    /// Path to the `.mathverse` shard directory.
    #[arg(long, default_value = "data/mathverse-shards")]
    pub shard_dir: PathBuf,
    /// Emit JSON instead of the human-readable view.
    #[arg(long)]
    pub json: bool,
}

/// Arguments for `clean mathverse list`.
///
/// Mirrors the standalone `mathverse list` shape: filter by source system
/// (e.g. `lean4`, `metamath`, `coq`), paginate with `--limit`/`--offset`,
/// render as a table (default) or JSON (`--json`).
#[derive(Debug, Args)]
pub struct ListArgs {
    /// Filter by source-system name (case-insensitive, e.g. `lean4`).
    ///
    /// Accepts the canonical `SourceSystem` display label or its numeric id.
    /// Unknown values return zero rows rather than erroring, matching the
    /// standalone binary's "no entries" behaviour.
    #[arg(long)]
    pub system: Option<String>,
    /// Maximum number of rows to emit.
    #[arg(long, default_value_t = 20)]
    pub limit: usize,
    /// Skip the first N matching rows before emitting.
    #[arg(long, default_value_t = 0)]
    pub offset: usize,
    /// Path to the `.mathverse` shard directory.
    #[arg(long, default_value = "data/mathverse-shards")]
    pub shard_dir: PathBuf,
    /// Emit JSON instead of the human-readable table.
    #[arg(long)]
    pub json: bool,
}

/// Arguments for `clean mathverse sample`.
///
/// Deterministic stride sample: given the same `--seed` and shard set the
/// output is byte-identical across runs. Intended for exploratory browsing
/// and as a stable fixture source for downstream tooling.
#[derive(Debug, Args)]
pub struct SampleArgs {
    /// Number of declarations to return.
    #[arg(long, default_value_t = 10)]
    pub n: usize,
    /// Filter by source-system name (case-insensitive).
    #[arg(long)]
    pub system: Option<String>,
    /// Filter by trust / import-confidence level (e.g. `kernelverified`).
    #[arg(long)]
    pub trust: Option<String>,
    /// Seed for the deterministic walk (changing this rotates the sample).
    #[arg(long, default_value_t = 0)]
    pub seed: u64,
    /// Path to the `.mathverse` shard directory.
    #[arg(long, default_value = "data/mathverse-shards")]
    pub shard_dir: PathBuf,
    /// Emit JSON instead of the human-readable table.
    #[arg(long)]
    pub json: bool,
}

/// Arguments for `clean mathverse deps`.
///
/// Walks the dependency adjacency list built by the shard loader. Default
/// is a single-hop listing; pass `--transitive` (or `--depth N`) for a
/// bounded BFS closure. `--limit` caps the number of rows returned so the
/// walk cannot explode on large libraries.
#[derive(Debug, Args)]
pub struct DepsArgs {
    /// Exact declaration name (e.g. `Nat.add_comm`).
    pub name: String,
    /// Reverse direction: list the declarations that DEPEND ON `name`
    /// (its users / blast radius), ranked by impact, instead of what `name`
    /// depends on. The `uses` verb is an alias for `deps --reverse`.
    #[arg(long)]
    pub reverse: bool,
    /// Walk transitive dependencies (equivalent to `--depth usize::MAX`).
    #[arg(long)]
    pub transitive: bool,
    /// Maximum BFS depth (default 1 = direct deps only). Setting `--depth > 1`
    /// implicitly turns on `--transitive`.
    #[arg(long, default_value_t = 1)]
    pub depth: usize,
    /// Cap total rows returned across the walk.
    #[arg(long, default_value_t = 200)]
    pub limit: usize,
    /// Path to the `.mathverse` shard directory.
    #[arg(long, default_value = "data/mathverse-shards")]
    pub shard_dir: PathBuf,
    /// Emit JSON instead of the human-readable table.
    #[arg(long)]
    pub json: bool,
}

/// Arguments for `clean mathverse version`.
///
/// Prints the Mathverse Library release string and, if a shard directory is
/// present, live summary counts. Does NOT fail when the shard directory is
/// missing — returns the static release line only, matching the standalone
/// `mathverse version` behaviour.
#[derive(Debug, Args)]
pub struct VersionArgs {
    /// Path to the `.mathverse` shard directory. If absent, only the static
    /// release line is emitted.
    #[arg(long, default_value = "data/mathverse-shards")]
    pub shard_dir: PathBuf,
    /// Emit JSON instead of the human-readable view.
    #[arg(long)]
    pub json: bool,
}

/// Arguments for `clean mathverse replay-corpus`.
#[derive(Debug, Args)]
pub struct ReplayCorpusArgs {
    /// Generate the checked production corpus accounting artifact.
    #[arg(long)]
    pub production: bool,
    /// Emit a machine-readable command summary after writing the artifact.
    #[arg(long)]
    pub json: bool,
    /// Repository root containing `data/raw/mathlib4`.
    #[arg(long, default_value = ".")]
    pub root: PathBuf,
    /// Output JSON artifact path.
    #[arg(long, default_value = crate::replay_corpus::DEFAULT_REPLAY_CORPUS_OUTPUT)]
    pub output: PathBuf,
}

/// Arguments for `clean mathverse validate-replay-report`.
#[derive(Debug, Args)]
pub struct ValidateReplayReportArgs {
    /// Repository root used to rebuild deterministic corpus accounting.
    #[arg(long, default_value = ".")]
    pub root: PathBuf,
    /// Mathverse replay replacement report path.
    #[arg(long, default_value = crate::replay_report::DEFAULT_REPLAY_REPLACEMENT_REPORT)]
    pub report: PathBuf,
    /// Mathverse replay production corpus artifact path.
    #[arg(long, default_value = crate::replay_corpus::DEFAULT_REPLAY_CORPUS_OUTPUT)]
    pub corpus: PathBuf,
    /// Emit JSON validation output.
    #[arg(long)]
    pub json: bool,
}

/// Arguments for `clean mathverse stamp-verified`.
///
/// Runs the full WS5 stamping pipeline against real `.olean` input: convert
/// each module to a heuristic `.mathverse` shard (which mints zero
/// `KernelVerified`), re-verify the merged corpus in Clean's kernel via
/// [`crate::verify::incremental::verify_corpus_incremental`], and then
/// destructively stamp `KernelVerified` into the shard bytes for exactly the
/// constants the kernel accepted (`kernel_verified_names`). The stored
/// `KernelVerified` count is re-read from disk and printed in the summary.
#[derive(Debug, Args)]
pub struct StampVerifiedArgs {
    /// One or more `.olean` files, or directories scanned recursively for
    /// `.olean` files. Each module becomes one stamped `.mathverse` shard.
    #[arg(required = true)]
    pub inputs: Vec<PathBuf>,
    /// Output directory for the stamped `.mathverse` shards. Created if absent.
    #[arg(long)]
    pub out_dir: PathBuf,
    /// Optional path to write the kernel-verified manifest (the by-name record
    /// of every constant Clean's kernel accepted). Skipped if omitted.
    #[arg(long)]
    pub manifest: Option<PathBuf>,
    /// Optional `.olean` search root (e.g. `.../lib/lean`). When set, each
    /// target module's TRANSITIVE IMPORT CLOSURE is loaded into the kernel
    /// `Environment` (alongside the prelude and stdlib search paths) BEFORE the
    /// target's own constants are re-checked. This is what lets real Mathlib
    /// modules — whose proofs reference constants defined in imported modules —
    /// kernel-verify: the dependency closure is the trusted imported context,
    /// and only the TARGET module's declarations are re-minted and proof-checked
    /// against it. Without this flag the legacy prelude-only behavior is used.
    #[arg(long)]
    pub closure_root: Option<PathBuf>,
    /// Bounded-memory closure loading (WS3): which never-unfolded proof VALUES
    /// to drop from the TRUSTED imported closure env after it is built, to cap
    /// resident memory. Only meaningful together with `--closure-root`.
    /// Defaults to `opaque` — statically sound (the kernel never δ-unfolds an
    /// `Opaque` value), so the kernel-verified count is unchanged. Use `none`
    /// for the legacy full-resident behavior, or `opaque-and-theorem` for a
    /// larger (NOT statically sound) win to be validated against the gate.
    #[arg(long, value_enum, default_value_t = ClosureElide::Opaque)]
    pub closure_elide: ClosureElide,
    /// Emit the JSON summary instead of the human-readable line.
    #[arg(long)]
    pub json: bool,
    /// SINGLE-PASS mode (efficiency): instead of the legacy all-at-once merged
    /// replay, verify the target modules ONE AT A TIME in import-topological
    /// order against ONE persistent kernel `Environment`, roll-eliding each
    /// verified module's proof values (per `--closure-elide`) before the next.
    ///
    /// This reconstructs each `.olean` exactly once (no per-chunk closure
    /// rebuild) and keeps peak RSS bounded to the closure + recently-verified
    /// modules rather than the whole corpus, so the full library can be stamped
    /// in one invocation. SOUNDNESS-NEUTRAL: every constant is still installed
    /// through the same checked `verify_corpus_incremental` (`add_decl`) path;
    /// rolling elision can only make a later proof FAIL to verify (a completeness
    /// cost governed by `--closure-elide`), never falsely accept one. Requires
    /// `--closure-root`.
    #[arg(long)]
    pub single_pass: bool,
    /// PARALLEL mode (PARAGON): build ONE shared, immutable base `Environment`
    /// (every target module + its transitive dependency closure, loaded TRUSTED
    /// with theorem/opaque proof VALUES elided to bound RAM), then re-verify
    /// every value-bearing target constant CONCURRENTLY against that base — each
    /// rayon worker reconstructs a module's constants and runs the kernel's
    /// read-only `check_decl_readonly` (the same `check_type` gauntlet `add_decl`
    /// runs, minus the env mutation). This replaces the serial `--single-pass`
    /// env-threading with a read-only fan-out across cores.
    ///
    /// SOUNDNESS: identical to `--single-pass` — a constant earns `KernelVerified`
    /// ONLY if the kernel accepted its value against the trusted dependency
    /// closure; axioms and inductive families are trusted context, never stamped.
    /// Requires `--closure-root`. Takes precedence over `--single-pass`.
    #[arg(long)]
    pub parallel: bool,
    /// Worker-thread count for `--parallel` (the rayon pool size). Defaults to
    /// the number of available CPU cores. Ignored unless `--parallel` is set.
    #[arg(long)]
    pub jobs: Option<usize>,
    /// Enable the content-addressed incremental cache (paragon "import again and
    /// again efficiently"). Each module is keyed on the blake3 hash of its
    /// transitive `.olean` import closure folded with the env fingerprint; a
    /// re-run replays the cached verdict for every module whose closure is
    /// unchanged (skipping convert + kernel re-verify) and re-verifies only
    /// changed modules and their transitive dependents. A `.import_cache.json`
    /// sidecar is written under `--out-dir`. Soundness-neutral: a hit replays a
    /// verdict the kernel already minted for byte-identical inputs under an
    /// identical fingerprint. Only meaningful with `--parallel`.
    #[arg(long)]
    pub incremental: bool,
    /// EXPLICIT override of the lazy-closure shard cache directory. Highest
    /// precedence: when set (or via `CLEAN_CLOSURE_SHARDS`) the closure is
    /// served LAZILY from these v3 fail-closed `.mathverse` shards, skipping
    /// auto-discovery. A coverage/validity miss still hard-falls-back to the
    /// trusted eager `.olean` closure. Only meaningful with `--closure-root`
    /// on the SEQUENTIAL path; `--parallel` always loads its shared base eagerly
    /// (lazy serving and the parallel fan-out are not yet composed), so this flag
    /// has no effect under `--parallel`.
    #[arg(long)]
    pub closure_shards: Option<PathBuf>,
    /// Opt-in: when no lazy-closure cache is found, BUILD one once into the
    /// default co-located cache dir (`<out-dir>/../.clean-closure-shards`) and
    /// then serve lazily — the re-import workflow. Without this flag a missing
    /// cache defaults to EAGER (a one-off run never pays the build cost). Also
    /// settable via `CLEAN_BUILD_CLOSURE_CACHE=1`. Needs `--closure-root`.
    /// Sequential path only — `--parallel` loads its base eagerly and ignores it.
    #[arg(long)]
    pub build_closure_cache: bool,
    /// Force PURE EAGER closure loading, disabling lazy serving and
    /// auto-discovery entirely (equivalently `CLEAN_LAZY_CLOSURE=0`). Use this
    /// to opt out of the default-on ergonomics. Only meaningful with
    /// `--closure-root` on the SEQUENTIAL path (`--parallel` is always eager).
    #[arg(long)]
    pub no_lazy_closure: bool,
    /// TURNKEY certification: after stamping, build a trust receipt over the
    /// KernelVerified constants in `--out-dir` (equivalent to a follow-up
    /// `trust-receipt from-shards --shard-dir <out-dir>`) and write it here. One
    /// command: stamp → certify.
    #[arg(long)]
    pub receipt: Option<PathBuf>,
    /// With `--receipt`: also write the auditable leaves manifest here.
    #[arg(long = "receipt-leaves")]
    pub receipt_leaves: Option<PathBuf>,
    /// With `--receipt`: also write the provenance record here.
    #[arg(long = "receipt-provenance")]
    pub receipt_provenance: Option<PathBuf>,
    /// With `--receipt`: the source identity to certify (e.g. `Mathlib@<git-sha>`).
    #[arg(long = "source-id")]
    pub source_id: Option<String>,
}

/// Arguments for `clean mathverse per-constant-verify`.
///
/// Kernel-verifies ONE (or a few) named constant(s) defined in `--target` by
/// demand-loading only the transitive CONSTANT closure of the target — the Rust
/// analog of Lean's `getUsedConstants` fold — into a shared trusted kernel
/// environment, then running the `add_decl`-equivalent `check_type` gauntlet on
/// the target alone. This avoids the eager reconstruction of the whole module
/// IMPORT closure (250k–429k constants) that `stamp-verified --closure-root`
/// pays even for a single leaf lemma.
#[derive(Debug, Args)]
pub struct PerConstantVerifyArgs {
    /// The `.olean` module that DECLARES the target constant(s) (e.g.
    /// `.../Mathlib/Data/Real/Basic.olean`).
    #[arg(long)]
    pub target: PathBuf,
    /// One or more fully-qualified constant names to kernel-verify (e.g.
    /// `Real.zero_lt_one`). Each must be declared by `--target`. Optional when
    /// `--all-declared` is given (which selects every value-bearing constant the
    /// module declares).
    #[arg(long = "constant", required = false)]
    pub constant: Vec<String>,
    /// Kernel-verify EVERY value-bearing constant (`Definition`/`Theorem`/
    /// `Opaque`) the `--target` module declares — a whole-module trust receipt
    /// over all of them under one Merkle root. Mutually informative with
    /// `--constant` (union). Inductive families and axioms are skipped (nothing
    /// to `check_type`).
    #[arg(long = "all-declared")]
    pub all_declared: bool,
    /// `.olean` search root (e.g. `.../.lake/build/lib/lean`) used to resolve the
    /// target's transitive import closure while building the name->olean header
    /// index and demand-loading referenced constants. Sibling lake-package olean
    /// roots and the stdlib toolchain paths are discovered automatically.
    #[arg(long)]
    pub closure_root: PathBuf,
    /// Per-check reduction/inference step budget applied to the kernel
    /// (`0` = unlimited, matching Lean 4). A pure resource limit, never a
    /// soundness gate. Defaults to unlimited so a valid-but-expensive proof is
    /// never rejected for budget.
    #[arg(long, default_value_t = 0)]
    pub heartbeat: u32,
    /// Streaming elision of the TARGET module's own proof values during the
    /// `check_type` gauntlet (the bounded-memory `--all-declared` fix): once a
    /// chunk of targets PASSES, the passed values the policy selects are freed
    /// — strictly post-success, so an ill-typed value still fails on its own
    /// merits. `opaque` (default) is statically sound: the kernel never
    /// δ-unfolds an `Opaque` value, so verdicts are byte-identical to the
    /// eager run. `opaque-and-theorem` is the large memory win but
    /// refusal-only for this kernel (theorem bodies CAN be δ-unfolded): a
    /// later target may conservatively FAIL where eager passes — never the
    /// reverse — so `failed=0` under it certifies the module verdict-identical
    /// to eager (re-run any `failed>0` module with `none` to disambiguate).
    /// Forced to `none` when a receipt is requested (receipt leaves + the
    /// axiom walk read resident values after verification).
    #[arg(long = "stream-elide", value_enum, default_value_t = ClosureElide::Opaque)]
    pub stream_elide: ClosureElide,
    /// Free passed elidable target values after every chunk of this many value
    /// checks. Smaller chunks bound peak resident memory tighter at the cost
    /// of rebuilding the cache-warmed checker per chunk. Under `opaque` a pure
    /// memory/perf knob; under `opaque-and-theorem` a smaller chunk can only
    /// REFUSE more (subset direction), never pass more.
    #[arg(long = "stream-elide-chunk", default_value_t = 2048)]
    pub stream_elide_chunk: usize,
    /// Serve trusted closure constants LAZILY from a fail-closed-verified
    /// `.mathverse` closure-shard cache (built with `build-closure-shards`)
    /// instead of eagerly converting every demand-walked dependency into
    /// resident memory. Shards are content-verified ON FIRST TOUCH
    /// (source-olean digest + namespace subset + per-constant arena
    /// recon_digest — the same gates as the stamp-verified lazy path,
    /// amortized to the modules a run actually reaches); any gate failure
    /// falls back PER NAME to the eager olean walker. Omit for the
    /// fully-eager legacy behavior (byte-identical default). Forced off when
    /// a receipt is requested (receipts run on the proven eager lane).
    #[arg(long = "closure-shards")]
    pub closure_shards: Option<PathBuf>,
    /// Optional path to an incremental **content-addressed verdict cache**. When
    /// set, a target whose content + trusted-closure digests match a stored
    /// `KernelVerified` entry (under the current executable's fingerprint) skips
    /// the kernel re-check; fresh passes are recorded back. Sound by
    /// construction: the demand walk still recomputes every digest, so a hit
    /// proves byte-identical content — a changed proof always misses and
    /// re-verifies. Omit for the uncached behaviour (no regression).
    #[arg(long = "kv-cache")]
    pub kv_cache: Option<PathBuf>,
    /// Bind cached verdicts to a blake3 **content hash** of the running binary
    /// instead of the default `size:mtime` metadata stamp. Stronger in the corner
    /// cases metadata cannot see (two builds sharing size+mtime), at the cost of
    /// one ~300 MB read+hash per process (amortized over the run). Recommended for
    /// the batch/corpus path; unnecessary for a single interactive verify.
    #[arg(long = "kv-cache-content-hash")]
    pub kv_cache_content_hash: bool,
    /// Emit the target + closure content digests (the cache's reproducibility
    /// witnesses) even when no `--kv-cache` is set. Two runs on the same
    /// (target, olean tree, binary) MUST print identical digests — use this to
    /// audit determinism of the demand walk.
    #[arg(long = "print-digests")]
    pub print_digests: bool,
    /// Emit a Merkle **trust receipt** (P4) over the kernel-verified target(s) to
    /// this path: a single root hash + axiom closure + within-TCB claim,
    /// independently re-derivable from the companion leaves file. A commitment to
    /// what the kernel accepted — NOT a verification shortcut.
    #[arg(long = "receipt")]
    pub receipt: Option<PathBuf>,
    /// Emit the auditable `(name, content_hash)` leaves manifest behind the
    /// receipt to this path (needed to re-derive the root and prove membership).
    #[arg(long = "receipt-leaves")]
    pub receipt_leaves: Option<PathBuf>,
    /// Optional source identity to record in the receipt (e.g. `Mathlib@<sha>`).
    #[arg(long = "source-id")]
    pub source_id: Option<String>,
    /// Emit the JSON summary instead of the human-readable line.
    #[arg(long)]
    pub json: bool,
}

/// Arguments for `clean mathverse build-closure-shards`.
///
/// Builds the v3 fail-closed `.mathverse` closure-shard cache the lazy
/// `stamp-verified --closure-root` path serves. The target module is EXCLUDED
/// from the cache (its decls are re-minted by the replay); only its transitive
/// import closure is converted. The on-disk shards are kernel-faithful
/// full-value shards bound to their source `.olean` by digest, so a stale or
/// foreign cache fails the load-time gate and forces the eager fallback.
#[derive(Debug, Args)]
pub struct BuildClosureShardsArgs {
    /// A module `.olean` file (or a directory scanned for `.olean` files) whose
    /// transitive import closure is converted into the cache. The target itself
    /// is not written to the cache.
    pub target: PathBuf,
    /// `.olean` search root (e.g. `.../.lake/build/lib/lean`) used to resolve
    /// every imported module in the closure, mirroring the eager loader's
    /// resolution so the cache covers exactly the eager closure.
    #[arg(long)]
    pub closure_root: PathBuf,
    /// Output directory for the closure `.mathverse` shards. Created if absent.
    /// Point a later `stamp-verified --closure-shards <out>` here, or place it
    /// at the auto-discovered `<out-dir>/../.clean-closure-shards`.
    #[arg(long)]
    pub out: PathBuf,
    /// Proof-value elision policy recorded in the build summary. The BUILT
    /// shards are policy-independent (always kernel-faithful full-value);
    /// elision is a LOAD-TIME memory cap the lazy loader applies. Kept for
    /// parity with `stamp-verified` and defaults to the statically-sound
    /// `opaque`.
    #[arg(long, value_enum, default_value_t = ClosureElide::Opaque)]
    pub closure_elide: ClosureElide,
}

/// Arguments for `clean mathverse ratchet check`.
#[derive(Debug, Args)]
pub struct RatchetCheckArgs {
    /// Path to a saved `clean mathverse stamp-verified --json` summary. SKIPs
    /// green (exit 0) when this file is absent.
    #[arg(long, default_value = "data/last_stamp_summary.json")]
    pub summary: PathBuf,
    /// Path to the ratchet baseline JSON read for the monotonic-UP comparison.
    #[arg(long, default_value = "data/mathlib_kv_ratchet.json")]
    pub ratchet: PathBuf,
    /// Emit a machine-readable summary instead of the human-readable line.
    #[arg(long)]
    pub json: bool,
}

/// Arguments for `clean mathverse ratchet update`.
#[derive(Debug, Args)]
pub struct RatchetUpdateArgs {
    /// Path to a saved `clean mathverse stamp-verified --json` summary. REQUIRED
    /// (update fails closed when this file is absent — unlike `check`).
    #[arg(long, default_value = "data/last_stamp_summary.json")]
    pub summary: PathBuf,
    /// Path to the ratchet baseline JSON to rewrite from the summary.
    #[arg(long, default_value = "data/mathlib_kv_ratchet.json")]
    pub ratchet: PathBuf,
    /// Emit a machine-readable summary instead of the human-readable line.
    #[arg(long)]
    pub json: bool,
}

/// Arguments for `clean mathverse elision-gate`.
///
/// The positional order encodes the soundness direction and MUST NOT be
/// swapped: the first manifest is the statically-sound `opaque` floor, the
/// second is the `opaque-and-theorem` run that may only ADD KernelVerified.
#[derive(Debug, Args)]
pub struct ElisionGateArgs {
    /// Manifest from `--closure-elide opaque` (the statically-sound floor).
    pub opaque_manifest: PathBuf,
    /// Manifest from `--closure-elide opaque-and-theorem` (may only ADD KV,
    /// never drop one).
    pub opaque_and_theorem_manifest: PathBuf,
    /// Emit a machine-readable summary instead of the human-readable line.
    #[arg(long)]
    pub json: bool,
}

/// Arguments for `clean mathverse fingerprint`.
#[derive(Debug, Args)]
pub struct FingerprintArgs {
    /// KernelVerifiedManifest JSON to read the `env_fingerprint` from.
    pub manifest: PathBuf,
    /// Emit the fingerprint as JSON instead of the human-readable field lines.
    #[arg(long)]
    pub json: bool,
}

/// Arguments for `clean mathverse build-library`.
///
/// End-to-end orchestration: prereqs → download → convert → package → publish.
/// Each stage can be skipped via the corresponding `--skip-*` flag so the
/// command is reusable for partial rebuilds (e.g. `--skip-download` to
/// re-package from an existing shard tree).
#[derive(Debug, Args)]
pub struct BuildLibraryArgs {
    /// Working directory for downloaded source repos, converted shards, and
    /// the packaged release archive. Sources are cloned into `<data-dir>/raw/`
    /// (matching `scripts/download_all_libraries.sh`). Shards are written to
    /// `<data-dir>/mathverse-shards/` by the converter pipeline.
    #[arg(long, default_value = "/tmp/mathverse-data")]
    pub data_dir: PathBuf,
    /// Skip the prerequisite-installer pass. Use this if you have already
    /// installed `git`, `cargo`, `b3sum`, `zstd` and don't want the command
    /// touching the system package manager.
    #[arg(long)]
    pub skip_prereqs: bool,
    /// Skip cloning upstream proof system sources. Requires `<data-dir>/raw/`
    /// to already contain the expected subdirectories.
    #[arg(long)]
    pub skip_download: bool,
    /// Skip running `mathverse_convert all`. Requires `<data-dir>/mathverse-shards/`
    /// to already contain the converted `.mathverse` shards.
    #[arg(long)]
    pub skip_convert: bool,
    /// Skip packaging the shards into `mathverse-library-v*.tar.zst`. Use when
    /// you just want the shards in place for local consumption.
    #[arg(long)]
    pub skip_package: bool,
    /// Upload the packaged archive + manifest to a GitHub Release. Requires
    /// the `gh` CLI to be authenticated.
    #[arg(long)]
    pub publish: bool,
    /// GitHub Release tag (defaults to `mathverse-v<workspace-version>`).
    #[arg(long)]
    pub tag: Option<String>,
    /// GitHub repo `owner/name` for the release (defaults to
    /// `alabsystems/clean`).
    #[arg(long, default_value = "alabsystems/clean")]
    pub repo: String,
    /// Output directory for the packaged archive (default: `target/`).
    #[arg(long, default_value = "target")]
    pub package_output_dir: PathBuf,
    /// On macOS, install missing prereqs via Homebrew. On Linux, use the
    /// system package manager (apt/dnf). If false (default), the command
    /// reports missing prereqs and exits non-zero instead of installing.
    #[arg(long)]
    pub auto_install_prereqs: bool,
}

/// Args for `mathverse isabelle-slice` — closure-complete slice extraction.
#[derive(Debug, Args)]
pub struct IsabelleSliceArgs {
    /// The serial-sorted corpus to slice.
    #[arg(long)]
    pub corpus: PathBuf,
    /// Output slice file (serial-sorted, replay-ready).
    #[arg(long)]
    pub out: PathBuf,
    /// Seed serials (comma-separated; repeatable).
    #[arg(long, value_delimiter = ',')]
    pub serials: Vec<i64>,
    /// Seed name substrings (comma-separated; repeatable).
    #[arg(long, value_delimiter = ',')]
    pub names: Vec<String>,
    /// Seed from an `ISA_DUMP_REJECTS` dump file (reason<TAB>name<TAB>sig).
    #[arg(long)]
    pub reject_dump: Option<PathBuf>,
    /// Keep only dump rows with this reason (e.g. `kernel-reject`).
    #[arg(long)]
    pub reason: Option<String>,
    /// EXCLUDE the corpus's registration lines (`_def`/`_dict`) from the
    /// slice. Default is to include them so the replay's PASS-1 registries
    /// match the grand corpus (mode-seam fidelity); exclude only for minimal
    /// proof-dependency slices.
    #[arg(long)]
    pub no_registrations: bool,
}

/// Args for `mathverse isabelle-targets` — blocking-weight cascade analysis.
#[derive(Debug, Args)]
pub struct IsabelleTargetsArgs {
    /// The serial-sorted corpus to analyze.
    #[arg(long)]
    pub corpus: PathBuf,
    /// A replay snapshot whose closure keys are the accepted (KernelVerified)
    /// serials; every other present serial is treated as rejected.
    #[arg(long)]
    pub snapshot: PathBuf,
    /// Optional `ISA_DUMP_REJECTS` dump (`reason<TAB>name<TAB>sig`) joined into
    /// the table for the reason/signature columns.
    #[arg(long)]
    pub dump: Option<PathBuf>,
    /// How many top gatekeepers to print (0 = all primaries).
    #[arg(long, default_value_t = 100)]
    pub top: usize,
}

/// Args for `mathverse isabelle-index` — build the `<corpus>.idx` sidecar.
#[derive(Debug, Args)]
pub struct IsabelleIndexArgs {
    /// The serial-sorted corpus to index. The sidecar is written to
    /// `<corpus>.idx` (or `--out` when given).
    #[arg(long)]
    pub corpus: PathBuf,
    /// Override the sidecar output path (default: `<corpus>.idx`).
    #[arg(long)]
    pub out: Option<PathBuf>,
}

/// Args for `mathverse isabelle-corpus-diff` — classify two corpus versions off
/// their `.idx` sidecars.
#[derive(Debug, Args)]
pub struct IsabelleCorpusDiffArgs {
    /// The OLD corpus version (its `.idx` sidecar must exist and be current).
    #[arg(long)]
    pub old: PathBuf,
    /// The NEW corpus version (its `.idx` sidecar must exist and be current).
    #[arg(long)]
    pub new: PathBuf,
    /// Where to write the typed JSON diff report.
    #[arg(long)]
    pub out: PathBuf,
}

/// Args for `mathverse isabelle-verify-one` — single-line diagnostic verify.
#[derive(Debug, Args)]
pub struct IsabelleVerifyOneArgs {
    /// The serial-sorted corpus holding the target line.
    #[arg(long)]
    pub corpus: PathBuf,
    /// The exact proof-term serial to verify.
    #[arg(long)]
    pub serial: i64,
    /// Restore the accepted env + closure + registries from this completed
    /// replay snapshot (fingerprint ignored — a diagnostic never mints a release
    /// verdict). Omit for a minimal state built from the corpus.
    #[arg(long)]
    pub snapshot: Option<PathBuf>,
    /// Emit the per-escalation-mode outcome trace for this serial (stderr).
    #[arg(long)]
    pub modes: bool,
    /// Emit the full expected-vs-got type dump on a kernel mismatch (stderr).
    #[arg(long)]
    pub full: bool,
}

/// Args for `mathverse isabelle-lean-goal` — Path-B statement translation.
#[derive(Debug, Args)]
pub struct IsabelleLeanGoalArgs {
    /// The serial-sorted corpus holding the target line(s). Seeks via the
    /// `<corpus>.idx` sidecar when present, else a streaming scan.
    #[arg(long)]
    pub corpus: PathBuf,
    /// Single-goal mode: the exact proof-term serial to translate.
    #[arg(long)]
    pub serial: Option<i64>,
    /// Single-goal mode: the exact Isabelle theorem name to translate.
    #[arg(long)]
    pub name: Option<String>,
    /// Override the emitted Lean theorem name (default: the Isabelle name's last
    /// dotted component).
    #[arg(long = "lean-name")]
    pub lean_name: Option<String>,
    /// Batch mode: a file of candidate serials (one per line; a leading `s` and
    /// `#` comments are tolerated). Requires `--out-dir`.
    #[arg(long)]
    pub candidates: Option<PathBuf>,
    /// Batch-mode output directory (`goals/<id>.lean` stubs, `unsupported/<id>.txt`
    /// curation markers, and `manifest.json`).
    #[arg(long = "out-dir")]
    pub out_dir: Option<PathBuf>,
}

/// Args for `mathverse isabelle-doctor` — the ops preflight / health verb that
/// mechanizes every operational failure mode a re-import campaign hit, so a run
/// on a fresh or busy machine fails LOUD before burning hours.
#[derive(Debug, Args)]
pub struct IsabelleDoctorArgs {
    /// Ops working directory scanned for dead script refs; also the default home
    /// of the verify lock and the volume whose disk headroom is reported.
    /// Defaults to `$HOME/isabelle-work`.
    #[arg(long)]
    pub ops_dir: Option<PathBuf>,
    /// A corpus `.jsonl` whose `.idx` sidecar coherence is checked (line count,
    /// stored size vs. on-disk size, serial range).
    #[arg(long)]
    pub corpus: Option<PathBuf>,
    /// A replay snapshot whose ENV-LAYOUT fingerprint is checked against this
    /// binary (the `LayoutDrift` preflight).
    #[arg(long)]
    pub snapshot: Option<PathBuf>,
    /// An AFP `thys` checkout to scan for distribution-theory references that no
    /// longer resolve (`afp-skew`). Requires `--isabelle-src`; both must be set
    /// for the version-skew check to run.
    #[arg(long)]
    pub afp_thys: Option<PathBuf>,
    /// The installed Isabelle distribution `src` dir (e.g.
    /// `/path/to/Isabelle2025-2.app/src`) the `--afp-thys` references are resolved
    /// against.
    #[arg(long)]
    pub isabelle_src: Option<PathBuf>,
    /// Override the verify lock path (default `<ops-dir>/.clean_verify.lock`).
    #[arg(long)]
    pub verify_lock: Option<PathBuf>,
    /// Warn when free space on the ops volume drops below this many GiB.
    #[arg(long, default_value_t = 100)]
    pub disk_threshold_gib: u64,
    /// Unattended/CI mode: escalate advisory WARNs (binary staleness, `/tmp`
    /// durability, disk headroom) to hard FAILs so a warning still blocks the
    /// gate. Hard checks (verify-busy, corpus/index, snapshot layout, dead
    /// script refs) fail on their own regardless.
    #[arg(long)]
    pub strict: bool,
    /// Emit a machine-readable JSON report instead of the human check list.
    #[arg(long)]
    pub json: bool,
}

/// Args for `mathverse isabelle-snapshot-preserve` — copy the current binary
/// into a durable, SHA-named location so a snapshot stays resumable.
///
/// NOTE: copies `current_exe`. Run as the real `clean` binary; under a test
/// harness `current_exe` is the test binary, so the real harness must be copied
/// manually in that case.
#[derive(Debug, Args)]
pub struct IsabelleSnapshotPreserveArgs {
    /// The replay snapshot whose builder binary is being preserved (used to
    /// report the snapshot↔binary pairing from its `<snap>.provenance.json`
    /// sidecar).
    #[arg(long)]
    pub snapshot: PathBuf,
    /// The durable directory the current binary is copied into, named
    /// `clean-<sha>`.
    #[arg(long)]
    pub binaries_dir: PathBuf,
}

/// Args for `mathverse isabelle-import` — the raw-export → corpus → replay →
/// snapshot pipeline. Stage selection: `--raw-dir` runs assembly into
/// `--corpus`; omit it to replay an existing corpus. `--assemble-only` skips
/// the replay.
#[derive(Debug, Args)]
pub struct IsabelleImportArgs {
    /// Directory of per-theory `.jsonl` exports (the zproof capture hook's
    /// `ISA_ZPROOF_OUT`). When set, assembly writes/overwrites `--corpus`.
    #[arg(long)]
    pub raw_dir: Option<PathBuf>,
    /// The serial-sorted corpus file (assembly output and/or replay input).
    #[arg(long)]
    pub corpus: PathBuf,
    /// Stop after assembly (no replay).
    #[arg(long)]
    pub assemble_only: bool,
    /// Replay worker threads; 0 = the serial streaming driver.
    #[arg(long, default_value_t = 10)]
    pub workers: usize,
    /// Resume from this snapshot (corpus must be an append-only extension of
    /// the snapshotted prefix; refused otherwise).
    #[arg(long)]
    pub snapshot_in: Option<PathBuf>,
    /// **Verdict-cache retry re-measure**: re-verify ONLY the snapshot's former
    /// reject lines against the SAME corpus with the current translator (a
    /// strictly-additive translator change), instead of replaying every line. A
    /// translator-fingerprint mismatch is expected and warned, not fatal — the
    /// accepted prefix is trusted per the additive discipline. Mutually
    /// exclusive with `--snapshot-in`; the updated state is written to
    /// `--snapshot-out` when given.
    #[arg(long, conflicts_with = "snapshot_in")]
    pub retry_from: Option<PathBuf>,
    /// **Ledger burn-down**: widen `--retry-from` to also re-attempt the two-tier
    /// trusted-ledger axioms and tier-2 conditionals (not just former rejects), so
    /// a ledgered line a newly-landed prover arm can now prove flips to genuine
    /// tier-1 `KernelVerified` — shrinking the trusted-ledger support set. Tier-1
    /// KV stays byte-invariant (the accepted KV prefix is never touched). Implies
    /// the ledger lane (`ISA_TRUSTED_LEDGER`); requires `--retry-from`.
    #[arg(long, requires = "retry_from")]
    pub retry_ledger: bool,
    /// **Targeted re-attempt seed**: a file of Isabelle proof-term serials (one per
    /// line, `#` comments). When given, the `--retry-from` re-attempt set is
    /// INTERSECTED with it — only these serials (that are non-KV in the snapshot)
    /// are re-verified; every OTHER non-KV line RETAINS its snapshot verdict. Turns
    /// "did my narrow arm flip its target family at corpus scale, 0-loss" from a
    /// full ~30 h burn-down into a minutes-scale attempt of just that family. The
    /// output is a PARTIAL burn-down (only the seed's flips are new) and must NOT be
    /// read as a full re-measure. Requires `--retry-from`.
    #[arg(long, requires = "retry_from")]
    pub retry_seed: Option<PathBuf>,
    /// **Incremental grand**: an `isabelle-corpus-diff` report between the OLD
    /// corpus version (the `--retry-from` snapshot's version) and this `--corpus`
    /// (the NEW version). Widens the retry re-attempt set with the diff's NEW +
    /// CHANGED lines so a corpus VERSION bump is measured in minutes — only the
    /// increment is kernel-verified, against the OLD version's trusted snapshot
    /// prefix. REFUSED (loud) if the diff shows any change inside that trusted
    /// prefix (fall back to a full grand). Requires `--retry-from`.
    #[arg(long, requires = "retry_from")]
    pub corpus_diff: Option<PathBuf>,
    /// Save the complete post-replay state snapshot here (the next run's
    /// resume point).
    #[arg(long)]
    pub snapshot_out: Option<PathBuf>,
    /// Per-line translation node budget (pathological recorded proofs are
    /// budget-cut and honestly rejected).
    #[arg(long, default_value_t = 8_000_000)]
    pub translate_budget: u64,
    /// Assembly sort-bucket memory budget in bytes.
    #[arg(long, default_value_t = 1_073_741_824)]
    pub mem_budget: usize,
    /// Persist the KernelVerified constants as a `.mathverse` shard here,
    /// with a full per-constant provenance sidecar (source system, corpus,
    /// translator fingerprint, timestamp).
    #[arg(long)]
    pub shard_out: Option<PathBuf>,
}

/// Which wave the `isabelle-sessions` generator plans for.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, ValueEnum)]
pub enum IsabelleSessionsMode {
    /// Per-entry fragments (Wave A, and the per-entry bodies of Wave C).
    #[default]
    Afp,
    /// The six HOL-* spine capture heaps (Wave B).
    Spine,
    /// AFP-on-AFP topological DAG order only (no ROOT fragments).
    Wavec,
}

/// Args for `mathverse isabelle-sessions` — checkpointed ROOT-fragment
/// generation for the AFP capture waves (Rust port of
/// `afp_session_gen.py`; flag surface preserved).
#[derive(Debug, Args)]
pub struct IsabelleSessionsArgs {
    /// afp: per-entry fragments (Wave A/C); spine: HOL-* spine heaps
    /// (Wave B); wavec: AFP-on-AFP topo DAG only.
    #[arg(long, value_enum, default_value_t = IsabelleSessionsMode::Afp)]
    pub mode: IsabelleSessionsMode,
    /// File with one entry name per line (afp/wavec modes); `#` starts a
    /// comment (inline `# CODEGEN` / `# BIG` tags are stripped).
    #[arg(long)]
    pub entries: Option<PathBuf>,
    /// Base captured heap session (ZP-Lib3e; ZP-Lib2 for the interim probe).
    #[arg(long, default_value = "ZP-Lib3e")]
    pub parent: String,
    /// AFP `thys` checkout (afp/wavec modes).
    #[arg(long, default_value = "~/isabelle-work/afp/thys")]
    pub afp_thys: PathBuf,
    /// Source of the HOL-* directories in spine mode. Defaults to
    /// `$ISABELLE_HOME/src/HOL`; if neither this flag nor `ISABELLE_HOME` is
    /// available, spine planning fails closed. Unused in afp/wavec modes.
    #[arg(long)]
    pub hol_src: Option<PathBuf>,
    /// Output dir for fragments + manifests.
    #[arg(long)]
    pub out: PathBuf,
    /// Max theories per checkpoint session (the Lib3 lesson).
    #[arg(long, default_value_t = 12)]
    pub cap: usize,
}

/// Args for `mathverse isabelle-capture-chain` — the self-healing capture-chain
/// driver.
#[derive(Debug, Args)]
pub struct IsabelleCaptureChainArgs {
    /// Path to the JSON chain spec (segments + global build opts). The spec is
    /// the source of truth; ROOT files are GENERATED from it.
    #[arg(long)]
    pub spec: PathBuf,
    /// Override the Isabelle installation recorded in the reusable spec.
    /// This keeps checked-in operational specs machine-portable.
    #[arg(long)]
    pub isabelle_home: Option<PathBuf>,
    /// Work dir holding the durable state file + build log
    /// (`capture_chain_state.json`, `capture_chain_build.log`).
    #[arg(long, default_value = "~/isabelle-work")]
    pub work_dir: PathBuf,
    /// Continue from the on-disk state (must match the spec's hash), never
    /// retrying a response-ladder rung it already exhausted.
    #[arg(long)]
    pub resume: bool,
    /// Print the plan and generated ROOTs; build nothing.
    #[arg(long)]
    pub dry: bool,
}

/// Args for `mathverse isabelle-flip-gate` — the standing FLIP-GATE CI verb.
#[derive(Debug, Args)]
pub struct IsabelleFlipGateArgs {
    /// Replay every registered gate's pinned slice and assert its serial lands
    /// `KernelVerified`. Reports PASS/FAIL per gate; exits nonzero on any FAIL.
    #[arg(long)]
    pub check: bool,
    /// Build + verify + register a new flip gate for `--serial` sliced from
    /// `--corpus` (registers ONLY if the serial KernelVerifies under this binary).
    #[arg(long)]
    pub add: bool,
    /// (add) Source corpus the target serial's closure slice is extracted from.
    #[arg(long)]
    pub corpus: Option<PathBuf>,
    /// (add) The target proof-term serial that must flip to `KernelVerified`.
    #[arg(long)]
    pub serial: Option<i64>,
    /// (add) Free-text description of the flip (why it matters / how it flips).
    #[arg(long)]
    pub description: Option<String>,
    /// (add) The round / fix tag that made this serial flip.
    #[arg(long)]
    pub round: Option<String>,
    /// Registry file (default: `data/isabelle_flip_gates.json`).
    #[arg(long)]
    pub registry: Option<PathBuf>,
    /// Durable slice directory (default: `~/isabelle-work/corpora/flip_gates`).
    #[arg(long)]
    pub gates_dir: Option<PathBuf>,
    /// Per-line translate node budget for the replay — match the grand default so
    /// the gate is a faithful predictor of the grand's verdict.
    #[arg(long, default_value_t = 8_000_000)]
    pub translate_budget: u64,
    /// Seconds to WAIT for a verify lock held by a sibling run before giving up
    /// (0 = wait indefinitely). The gate never bypasses a held lock.
    #[arg(long, default_value_t = 3600)]
    pub lock_timeout_secs: u64,
}

/// Errors surfaced by `clean mathverse <verb>` dispatch.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum MathverseCliError {
    /// The `isabelle-import` pipeline failed (assembly, snapshot, or replay).
    #[error("isabelle-import: {0}")]
    IsabelleImport(String),
    /// The `isabelle-sessions` ROOT-fragment generator failed.
    #[error("isabelle-sessions: {0}")]
    IsabelleSessions(#[from] crate::hol::isabelle_sessions::IsabelleSessionsError),
    /// The `isabelle-capture-chain` self-healing driver failed.
    #[error("isabelle-capture-chain: {0}")]
    IsabelleCaptureChain(#[from] crate::hol::isabelle_capture_chain::CaptureChainError),
    /// Building the `<corpus>.idx` sidecar failed.
    #[error("isabelle-index: {0}")]
    IsabelleIndex(String),
    /// The `isabelle-corpus-diff` two-version classification failed.
    #[error("isabelle-corpus-diff: {0}")]
    IsabelleCorpusDiff(String),
    /// The single-line `isabelle-verify-one` diagnostic failed.
    #[error("isabelle-verify-one: {0}")]
    IsabelleVerifyOne(String),
    /// The `isabelle-lean-goal` Path-B statement translator failed (bad
    /// args, corpus/serial fetch, or a write failure).
    #[error("isabelle-lean-goal: {0}")]
    IsabelleLeanGoal(String),
    /// The `isabelle-doctor` ops preflight reported one or more FAIL checks
    /// (the report is printed before this error is returned).
    #[error("isabelle-doctor: {0}")]
    IsabelleDoctor(String),
    /// The `isabelle-snapshot-preserve` binary copy failed.
    #[error("isabelle-snapshot-preserve: {0}")]
    IsabelleSnapshotPreserve(#[from] crate::hol::isabelle_snapshot_preserve::PreserveError),
    /// The `isabelle-flip-gate` verb failed: a gate FAILed the `--check`, or an
    /// `--add` could not build/verify/register (the per-gate report is printed
    /// before this error is returned).
    #[error("isabelle-flip-gate: {0}")]
    IsabelleFlipGate(String),
    /// A `trust-receipt` verb failed (bad input, audit mismatch, missing leaf, …).
    #[error("trust-receipt: {0}")]
    TrustReceipt(String),
    /// Requested shard directory does not exist.
    #[error("shard directory `{0}` does not exist — run ./scripts/download_mathverse_library.sh")]
    ShardDirMissing(PathBuf),
    /// Failed to read an entry from the shard directory.
    #[error("failed to read shard directory `{path}`: {source}")]
    ShardDirIo {
        /// Directory that failed to read.
        path: PathBuf,
        /// Underlying IO error.
        #[source]
        source: std::io::Error,
    },
    /// Requested declaration was not present in any loaded shard.
    #[error("declaration `{0}` not found in loaded shards")]
    DeclarationNotFound(String),
    /// Semantic search returned an error from the library layer.
    #[error("semantic search failed: {0}")]
    SearchFailed(String),
    /// `clean mathverse search --mode {0}` was invoked without a query: name and
    /// semantic modes need a positional pattern; type mode needs a `--like`
    /// reference declaration (or a positional pattern naming one).
    #[error(
        "search --mode {0}: missing query (provide a pattern, or `--like <decl>` for type mode)"
    )]
    SearchMissingQuery(&'static str),
    /// Writing to stdout failed.
    #[error("failed to write output: {0}")]
    Io(#[from] std::io::Error),
    /// JSON serialization failed.
    #[error("failed to serialize JSON: {0}")]
    Json(#[from] serde_json::Error),
    /// Graduation intake / baseline-loading failed in the library layer.
    #[error(transparent)]
    Mathverse(#[from] crate::error::MathverseError),
    /// Projecting a full graduation record into the compact
    /// `mathverse-graduation-record-v1` form failed.
    #[error(transparent)]
    CompactRecord(#[from] crate::graduate::compact_record::CompactRecordError),
    /// The freshly graduated shard failed its own cake-gate self-check.
    #[error("graduated shard failed the cake gate: {0}")]
    GraduationGate(String),
    /// Baseline-index check-sample disagreed with the direct shard scan.
    #[error("baseline index check failed: {0}")]
    IndexCheck(String),
    /// Building the `graduate --env olean` source environment failed.
    #[error("graduate --env olean: {0}")]
    GraduateOleanEnv(String),
    /// Mathverse replay corpus generation failed.
    #[error(transparent)]
    ReplayCorpus(#[from] crate::replay_corpus::ReplayCorpusError),
    /// Mathverse replay report validation failed.
    #[error(transparent)]
    ReplayReport(#[from] crate::replay_report::ReplayReportError),
    /// Mathverse replay report contract failed.
    #[error("mathverse replay report validation failed: {0}")]
    ReplayReportInvalid(String),
    /// `clean mathverse stamp-verified` was given no readable `.olean` input.
    #[error("stamp-verified: no `.olean` files found in {0}")]
    StampNoInput(String),
    /// `clean mathverse stamp-verified` could not build the kernel prelude
    /// environment needed to re-verify the converted corpus.
    #[error("stamp-verified: failed to build kernel prelude environment: {0}")]
    StampPrelude(String),
    /// SOUNDNESS FLOOR VIOLATION: the heuristic `.olean` converter minted one
    /// or more `KernelVerified` headers before Clean's kernel re-verified the
    /// corpus. The heuristic importer must NEVER promote a constant to
    /// `KernelVerified` (only the kernel's `add_decl` verdict may), so a nonzero
    /// count is an invariant breach. Surfaced as a typed error (not a panic —
    /// this is a library crate) so the stamping pipeline fails closed.
    #[error(
        "stamp-verified: SOUNDNESS FLOOR VIOLATION: heuristic converter minted \
         {0} KernelVerified header(s) before kernel re-verification (must be 0); \
         only the kernel may mint KernelVerified"
    )]
    StampHeuristicMintedKernelVerified(u32),
    /// `stamp-verified` was asked to package a manifest over a directory that
    /// already holds a delta-bearing (real built/release) MathverseManifest.
    /// stamp-verified only produces a FLAT base-only library and refuses to
    /// silently overwrite an existing delta library's manifest with a flat one.
    #[error(
        "stamp-verified: refusing to overwrite an existing delta-bearing \
         library manifest in {0}; point --out-dir at a fresh directory"
    )]
    StampManifestClobber(String),
    /// `clean mathverse stamp-verified --closure-root` could not load a target
    /// module's transitive import closure into the kernel environment.
    #[error("stamp-verified: failed to load import closure for `{module}`: {reason}")]
    StampClosure {
        /// Module whose closure failed to load.
        module: String,
        /// Underlying loader failure.
        reason: String,
    },
    /// `CLEAN_LAZY_CLOSURE=1` was requested but the closure `.mathverse` shards
    /// at `CLEAN_CLOSURE_SHARDS` could not be loaded into the lazy source. This
    /// is a configuration error (bad/empty shard dir), surfaced as a hard error
    /// rather than silently degrading; a *coverage* miss instead hard-falls-back
    /// to the eager path (never an error) so no run loses a verdict.
    #[error("stamp-verified: failed to load lazy-closure shards from `{dir}`: {reason}")]
    StampLazyClosureShards {
        /// The `CLEAN_CLOSURE_SHARDS` directory.
        dir: String,
        /// Underlying shard-load failure.
        reason: String,
    },
    /// `CLEAN_REQUIRE_BOUNDED=1` (fail-closed) was set but the demand-paged,
    /// RSS-bounded PARAGON base could not be built, so the only remaining posture
    /// is the fully-resident eager base (the multi-GB floor that OOMs a small
    /// machine). Rather than silently defeat the OOM bound, the run fails closed.
    #[error("stamp-verified: CLEAN_REQUIRE_BOUNDED=1 but the demand-paged base was unavailable: {reason}")]
    StampBoundedRequired {
        /// Why the bounded base was unavailable and how to proceed.
        reason: String,
    },
    /// Unsupported Mathverse replay corpus mode.
    #[error("unsupported mathverse replay corpus mode: {0}")]
    ReplayCorpusMode(String),
    /// `clean mathverse build-library` stage failed.
    #[error("build-library {stage} stage failed: {message}")]
    BuildLibraryStage {
        /// Stage name: "prereqs", "download", "convert", "package", "publish".
        stage: &'static str,
        /// Human-readable message describing the failure.
        message: String,
    },
    /// `clean mathverse build-library` could not find a required external tool.
    #[error(
        "missing prerequisite `{tool}` — install it (e.g. `{install_hint}`) \
         or re-run with `--auto-install-prereqs`"
    )]
    MissingPrereq {
        /// Tool name that wasn't on PATH (e.g. `b3sum`, `zstd`).
        tool: &'static str,
        /// Suggested install command for the user.
        install_hint: String,
    },
    /// `clean mathverse axiom-audit <verb>` reached the mathverse-lib dispatcher
    /// instead of being intercepted by the top-level CLI shim. The handler
    /// for axiom-audit verbs lives in `clean-cli` (it shells out to scripts
    /// in the repo root), so the mathverse-lib `run` entry point must never see
    /// this variant in production. Surfaced as an error rather than a panic
    /// so callers embedding `mathverse_run` directly fail closed.
    #[error(
        "clean mathverse axiom-audit must be dispatched through the top-level \
         clean-cli shim, not via clean_mathverse::cli::run"
    )]
    AxiomAuditDispatch,
    /// SOUNDNESS FLOOR VIOLATION in the KV ratchet: the saved `stamp-verified`
    /// summary reports a nonzero `heuristic_kernel_verified`. The heuristic
    /// converter must NEVER mint `KernelVerified` (only the kernel may), so this
    /// is fail-closed on BOTH `ratchet check` and `ratchet update`.
    #[error(
        "KV ratchet SOUNDNESS FLOOR breached: heuristic_kernel_verified={0} \
         (must be 0)"
    )]
    RatchetSoundnessFloor(u32),
    /// The saved `stamp-verified` summary is missing a required integer count
    /// field or carries a non-integer (e.g. bool) value. Fail-closed: a
    /// malformed summary can never spuriously pass the ratchet.
    #[error("KV ratchet: malformed stamp summary: {0}")]
    RatchetMalformedSummary(String),
    /// One or more KernelVerified counts regressed below the ratcheted baseline
    /// (a refactor silently dropped kernel-verified stamps). Each string names
    /// the regressed key with its current value and baseline.
    #[error("KV ratchet: KernelVerified count regressed:\n  {}", .0.join("\n  "))]
    RatchetRegressed(Vec<String>),
    /// `ratchet update` was invoked without the required stamp summary present.
    /// Unlike `check`, update fails closed on an absent summary rather than
    /// skipping.
    #[error("KV ratchet update needs a stamp summary at `{0}`")]
    RatchetUpdateNoSummary(PathBuf),
    /// `elision-gate` found constants the statically-sound `opaque` floor
    /// kernel-verified that the `opaque-and-theorem` run DROPPED. Eliding
    /// theorem values may only ADD KernelVerified, never drop one.
    #[error(
        "elision gate: opaque-and-theorem elision DROPPED {} kernel-verified \
         constant(s) that opaque kept (eliding may only ADD KV, never drop \
         one):\n  {}",
        .0.len(),
        .0.join("\n  ")
    )]
    ElisionDropped(Vec<String>),
    /// `fingerprint` was asked to print the `env_fingerprint` of a manifest that
    /// carries none (a legacy manifest written before the field existed).
    #[error(
        "manifest `{0}` has no env_fingerprint (legacy manifest written before \
         the field existed)"
    )]
    MissingEnvFingerprint(PathBuf),
}

/// Dispatch entry point for `clean mathverse <verb>`.
///
/// Callers (the top-level `clean-cli` binary) construct the clap args via
/// their own parser and pass the resulting [`MathverseArgs`] here. No shelling
/// out to the deprecated `mathverse_search` or standalone `mathverse` binaries — the
/// Search/Info/Stats/Systems verbs call the library directly, and every
/// other verb calls the library-hosted `cmd_*` functions in
/// [`crate::mathverse_bin_cmds::commands`].
pub fn run(args: MathverseArgs) -> Result<(), MathverseCliError> {
    match args.command {
        MathverseCommands::Search(a) => dispatch::cmd_search(a),
        MathverseCommands::Info(a) => dispatch::cmd_info(a),
        MathverseCommands::Stats(a) => dispatch::cmd_stats(a),
        MathverseCommands::Systems(a) => dispatch::cmd_systems(a),
        MathverseCommands::List(a) => browse_dispatch::cmd_list(a),
        MathverseCommands::Sample(a) => browse_dispatch::cmd_sample(a),
        MathverseCommands::Deps(a) => browse_dispatch::cmd_deps(a),
        MathverseCommands::Uses(mut a) => {
            a.reverse = true;
            browse_dispatch::cmd_deps(a)
        }
        MathverseCommands::Version(a) => browse_dispatch::cmd_version(a),
        MathverseCommands::Find(a) => passthrough_dispatch::cmd_find(a),
        MathverseCommands::Graph(a) => passthrough_dispatch::cmd_graph(a),
        MathverseCommands::Diff(a) => passthrough_dispatch::cmd_diff(a),
        MathverseCommands::Verify(a) => passthrough_dispatch::cmd_verify(a),
        MathverseCommands::Download(a) => passthrough_dispatch::cmd_download(a),
        MathverseCommands::Upload(a) => passthrough_dispatch::cmd_upload(a),
        MathverseCommands::Serve(a) => passthrough_dispatch::cmd_serve(a),
        MathverseCommands::Export(a) => passthrough_dispatch::cmd_export(a),
        MathverseCommands::Release(a) => passthrough_dispatch::cmd_release(a),
        MathverseCommands::Graduate(a) => graduate_dispatch::cmd_graduate(a),
        MathverseCommands::IndexBuild(a) => graduate_dispatch::cmd_index_build(a),
        MathverseCommands::IndexTreeScore(a) => graduate_dispatch::cmd_index_tree_score(a),
        MathverseCommands::GraduationRecord(a) => graduate_dispatch::cmd_graduation_record(a),
        MathverseCommands::ReplayCorpus(a) => replay_dispatch::cmd_replay_corpus(a),
        MathverseCommands::ValidateReplayReport(a) => {
            replay_dispatch::cmd_validate_replay_report(a)
        }
        MathverseCommands::StampVerified(a) => stamp_verified_dispatch::cmd_stamp_verified(a),
        MathverseCommands::IsabelleImport(a) => isabelle_import_dispatch::cmd_isabelle_import(a),
        MathverseCommands::IsabelleSlice(a) => isabelle_import_dispatch::cmd_isabelle_slice(a),
        MathverseCommands::IsabelleTargets(a) => isabelle_import_dispatch::cmd_isabelle_targets(a),
        MathverseCommands::IsabelleIndex(a) => isabelle_import_dispatch::cmd_isabelle_index(a),
        MathverseCommands::IsabelleCorpusDiff(a) => {
            isabelle_import_dispatch::cmd_isabelle_corpus_diff(a)
        }
        MathverseCommands::IsabelleLeanGoal(a) => {
            isabelle_import_dispatch::cmd_isabelle_lean_goal(a)
        }
        MathverseCommands::IsabelleVerifyOne(a) => {
            isabelle_import_dispatch::cmd_isabelle_verify_one(a)
        }
        MathverseCommands::IsabelleSessions(a) => {
            isabelle_sessions_dispatch::cmd_isabelle_sessions(a)
        }
        MathverseCommands::IsabelleCaptureChain(a) => {
            isabelle_capture_chain_dispatch::cmd_isabelle_capture_chain(a)
        }
        MathverseCommands::IsabelleFlipGate(a) => {
            isabelle_flip_gate_dispatch::cmd_isabelle_flip_gate(a)
        }
        // The library path cannot see `clean-cli`'s compile-time build metadata,
        // so it runs the doctor with an UNKNOWN build identity (that check then
        // warns). The `clean` binary intercepts this verb in `cmd_mathverse.rs`
        // and supplies the real embedded identity from its `build.rs`.
        MathverseCommands::IsabelleDoctor(a) => run_isabelle_doctor(a, BuildIdentity::unknown()),
        MathverseCommands::IsabelleSnapshotPreserve(a) => {
            run_isabelle_snapshot_preserve(a, BuildIdentity::unknown())
        }
        // Per-constant verify and the trust-receipt corpus driver recurse deeply
        // through the kernel (def-eq / term reconstruction over large closures) on
        // foundational Mathlib modules — enough to overflow the 8 MB main-thread
        // stack (observed: `Order/Basic` aborts with a stack overflow). Run them on
        // a 1 GiB-stack worker, exactly as the stamp path does; virtual stack, no
        // semantic change.
        MathverseCommands::PerConstantVerify(a) => {
            on_large_stack(move || per_constant_load::cmd_per_constant_verify(a))
        }
        MathverseCommands::BuildClosureShards(a) => {
            closure_shards_dispatch::cmd_build_closure_shards(a)
        }
        MathverseCommands::BuildLibrary(a) => build_library_dispatch::cmd_build_library(a),
        MathverseCommands::AxiomAudit { .. } => Err(MathverseCliError::AxiomAuditDispatch),
        MathverseCommands::Ratchet { command } => match command {
            RatchetCommands::Check(a) => kv_guardrail_dispatch::cmd_ratchet_check(a),
            RatchetCommands::Update(a) => kv_guardrail_dispatch::cmd_ratchet_update(a),
            // `RatchetCommands` is `#[non_exhaustive]`; future sibling verbs must
            // gain a concrete arm here.
            #[allow(unreachable_patterns)]
            _ => unreachable!("unhandled RatchetCommands variant; add a dispatch arm"),
        },
        MathverseCommands::ElisionGate(a) => kv_guardrail_dispatch::cmd_elision_gate(a),
        MathverseCommands::Fingerprint(a) => kv_guardrail_dispatch::cmd_fingerprint(a),
        MathverseCommands::TrustReceipt(cmd) => {
            on_large_stack(move || trust_receipt_cmd::cmd_trust_receipt(cmd))
        }
    }
}

/// Run `f` on a worker thread with a 1 GiB stack. Deep Mathlib verification
/// recurses far enough to overflow the 8 MB main-thread stack; the stamp path
/// uses the same device. The stack is virtual (only touched pages commit) and the
/// call is otherwise transparent — same return value, semantics unchanged.
fn on_large_stack<F, R>(f: F) -> R
where
    F: FnOnce() -> R + Send + 'static,
    R: Send + 'static,
{
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(f)
        .expect("spawn large-stack worker thread")
        .join()
        .expect("large-stack worker thread panicked")
}

// Parse tests for every `clean mathverse <verb>` variant live in a sibling file
// so this module stays under the 500-line file-size cap. Same pattern as
// `browse_dispatch.rs` ↔ `browse_dispatch_tests.rs`.
#[cfg(test)]
#[path = "mod_tests.rs"]
mod tests;
