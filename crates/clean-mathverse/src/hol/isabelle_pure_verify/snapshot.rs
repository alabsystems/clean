// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Replay snapshots** — the standing re-import substrate (P2.3 of
//! `designs/2026-07-07-isabelle-100pct-industrial-import.md`).
//!
//! A snapshot captures the complete accumulated verify-time state after a
//! closure replay of a corpus **prefix**: the kernel [`Environment`], the
//! serial-keyed [`Closure`], the five PASS-1 registries, and the cumulative
//! counters. A later run over an **append-only extension** of that corpus
//! loads the snapshot, proves the prefix is byte-identical (BLAKE3 over the
//! prefix byte range), seeks directly to the first new byte, and verifies only
//! the new lines — so a regular re-import (a new Isabelle export, an AFP
//! entry) costs minutes proportional to the NEW material, not hours
//! proportional to the whole corpus.
//!
//! # Trust model — read this before relying on a snapshot
//!
//! A resumed run is an **import accelerator, not the authority**. Its verdicts
//! equal a full clean replay's under two recorded, machine-checked conditions:
//!
//! 1. **Prefix identity:** the extended corpus's first `prefix_bytes` bytes
//!    hash to the stored `prefix_blake3` (append-only extension).
//! 2. **Translator identity:** the stored `fingerprint` matches the loader's
//!    (a translator change invalidates cached verdicts — rejects could flip).
//!
//! One deliberate, documented asymmetry remains even then: a full run over the
//! extended corpus registers the NEW segment's PASS-1 registry entries before
//! replaying the prefix, while a resumed run replays the prefix from the
//! snapshot (registered without them). Because the corpus is serial-ordered
//! (definitions precede every use), a prefix line referencing a new-segment
//! registration cannot occur in well-formed exports; publication-grade numbers
//! should nevertheless come from a full clean replay (`RELEASE` runs), with
//! snapshots powering the iterative/import loop (`DEV` runs) — exactly the
//! incremental-vs-clean-build distinction in compilers.
//!
//! Format: an 8-byte magic + u32 version header, then a `bincode` (standard
//! config) payload, then a trailing BLAKE3 of the payload for corruption
//! detection. Writes are atomic (`.tmp` + rename).

use std::collections::BTreeMap;
use std::io::{Read as _, Seek as _, Write as _};
use std::path::{Path, PathBuf};

use clean_kernel::{Environment, Expr, Level};

use crate::hol::isabelle_doctor::BuildIdentity;

use super::super::isabelle_pure_translate::{
    ClassRegistry, Closure, ClosureEntry, InstanceOpRegistry, ListFnRegistry, MethodRegistry,
    PolyInstRegistry,
};
use super::PureVerifiedImport;

/// Snapshot file magic ("CLNISNAP").
const MAGIC: &[u8; 8] = b"CLNISNAP";
/// Bump on ANY incompatible change to [`ReplaySnapshot`] or the encoding.
/// v2: G4 — `PolyInstInfo` gained the `alias_of: Option<String>` field
/// (instance-link aliases + composite-keyed method-inst registrations), which
/// changes the bincode record layout of `poly_inst_registry` entries.
/// v3: verdict cache — trailing `rejects: Vec<RejectRecord>` (per-line reject
/// index: line number + byte offset + byte length) so a retry re-measure can
/// seek straight to each former reject. v2 snapshots still LOAD (see
/// [`load_snapshot`]): they migrate with an empty reject index, which the
/// retry driver derives from the corpus + closure instead.
/// v4: real-data decode fix — the five PASS-1 registries ride as an embedded
/// `serde_json` blob (see [`RegistriesBlob`]) rather than bincode, because their
/// internally-tagged `IsaType`/`IsaTerm` fields are undecodable by bincode. The
/// seam-matrix round's `ClassDefInfo::def_value: Expr` addition lands inside
/// that JSON blob (self-describing) with NO change to the bincode wire layout —
/// `registries_json` stays an opaque `Vec<u8>` — so it needs no version bump. As
/// with the pre-v4 registry breakage, a v4 snapshot written before this field
/// existed is not resumable across the change; regenerate by full replay
/// (`ISA_SNAPSHOT_OUT`). Fresh runs round-trip cleanly.
/// v5: two-tier trusted ledger — [`PureVerifiedImport`] gained the
/// `kernel_checked_ledger` / `ledger_size` / `ledger` / `written_constants`
/// fields (see [`super::PureVerifiedImport`]). Because `out` rides the bincode
/// envelope POSITIONALLY (not inside the self-describing JSON blob), the added
/// trailing fields change the wire layout, so this is a real version bump. A
/// pre-v5 snapshot is not resumable across the change; regenerate by full
/// replay (`ISA_SNAPSHOT_OUT`). Fresh runs round-trip cleanly; the ledger
/// counters + records + written-constant index ride the wire so a resumed
/// two-tier run continues its cumulative tallies.
/// v6: ENV-LAYOUT guard — the header now carries a 32-byte
/// [`env_layout_fingerprint`] BEFORE the payload length. Upstream kernel
/// `Environment` (and the other bincode-positional wire types) serde churn
/// silently invalidated snapshots — the byte stream misaligned and the payload
/// decode failed late with an opaque `Utf8Error`, discovered only at USE time.
/// The loader now recomputes the fingerprint with the CURRENT binary and rejects
/// a mismatch up front with an actionable [`SnapshotError::LayoutDrift`], BEFORE
/// any payload decode. A pre-v6 snapshot carries no fingerprint field (the
/// loader skips the check and migrates as before — best effort). Fresh runs
/// write + verify the fingerprint.
const FORMAT_VERSION: u32 = 6;
/// The first format version whose header carries the ENV-LAYOUT fingerprint.
const LAYOUT_FP_MIN_VERSION: u32 = 6;
/// The last snapshot format this loader can still decode (by migration).
const OLDEST_READABLE_VERSION: u32 = 2;
/// Decode budget: a snapshot beyond this is corrupt or hostile, not real.
const DECODE_BUDGET_BYTES: usize = 64 * 1024 * 1024 * 1024;

/// The translator fingerprint recorded in snapshots this build writes and
/// demanded of snapshots it loads. Defaults to the crate version; callers
/// SHOULD refine it with `ISA_SNAPSHOT_FINGERPRINT` (e.g. a git SHA) so every
/// translator change invalidates cached verdicts even within one version.
#[must_use]
pub fn current_fingerprint() -> String {
    std::env::var("ISA_SNAPSHOT_FINGERPRINT")
        .unwrap_or_else(|_| format!("clean-mathverse-{}", env!("CARGO_PKG_VERSION")))
}

/// Errors from snapshot save/load/validate. Typed so callers can distinguish
/// "stale/foreign snapshot" (re-run full) from I/O and corruption.
#[derive(Debug, thiserror::Error)]
pub enum SnapshotError {
    /// Filesystem failure reading or writing the snapshot or corpus.
    #[error("snapshot I/O: {0}")]
    Io(#[from] std::io::Error),
    /// Not a snapshot file (bad magic) or an incompatible format version.
    #[error("unrecognized snapshot format (magic/version mismatch: {0})")]
    Format(String),
    /// Payload digest mismatch — truncated or corrupted file.
    #[error("snapshot payload digest mismatch (corrupt file)")]
    Corrupt,
    /// Serialization / deserialization failure.
    #[error("snapshot encode/decode: {0}")]
    Codec(String),
    /// The snapshot was produced by a different translator build.
    #[error("translator fingerprint mismatch: snapshot '{snapshot}', loader '{loader}' — cached verdicts are invalid; run a full replay (or set ISA_SNAPSHOT_ALLOW_MISMATCH=1 to force)")]
    Fingerprint {
        /// Fingerprint stored in the snapshot.
        snapshot: String,
        /// The loader's fingerprint.
        loader: String,
    },
    /// The corpus's prefix bytes no longer match the snapshot (not an
    /// append-only extension of the snapshotted corpus).
    #[error("corpus prefix hash mismatch: the first {prefix_bytes} bytes are not identical to the snapshotted corpus — resume refused")]
    PrefixMismatch {
        /// Length of the snapshotted prefix in bytes.
        prefix_bytes: u64,
    },
    /// The kernel `Environment` (or another bincode-positional wire type) serde
    /// LAYOUT changed since the snapshot was written, so its payload cannot be
    /// decoded by this binary. Caught by the header ENV-LAYOUT fingerprint BEFORE
    /// any payload decode, turning a late opaque `Utf8Error` into a clear,
    /// actionable up-front refusal.
    #[error(
        "snapshot ENV-LAYOUT drift: the kernel Environment serde layout changed since this \
         snapshot was written (snapshot fingerprint {snapshot}, this binary {loader}) — the \
         payload is undecodable; regenerate the snapshot with a full replay (ISA_SNAPSHOT_OUT).{provenance}"
    )]
    LayoutDrift {
        /// The 8-byte hex prefix of the fingerprint stored in the snapshot.
        snapshot: String,
        /// The 8-byte hex prefix of this binary's fingerprint.
        loader: String,
        /// When a `<snap>.provenance.json` sidecar exists, an actionable clause
        /// naming the binary that built the snapshot (` built by <sha> at <path>;
        /// rerun with the original binary or regenerate via full replay`); empty
        /// when the sidecar is absent (back-compat / pre-provenance snapshots).
        provenance: String,
    },
}

/// A fixed, DETERMINISTIC canary whose bincode encoding fingerprints the kernel
/// / wire serde LAYOUT this binary uses for the snapshot payload. Written into
/// the v6+ header at save and recomputed at load: a mismatch means an upstream
/// serde change (a new/removed/reordered `Environment` field, a changed
/// `Expr`/`ClosureEntry`/`PureVerifiedImport` encoding) would misalign the
/// bincode byte stream and fail the payload decode late — so the loader refuses
/// up front with [`SnapshotError::LayoutDrift`].
///
/// # Why these values (and NOT `Environment::with_prelude()`)
///
/// The fingerprint must be byte-identical across two runs of the SAME binary
/// (else every resume would falsely trip). A populated `with_prelude()` is
/// unusable: its `hashbrown` maps use a randomized hasher, so iteration order —
/// and thus the encoded bytes — differ run-to-run. `Environment::default()` has
/// only EMPTY maps (length-0, order-free), so it is deterministic, while still
/// encoding every `Environment` STRUCT field (the exact churn that caused the
/// `Utf8Error` incidents shifts a length prefix or field and changes the hash).
/// A fixed nested `Expr`, a `ClosureEntry`, `PureVerifiedImport::default()` and a
/// `RejectRecord` exercise the deeper bincode-positional wire graph
/// (`Expr`/`Level`/`Name`, closure entries, the counters struct, the reject
/// index) so churn in ANY of them is caught too. All are `BTreeMap`/`Vec`/scalar
/// based ⇒ deterministic.
fn env_layout_fingerprint() -> [u8; 32] {
    // App(Sort 0, BVar 0): touches the App / Sort / Level / BVar Expr variants.
    let sample_expr = Expr::app(Expr::sort(Level::zero()), Expr::bvar(0));
    let closure_entry = ClosureEntry {
        name: "canary".to_string(),
        ty: sample_expr.clone(),
        type_param_keys: vec!["T".to_string()],
        term_param_keys: Vec::new(),
    };
    let reject = RejectRecord {
        line: 1,
        offset: 2,
        len: 3,
    };
    let canary = (
        Environment::default(),
        PureVerifiedImport::default(),
        closure_entry,
        reject,
        sample_expr,
    );
    let bytes =
        bincode::serde::encode_to_vec(&canary, bincode::config::standard()).unwrap_or_default();
    *blake3::hash(&bytes).as_bytes()
}

/// The 8-byte hex prefix of a fingerprint, for error messages.
fn fp_hex(fp: &[u8; 32]) -> String {
    fp.iter().take(8).map(|b| format!("{b:02x}")).collect()
}

/// The full 32-byte hex of a fingerprint, for the provenance sidecar (where an
/// unambiguous, complete value is wanted, not just an error-message prefix).
fn fp_hex_full(fp: &[u8; 32]) -> String {
    fp.iter().map(|b| format!("{b:02x}")).collect()
}

/// The `snapshot ↔ building-binary` pairing record written next to a snapshot at
/// SAVE time as an EXTERNAL sidecar (`<snap>.provenance.json`), so the operator
/// no longer hand-tracks which binary a snapshot needs. It is deliberately NOT
/// part of the snapshot wire format (no [`FORMAT_VERSION`] bump): loading never
/// requires it, and a pre-provenance snapshot simply has no sidecar.
///
/// The `binary_git_sha` threads down from the CLI's compile-time build identity
/// ([`BuildIdentity`], which `clean-cli`'s `build.rs` embeds); the env-driven
/// library replay path has no such identity, so it records `"unknown"` — the
/// always-present [`Self::binary_path`] (the running `current_exe`) is the
/// durable pairing key regardless.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SnapshotProvenance {
    /// Full git SHA of the binary that wrote the snapshot, or `"unknown"` when
    /// no build identity was threaded (the env-driven library replay path).
    pub binary_git_sha: String,
    /// Filesystem path of the running binary at save time (`current_exe`), or
    /// `"unknown"` if it could not be resolved.
    pub binary_path: String,
    /// Full hex of the ENV-LAYOUT fingerprint this binary computes (matches the
    /// v6 header guard; recorded for cross-checking against a loader).
    pub env_layout_fp: String,
    /// Full hex of the snapshotted corpus prefix's BLAKE3
    /// (`ReplaySnapshot::prefix_blake3`).
    pub corpus_fingerprint: String,
    /// Unix timestamp (seconds) the sidecar was written.
    pub created_unix: u64,
}

impl SnapshotProvenance {
    /// Capture the current binary's provenance for a snapshot whose corpus prefix
    /// hashes to `corpus_fingerprint`. `build` is the (optional) threaded build
    /// identity; a missing SHA records `"unknown"`.
    #[must_use]
    pub fn capture(build: Option<&BuildIdentity>, corpus_fingerprint: &[u8; 32]) -> Self {
        let binary_git_sha = build
            .and_then(|b| b.git_sha.clone())
            .unwrap_or_else(|| "unknown".to_string());
        let binary_path = std::env::current_exe()
            .map(|p| p.display().to_string())
            .unwrap_or_else(|_| "unknown".to_string());
        let created_unix = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs())
            .unwrap_or(0);
        SnapshotProvenance {
            binary_git_sha,
            binary_path,
            env_layout_fp: fp_hex_full(&env_layout_fingerprint()),
            corpus_fingerprint: fp_hex_full(corpus_fingerprint),
            created_unix,
        }
    }
}

/// The provenance sidecar path for a snapshot: `<snap>.provenance.json`.
#[must_use]
pub fn provenance_sidecar_path(snapshot: &Path) -> PathBuf {
    let mut name = snapshot.as_os_str().to_os_string();
    name.push(".provenance.json");
    PathBuf::from(name)
}

/// Atomically write the provenance sidecar for `snapshot` (`.tmp` + rename).
///
/// # Errors
/// I/O or JSON-encoding failures.
pub fn write_provenance_sidecar(
    snapshot: &Path,
    prov: &SnapshotProvenance,
) -> Result<(), SnapshotError> {
    let path = provenance_sidecar_path(snapshot);
    let json = serde_json::to_vec_pretty(prov)
        .map_err(|e| SnapshotError::Codec(format!("provenance sidecar: {e}")))?;
    let mut tmp = path.clone().into_os_string();
    tmp.push(".tmp");
    let tmp = PathBuf::from(tmp);
    std::fs::write(&tmp, &json)?;
    std::fs::rename(&tmp, &path)?;
    Ok(())
}

/// Read the provenance sidecar for `snapshot`, if present and well-formed.
/// Best-effort: a missing or corrupt sidecar yields `None` (loading a snapshot
/// never requires one — back-compat).
#[must_use]
pub fn read_provenance_sidecar(snapshot: &Path) -> Option<SnapshotProvenance> {
    let bytes = std::fs::read(provenance_sidecar_path(snapshot)).ok()?;
    serde_json::from_slice(&bytes).ok()
}

/// The `LayoutDrift` provenance clause: names the binary that built the snapshot
/// when a sidecar exists, so a drift refusal points straight at the binary to
/// rerun. Empty when there is no sidecar (pre-provenance snapshot).
fn layout_drift_provenance_hint(snapshot: &Path) -> String {
    match read_provenance_sidecar(snapshot) {
        Some(p) => format!(
            " built by {} at {}; rerun with the original binary or regenerate via full replay",
            p.binary_git_sha, p.binary_path
        ),
        None => String::new(),
    }
}

/// One REJECTED corpus line, addressed for direct re-verification: its line
/// number (the kernel anon-naming / progress index), the byte offset of its
/// first byte, and its byte length **including the trailing delimiter(s)** —
/// exactly the bytes a `read_until(b'\n')` consumed, so a retry driver can
/// `seek(offset)` + read `len` bytes and reproduce the driver's line view.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct RejectRecord {
    /// Zero-based corpus line number (empty lines counted, exactly like the
    /// drivers' running index).
    pub line: u64,
    /// Byte offset of the line's first byte in the corpus file.
    pub offset: u64,
    /// Byte length including the trailing `\n` (and `\r` if present).
    pub len: u64,
}

/// The complete resumable state of a closure replay over a corpus prefix.
#[derive(serde::Serialize, serde::Deserialize)]
pub struct ReplaySnapshot {
    /// Translator identity that produced these verdicts.
    pub fingerprint: String,
    /// Number of corpus LINES fully verified (the resume line index).
    pub prefix_lines: usize,
    /// Number of corpus BYTES those lines occupy (the resume seek offset).
    pub prefix_bytes: u64,
    /// BLAKE3 of the corpus byte range `[0, prefix_bytes)`.
    pub prefix_blake3: [u8; 32],
    /// Cumulative import counters over the prefix.
    pub out: PureVerifiedImport,
    /// The kernel environment after the prefix (values elided if the run
    /// elided; `lazy_source` is not serialized and resets to default).
    pub env: Environment,
    /// Serial → verified-entry closure over the prefix.
    pub closure: Closure,
    /// PASS-1 registries as of the snapshot (refreshed additively on resume).
    pub class_registry: ClassRegistry,
    /// See [`Self::class_registry`].
    pub method_registry: MethodRegistry,
    /// See [`Self::class_registry`].
    pub instance_op_registry: InstanceOpRegistry,
    /// See [`Self::class_registry`].
    pub list_fn_registry: ListFnRegistry,
    /// See [`Self::class_registry`].
    pub poly_inst_registry: PolyInstRegistry,
    /// Per-reason rejection tallies at snapshot time (duplicated from `out`
    /// for cheap inspection without decoding counters elsewhere).
    pub rejection_reasons: BTreeMap<String, usize>,
    /// The **verdict cache**'s reject index (v3+): every line the snapshotted
    /// run REJECTED, in ascending line order, each directly addressable by
    /// byte offset. Under the strictly-additive translator discipline the
    /// accepted lines stay accepted with the same declarations, so a
    /// translator change needs to re-verify ONLY these lines (see
    /// [`super::retry`]). Empty on a v2-migrated snapshot — the retry driver
    /// then derives the set from the corpus + closure keys, guarded by an
    /// exact count check against [`Self::out`].
    pub rejects: Vec<RejectRecord>,
}

/// The v2 on-disk layout of [`ReplaySnapshot`] (no `rejects` index), kept so
/// pre-verdict-cache snapshots (e.g. a grand run's output) still load. Field
/// order matters: bincode encodes structs positionally.
#[derive(serde::Deserialize)]
struct ReplaySnapshotV2 {
    fingerprint: String,
    prefix_lines: usize,
    prefix_bytes: u64,
    prefix_blake3: [u8; 32],
    out: PureVerifiedImport,
    env: Environment,
    closure: Closure,
    class_registry: ClassRegistry,
    method_registry: MethodRegistry,
    instance_op_registry: InstanceOpRegistry,
    list_fn_registry: ListFnRegistry,
    poly_inst_registry: PolyInstRegistry,
    rejection_reasons: BTreeMap<String, usize>,
}

impl From<ReplaySnapshotV2> for ReplaySnapshot {
    fn from(v2: ReplaySnapshotV2) -> Self {
        ReplaySnapshot {
            fingerprint: v2.fingerprint,
            prefix_lines: v2.prefix_lines,
            prefix_bytes: v2.prefix_bytes,
            prefix_blake3: v2.prefix_blake3,
            out: v2.out,
            env: v2.env,
            closure: v2.closure,
            class_registry: v2.class_registry,
            method_registry: v2.method_registry,
            instance_op_registry: v2.instance_op_registry,
            list_fn_registry: v2.list_fn_registry,
            poly_inst_registry: v2.poly_inst_registry,
            rejection_reasons: v2.rejection_reasons,
            rejects: Vec::new(),
        }
    }
}

/// The five PASS-1 registries in JSON-safe pair form. The registry Info
/// structs embed the corpus data types `IsaType`/`IsaTerm`, which are
/// INTERNALLY TAGGED (`#[serde(tag = "k")]` — their corpus-JSON home format);
/// internally-tagged enums require a self-describing format, so bincode
/// cannot decode them (`Serde(AnyNotSupported)` — the v2/v3 real-data loader
/// bug). v4 therefore carries the registries as an embedded `serde_json`
/// blob inside the bincode envelope; tuple map keys ride as pair vectors.
#[derive(serde::Serialize, serde::Deserialize)]
struct RegistriesBlob {
    class: Vec<(String, super::super::isabelle_pure_translate::ClassDefInfo)>,
    method: Vec<(String, super::super::isabelle_pure_translate::MethodDefInfo)>,
    instance_op: Vec<(
        (String, String),
        super::super::isabelle_pure_translate::InstanceOpInfo,
    )>,
    list_fn: Vec<(String, super::super::isabelle_pure_translate::ListFnInfo)>,
    poly_inst: Vec<(String, super::super::isabelle_pure_translate::PolyInstInfo)>,
}

/// Borrowed serialize-side twin of [`SnapshotWireV4`] (field order and types
/// MUST match — bincode encodes positionally and `&T` encodes exactly as `T`).
#[derive(serde::Serialize)]
struct SnapshotWireV4Ref<'a> {
    fingerprint: &'a str,
    prefix_lines: usize,
    prefix_bytes: u64,
    prefix_blake3: [u8; 32],
    out: &'a PureVerifiedImport,
    env: &'a Environment,
    closure: &'a Closure,
    registries_json: Vec<u8>,
    rejection_reasons: &'a BTreeMap<String, usize>,
    rejects: &'a [RejectRecord],
}

/// The v4 on-disk layout: everything bincode-friendly stays positional
/// bincode; the registries are a nested JSON blob (see [`RegistriesBlob`]).
#[derive(serde::Serialize, serde::Deserialize)]
struct SnapshotWireV4 {
    fingerprint: String,
    prefix_lines: usize,
    prefix_bytes: u64,
    prefix_blake3: [u8; 32],
    out: PureVerifiedImport,
    env: Environment,
    closure: Closure,
    registries_json: Vec<u8>,
    rejection_reasons: BTreeMap<String, usize>,
    rejects: Vec<RejectRecord>,
}

impl TryFrom<SnapshotWireV4> for ReplaySnapshot {
    type Error = SnapshotError;
    fn try_from(w: SnapshotWireV4) -> Result<Self, SnapshotError> {
        // The registries carry stored HOL types/terms (poly-inst bodies, method
        // operation types) that can nest deeper than serde_json's default 128-level
        // recursion cap — a full grand snapshot's `poly_inst` blob overflows it.
        // Disable the cap on decode (mirroring `isabelle_pure::parse_proven_theorem`);
        // this relaxes decoding ONLY and does not change the wire layout. Run under a
        // large `RUST_MIN_STACK` so the recursive descent does not overflow the stack.
        let mut de = serde_json::Deserializer::from_slice(&w.registries_json);
        de.disable_recursion_limit();
        let blob = <RegistriesBlob as serde::Deserialize>::deserialize(&mut de)
            .map_err(|e| SnapshotError::Codec(format!("registries blob: {e}")))?;
        de.end()
            .map_err(|e| SnapshotError::Codec(format!("registries blob: {e}")))?;
        Ok(ReplaySnapshot {
            fingerprint: w.fingerprint,
            prefix_lines: w.prefix_lines,
            prefix_bytes: w.prefix_bytes,
            prefix_blake3: w.prefix_blake3,
            out: w.out,
            env: w.env,
            closure: w.closure,
            class_registry: blob.class.into_iter().collect(),
            method_registry: blob.method.into_iter().collect(),
            instance_op_registry: blob.instance_op.into_iter().collect(),
            list_fn_registry: blob.list_fn.into_iter().collect(),
            poly_inst_registry: blob.poly_inst.into_iter().collect(),
            rejection_reasons: w.rejection_reasons,
            rejects: w.rejects,
        })
    }
}

/// BLAKE3 of the first `prefix_bytes` bytes of `corpus`, streamed.
///
/// # Errors
/// I/O failures reading the corpus.
pub fn hash_corpus_prefix(corpus: &Path, prefix_bytes: u64) -> Result<[u8; 32], SnapshotError> {
    let mut f = std::fs::File::open(corpus)?;
    let mut hasher = blake3::Hasher::new();
    let mut remaining = prefix_bytes;
    let mut buf = vec![0u8; 8 * 1024 * 1024];
    while remaining > 0 {
        let want = buf
            .len()
            .min(usize::try_from(remaining).unwrap_or(buf.len()));
        let got = f.read(&mut buf[..want])?;
        if got == 0 {
            return Err(SnapshotError::Format(format!(
                "corpus shorter than snapshot prefix ({prefix_bytes} bytes)"
            )));
        }
        hasher.update(&buf[..got]);
        remaining -= got as u64;
    }
    Ok(*hasher.finalize().as_bytes())
}

/// Serialize and atomically write `snap` to `path` (`.tmp` + rename), with the
/// magic/version header and a trailing payload digest, then write the external
/// `<snap>.provenance.json` sidecar pairing the snapshot to the building binary.
///
/// `build` is the optional threaded build identity (`clean-cli` embeds a real
/// git SHA via `build.rs`; the env-driven library replay path has none and
/// records `"unknown"`). The sidecar is EXTERNAL — it never affects the snapshot
/// wire format or loadability — so a sidecar-write failure is a loud warning, not
/// a hard error: the authoritative snapshot has already been written.
///
/// # Errors
/// I/O or encoding failures WRITING THE SNAPSHOT; the target is left untouched on
/// such a failure. A failed sidecar write is warned, not returned.
pub fn save_snapshot(
    path: &Path,
    snap: &ReplaySnapshot,
    build: Option<&BuildIdentity>,
) -> Result<(), SnapshotError> {
    // Registries carry internally-tagged corpus enums -> JSON blob (see
    // [`RegistriesBlob`]); everything else stays positional bincode.
    #[derive(serde::Serialize)]
    struct BlobRef<'a> {
        class: Vec<(
            &'a String,
            &'a super::super::isabelle_pure_translate::ClassDefInfo,
        )>,
        method: Vec<(
            &'a String,
            &'a super::super::isabelle_pure_translate::MethodDefInfo,
        )>,
        instance_op: Vec<(
            &'a (String, String),
            &'a super::super::isabelle_pure_translate::InstanceOpInfo,
        )>,
        list_fn: Vec<(
            &'a String,
            &'a super::super::isabelle_pure_translate::ListFnInfo,
        )>,
        poly_inst: Vec<(
            &'a String,
            &'a super::super::isabelle_pure_translate::PolyInstInfo,
        )>,
    }
    let registries_json = serde_json::to_vec(&BlobRef {
        class: snap.class_registry.iter().collect(),
        method: snap.method_registry.iter().collect(),
        instance_op: snap.instance_op_registry.iter().collect(),
        list_fn: snap.list_fn_registry.iter().collect(),
        poly_inst: snap.poly_inst_registry.iter().collect(),
    })
    .map_err(|e| SnapshotError::Codec(format!("registries blob: {e}")))?;
    let wire = SnapshotWireV4Ref {
        fingerprint: &snap.fingerprint,
        prefix_lines: snap.prefix_lines,
        prefix_bytes: snap.prefix_bytes,
        prefix_blake3: snap.prefix_blake3,
        out: &snap.out,
        env: &snap.env,
        closure: &snap.closure,
        registries_json,
        rejection_reasons: &snap.rejection_reasons,
        rejects: &snap.rejects,
    };
    let payload = bincode::serde::encode_to_vec(&wire, bincode::config::standard())
        .map_err(|e| SnapshotError::Codec(e.to_string()))?;
    let digest = blake3::hash(&payload);
    let layout_fp = env_layout_fingerprint();
    let tmp = path.with_extension("tmp");
    {
        let mut w = std::io::BufWriter::new(std::fs::File::create(&tmp)?);
        w.write_all(MAGIC)?;
        w.write_all(&FORMAT_VERSION.to_le_bytes())?;
        // v6+ ENV-LAYOUT guard: the fingerprint rides the header BEFORE the
        // payload length so the loader can reject a layout drift without reading
        // (let alone decoding) the payload.
        w.write_all(&layout_fp)?;
        w.write_all(&(payload.len() as u64).to_le_bytes())?;
        w.write_all(&payload)?;
        w.write_all(digest.as_bytes())?;
        w.flush()?;
    }
    std::fs::rename(&tmp, path)?;
    // External provenance sidecar (deliberately AFTER the snapshot rename, and
    // best-effort): pairs the snapshot to the binary that built it. Loading never
    // requires it, so a failure here must not undo an otherwise-complete save.
    let prov = SnapshotProvenance::capture(build, &snap.prefix_blake3);
    if let Err(e) = write_provenance_sidecar(path, &prov) {
        eprintln!(
            "WARNING: snapshot saved but provenance sidecar not written for {}: {e}",
            path.display()
        );
    }
    Ok(())
}

/// Build a v6 CHECKPOINT snapshot from BORROWED in-flight replay state (it
/// CLONES — the run continues) and atomically write it via [`save_snapshot`]
/// (`.tmp` + rename) plus the provenance sidecar. The result is a NORMAL v6
/// prefix snapshot at `prefix_lines`/`prefix_bytes`, byte-for-byte loadable and
/// resumable through the unchanged `ISA_SNAPSHOT_IN` / `--retry-from` machinery.
///
/// Shared by the two drivers' periodic crash/stall insurance so neither
/// duplicates the snapshot-build + atomic-write + sidecar logic:
///
/// * the streaming driver ([`super::streaming`]) passes the GROWING prefix hash
///   it recomputes each checkpoint (its prefix advances line by line);
/// * the retry driver ([`super::retry`]) passes its FIXED loaded prefix hash
///   (a retry never moves the prefix boundary — it only flips lines within it —
///   so re-hashing the multi-GB prefix each checkpoint would be pure waste).
///
/// The `fingerprint` is the CURRENT translator's ([`current_fingerprint`]);
/// `build` identity is `None` for the env-driven library path (matching the
/// final save).
///
/// # Errors
/// I/O or encoding failures WRITING THE SNAPSHOT (a failed sidecar write is
/// warned inside [`save_snapshot`], not returned).
#[allow(clippy::too_many_arguments)]
pub(super) fn write_checkpoint(
    ckpt_path: &Path,
    prefix_lines: usize,
    prefix_bytes: u64,
    prefix_blake3: [u8; 32],
    out: &PureVerifiedImport,
    env: &Environment,
    closure: &Closure,
    class_registry: &ClassRegistry,
    method_registry: &MethodRegistry,
    instance_op_registry: &InstanceOpRegistry,
    list_fn_registry: &ListFnRegistry,
    poly_inst_registry: &PolyInstRegistry,
    rejects: &[RejectRecord],
) -> Result<(), SnapshotError> {
    let snap = ReplaySnapshot {
        fingerprint: current_fingerprint(),
        prefix_lines,
        prefix_bytes,
        prefix_blake3,
        rejection_reasons: out.rejection_reasons.clone(),
        out: out.clone(),
        env: env.clone(),
        closure: closure.clone(),
        class_registry: class_registry.clone(),
        method_registry: method_registry.clone(),
        instance_op_registry: instance_op_registry.clone(),
        list_fn_registry: list_fn_registry.clone(),
        poly_inst_registry: poly_inst_registry.clone(),
        rejects: rejects.to_vec(),
    };
    save_snapshot(ckpt_path, &snap, None)
}

/// Load, verify (magic, version, digest, fingerprint) and return a snapshot.
/// Fingerprint mismatch is an error unless `ISA_SNAPSHOT_ALLOW_MISMATCH=1`.
///
/// # Errors
/// See [`SnapshotError`] variants.
pub fn load_snapshot(path: &Path) -> Result<ReplaySnapshot, SnapshotError> {
    let snap = load_snapshot_unfingerprinted(path)?;
    let loader = current_fingerprint();
    if snap.fingerprint != loader
        && std::env::var("ISA_SNAPSHOT_ALLOW_MISMATCH").as_deref() != Ok("1")
    {
        return Err(SnapshotError::Fingerprint {
            snapshot: snap.fingerprint,
            loader,
        });
    }
    Ok(snap)
}

/// [`load_snapshot`] for the **retry re-measure** ([`super::retry`]): a
/// fingerprint mismatch is EXPECTED there — the whole point of a retry is
/// that the translator changed — so it is reported as a loud warning, never
/// an error. Magic/version/digest checks are identical to [`load_snapshot`].
///
/// # Trust model
/// The accepted prefix (env + closure) is trusted ACROSS the translator
/// change on the strength of the strictly-additive verdict discipline
/// (every translator round proves "0 former-KV lost" at slice scale via KV
/// name+serial dumps, enforced by the slice gates) — NOT on fingerprint
/// identity. The reject set is re-verified from scratch, so nothing cached
/// about a reject survives. Publication-grade numbers still come from full
/// clean replays; see the module docs.
///
/// # Errors
/// See [`SnapshotError`] variants (all but `Fingerprint`).
pub fn load_snapshot_retry(path: &Path) -> Result<ReplaySnapshot, SnapshotError> {
    let snap = load_snapshot_unfingerprinted(path)?;
    let loader = current_fingerprint();
    if snap.fingerprint != loader {
        eprintln!(
            "RETRY: translator fingerprint changed (snapshot '{}', loader '{loader}') — \
             re-verifying the reject set under the new translator; the accepted prefix is \
             trusted per the strictly-additive discipline",
            snap.fingerprint
        );
    }
    Ok(snap)
}

/// Shared header/digest/decode path: everything [`load_snapshot`] does except
/// the fingerprint policy. Decodes v3 natively and migrates v2 (empty reject
/// index) with a loud notice.
fn load_snapshot_unfingerprinted(path: &Path) -> Result<ReplaySnapshot, SnapshotError> {
    let mut f = std::fs::File::open(path)?;
    let mut magic = [0u8; 8];
    f.read_exact(&mut magic)?;
    if &magic != MAGIC {
        return Err(SnapshotError::Format("bad magic".to_string()));
    }
    let mut ver = [0u8; 4];
    f.read_exact(&mut ver)?;
    let version = u32::from_le_bytes(ver);
    if !(OLDEST_READABLE_VERSION..=FORMAT_VERSION).contains(&version) {
        return Err(SnapshotError::Format(format!(
            "version {version}, loader supports {OLDEST_READABLE_VERSION}..={FORMAT_VERSION}"
        )));
    }
    // v6+ ENV-LAYOUT guard: read the stored fingerprint and compare it to this
    // binary's BEFORE any payload decode. A mismatch means the kernel Environment
    // (or another bincode-positional wire type) serde layout changed, so the
    // payload would misalign — refuse up front with an actionable error instead
    // of a late opaque `Utf8Error`. Pre-v6 snapshots carry no fingerprint field
    // (the check is skipped; they migrate as before).
    if version >= LAYOUT_FP_MIN_VERSION {
        let mut stored_fp = [0u8; 32];
        f.read_exact(&mut stored_fp)?;
        let current_fp = env_layout_fingerprint();
        if stored_fp != current_fp {
            return Err(SnapshotError::LayoutDrift {
                snapshot: fp_hex(&stored_fp),
                loader: fp_hex(&current_fp),
                provenance: layout_drift_provenance_hint(path),
            });
        }
    }
    let mut len8 = [0u8; 8];
    f.read_exact(&mut len8)?;
    let len = usize::try_from(u64::from_le_bytes(len8))
        .map_err(|_| SnapshotError::Format("payload length".to_string()))?;
    if len > DECODE_BUDGET_BYTES {
        return Err(SnapshotError::Format(format!(
            "payload {len} bytes exceeds decode budget"
        )));
    }
    let mut payload = vec![0u8; len];
    f.read_exact(&mut payload)?;
    let mut digest = [0u8; 32];
    f.read_exact(&mut digest)?;
    if blake3::hash(&payload).as_bytes() != &digest {
        return Err(SnapshotError::Corrupt);
    }
    let snap: ReplaySnapshot = if version == FORMAT_VERSION {
        let wire: SnapshotWireV4 =
            bincode::serde::decode_from_slice(&payload, bincode::config::standard())
                .map(|(s, _): (SnapshotWireV4, usize)| s)
                .map_err(|e| SnapshotError::Codec(e.to_string()))?;
        ReplaySnapshot::try_from(wire)?
    } else if version == 3 {
        eprintln!("SNAPSHOT MIGRATE: v3 -> v{FORMAT_VERSION}");
        bincode::serde::decode_from_slice(&payload, bincode::config::standard())
            .map(|(s, _): (ReplaySnapshot, usize)| s)
            .map_err(|e| migrate_err(3, e))?
    } else {
        eprintln!(
            "SNAPSHOT MIGRATE: v{version} -> v{FORMAT_VERSION} (no stored reject index; \
             a retry re-measure will derive it from the corpus + closure)"
        );
        bincode::serde::decode_from_slice(&payload, bincode::config::standard())
            .map(|(s, _): (ReplaySnapshotV2, usize)| ReplaySnapshot::from(s))
            .map_err(|e| migrate_err(version, e))?
    };
    Ok(snap)
}

/// The cheap header identity of a snapshot, read WITHOUT decoding (or even
/// reading) the payload: its format version, and — for v6+ files carrying the
/// ENV-LAYOUT guard — whether the stored fingerprint matches THIS binary's. The
/// ops doctor uses this to flag [`SnapshotError::LayoutDrift`] up front (the
/// exact failure a snapshot built by an older binary layout hits at load) with
/// no memory cost, instead of a full [`load_snapshot`].
#[derive(Debug, Clone)]
pub struct SnapshotHeaderInfo {
    /// The on-disk format version (in `OLDEST_READABLE_VERSION..=FORMAT_VERSION`).
    pub version: u32,
    /// TRUE when the file is v6+ and therefore carries an ENV-LAYOUT
    /// fingerprint. Pre-v6 snapshots have none ([`Self::layout_matches`] is then
    /// reported `true` — there is no fingerprint to disagree with).
    pub has_layout_fp: bool,
    /// For a v6+ file, whether the stored ENV-LAYOUT fingerprint equals this
    /// binary's — i.e. the payload would decode without drift. `true` for pre-v6
    /// files.
    pub layout_matches: bool,
    /// 8-byte hex prefix of the fingerprint stored in the snapshot (empty for
    /// pre-v6 files).
    pub snapshot_fp_hex: String,
    /// 8-byte hex prefix of this binary's current ENV-LAYOUT fingerprint.
    pub loader_fp_hex: String,
}

/// Read a snapshot's header identity (magic, version, and — v6+ — the ENV-LAYOUT
/// fingerprint match) WITHOUT decoding the payload. Reuses the module's own
/// [`MAGIC`]/version constants and [`env_layout_fingerprint`], so it can never
/// drift from the real [`load_snapshot`] parser.
///
/// # Errors
/// [`SnapshotError::Format`] on a bad magic or an out-of-range version;
/// [`SnapshotError::Io`] on a truncated header.
pub fn inspect_snapshot_header(path: &Path) -> Result<SnapshotHeaderInfo, SnapshotError> {
    let mut f = std::fs::File::open(path)?;
    let mut magic = [0u8; 8];
    f.read_exact(&mut magic)?;
    if &magic != MAGIC {
        return Err(SnapshotError::Format("bad magic".to_string()));
    }
    let mut ver = [0u8; 4];
    f.read_exact(&mut ver)?;
    let version = u32::from_le_bytes(ver);
    if !(OLDEST_READABLE_VERSION..=FORMAT_VERSION).contains(&version) {
        return Err(SnapshotError::Format(format!(
            "version {version}, loader supports {OLDEST_READABLE_VERSION}..={FORMAT_VERSION}"
        )));
    }
    let loader_fp = env_layout_fingerprint();
    if version >= LAYOUT_FP_MIN_VERSION {
        let mut stored_fp = [0u8; 32];
        f.read_exact(&mut stored_fp)?;
        return Ok(SnapshotHeaderInfo {
            version,
            has_layout_fp: true,
            layout_matches: stored_fp == loader_fp,
            snapshot_fp_hex: fp_hex(&stored_fp),
            loader_fp_hex: fp_hex(&loader_fp),
        });
    }
    Ok(SnapshotHeaderInfo {
        version,
        has_layout_fp: false,
        layout_matches: true,
        snapshot_fp_hex: String::new(),
        loader_fp_hex: fp_hex(&loader_fp),
    })
}

/// Wrap a v2/v3 migration decode failure with the known real-data caveat:
/// those formats bincode-encoded the registries, whose `IsaType`/`IsaTerm`
/// fields are internally tagged and undecodable by bincode whenever the
/// registries are non-empty (every real corpus). v4 fixed the wire format;
/// old real-data snapshots must be regenerated by a full replay.
fn migrate_err(version: u32, e: bincode::error::DecodeError) -> SnapshotError {
    SnapshotError::Codec(format!(
        "v{version} payload: {e} — pre-v4 snapshots with non-empty registries are \
         undecodable by construction (internally-tagged registry enums under bincode); \
         regenerate the snapshot with a full replay (ISA_SNAPSHOT_OUT)"
    ))
}

/// Validate that `corpus` is an append-only extension of the snapshotted
/// prefix (byte-identical first `prefix_bytes`), returning the seek offset to
/// resume from. `ISA_SNAPSHOT_SKIP_PREFIX_HASH=1` skips the hash (trusted
/// local loops only — the offset/line bookkeeping is still enforced).
///
/// # Errors
/// [`SnapshotError::PrefixMismatch`] when the prefix bytes differ.
pub fn validate_prefix(corpus: &Path, snap: &ReplaySnapshot) -> Result<u64, SnapshotError> {
    if std::env::var("ISA_SNAPSHOT_SKIP_PREFIX_HASH").as_deref() != Ok("1") {
        let got = hash_corpus_prefix(corpus, snap.prefix_bytes)?;
        if got != snap.prefix_blake3 {
            return Err(SnapshotError::PrefixMismatch {
                prefix_bytes: snap.prefix_bytes,
            });
        }
    }
    Ok(snap.prefix_bytes)
}

/// Seek `file` to the resume offset.
///
/// # Errors
/// I/O failures.
pub fn seek_to_resume(
    file: &mut std::fs::File,
    snap: &ReplaySnapshot,
) -> Result<(), SnapshotError> {
    file.seek(std::io::SeekFrom::Start(snap.prefix_bytes))?;
    Ok(())
}

#[cfg(test)]
mod header_inspect_tests {
    use super::*;

    /// Write a valid v6 snapshot HEADER (magic + version + `fp`) — enough for
    /// [`inspect_snapshot_header`], which never touches the payload.
    fn write_header(path: &Path, version: u32, fp: &[u8; 32]) {
        let mut bytes = Vec::new();
        bytes.extend_from_slice(MAGIC);
        bytes.extend_from_slice(&version.to_le_bytes());
        bytes.extend_from_slice(fp);
        std::fs::write(path, &bytes).expect("write header fixture");
    }

    #[test]
    fn test_inspect_snapshot_header_current_layout_matches() {
        let dir = std::env::temp_dir().join(format!("isa_hdr_ok_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("mk dir");
        let snap = dir.join("ok.snap");
        write_header(&snap, FORMAT_VERSION, &env_layout_fingerprint());

        let info = inspect_snapshot_header(&snap).expect("header parses");
        assert_eq!(info.version, FORMAT_VERSION);
        assert!(info.has_layout_fp, "v6+ carries a layout fingerprint");
        assert!(
            info.layout_matches,
            "a snapshot written with THIS binary's fingerprint must match"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_inspect_snapshot_header_drifted_fp_detected() {
        let dir = std::env::temp_dir().join(format!("isa_hdr_drift_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("mk dir");
        let snap = dir.join("drift.snap");
        let mut fp = env_layout_fingerprint();
        fp[0] ^= 0xff; // simulate an env-layout change
        write_header(&snap, FORMAT_VERSION, &fp);

        let info = inspect_snapshot_header(&snap).expect("header still parses");
        assert!(info.has_layout_fp);
        assert!(
            !info.layout_matches,
            "a drifted fingerprint must be reported as a mismatch"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_inspect_snapshot_header_bad_magic_errors() {
        let dir = std::env::temp_dir().join(format!("isa_hdr_magic_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("mk dir");
        let snap = dir.join("junk.snap");
        std::fs::write(&snap, b"NOTASNAP\x06\x00\x00\x00").expect("write junk");

        let err = inspect_snapshot_header(&snap).expect_err("bad magic must error");
        assert!(matches!(err, SnapshotError::Format(_)), "got {err:?}");
        let _ = std::fs::remove_dir_all(&dir);
    }
}

#[cfg(test)]
mod provenance_tests {
    use super::*;

    /// Write a MINIMAL v6 snapshot HEADER whose stored ENV-LAYOUT fingerprint is
    /// deliberately WRONG (one byte flipped from this binary's), so a load refuses
    /// with [`SnapshotError::LayoutDrift`] right after reading the fingerprint —
    /// BEFORE any payload is read (see [`load_snapshot_unfingerprinted`]). No valid
    /// payload is needed to exercise the drift path.
    fn write_drifted_header(path: &Path) {
        let mut fp = env_layout_fingerprint();
        fp[0] ^= 0xff;
        let mut bytes = Vec::new();
        bytes.extend_from_slice(MAGIC);
        bytes.extend_from_slice(&FORMAT_VERSION.to_le_bytes());
        bytes.extend_from_slice(&fp);
        std::fs::write(path, &bytes).expect("write drifted header fixture");
    }

    #[test]
    fn test_provenance_sidecar_roundtrip() {
        let dir = std::env::temp_dir().join(format!("isa_prov_rt_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("mk dir");
        let snap = dir.join("rt.snap");

        let build = BuildIdentity::new(Some("deadbeefcafef00d".to_string()), Some(1_700_000_000));
        let corpus_fp = [7u8; 32];
        let prov = SnapshotProvenance::capture(Some(&build), &corpus_fp);
        assert_eq!(prov.binary_git_sha, "deadbeefcafef00d");
        assert_eq!(prov.corpus_fingerprint, fp_hex_full(&corpus_fp));
        assert_eq!(prov.env_layout_fp, fp_hex_full(&env_layout_fingerprint()));
        assert_ne!(
            prov.binary_path, "",
            "current_exe should resolve under test"
        );

        write_provenance_sidecar(&snap, &prov).expect("write sidecar");
        // The sidecar lives at `<snap>.provenance.json`, NOT the snapshot path.
        assert_eq!(
            provenance_sidecar_path(&snap),
            dir.join("rt.snap.provenance.json")
        );
        assert!(
            provenance_sidecar_path(&snap).exists(),
            "sidecar file exists"
        );

        let read = read_provenance_sidecar(&snap).expect("sidecar reads back");
        assert_eq!(read, prov, "sidecar must round-trip byte-for-byte");
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_capture_missing_build_records_unknown_sha() {
        let prov = SnapshotProvenance::capture(None, &[0u8; 32]);
        assert_eq!(
            prov.binary_git_sha, "unknown",
            "no threaded build identity => unknown SHA (never a silent blank)"
        );
    }

    #[test]
    fn test_read_provenance_sidecar_absent_is_none() {
        let dir = std::env::temp_dir().join(format!("isa_prov_absent_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("mk dir");
        let snap = dir.join("no-sidecar.snap");
        assert!(
            read_provenance_sidecar(&snap).is_none(),
            "a missing sidecar must read back as None (back-compat)"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_layout_drift_error_includes_provenance_when_sidecar_present() {
        let dir = std::env::temp_dir().join(format!("isa_prov_drift_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("mk dir");
        let snap = dir.join("drift.snap");
        write_drifted_header(&snap);

        let build = BuildIdentity::new(Some("abc123def456aa".to_string()), Some(42));
        let prov = SnapshotProvenance::capture(Some(&build), &[3u8; 32]);
        write_provenance_sidecar(&snap, &prov).expect("write sidecar");

        match load_snapshot(&snap).err().expect("layout drift must error") {
            SnapshotError::LayoutDrift { provenance, .. } => {
                assert!(
                    provenance.contains("abc123def456aa"),
                    "drift error must name the builder SHA, got: {provenance}"
                );
                assert!(
                    provenance.contains(&prov.binary_path),
                    "drift error must name the builder binary path, got: {provenance}"
                );
                // The full rendered message carries the actionable clause too.
                let rendered = SnapshotError::LayoutDrift {
                    snapshot: "aa".to_string(),
                    loader: "bb".to_string(),
                    provenance,
                }
                .to_string();
                assert!(
                    rendered.contains("rerun with the original binary"),
                    "{rendered}"
                );
            }
            other => panic!("expected LayoutDrift with provenance, got: {other:?}"),
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_layout_drift_error_empty_provenance_without_sidecar() {
        let dir = std::env::temp_dir().join(format!("isa_prov_nodrift_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("mk dir");
        let snap = dir.join("bare-drift.snap");
        write_drifted_header(&snap);
        // No sidecar written.
        match load_snapshot(&snap).err().expect("layout drift must error") {
            SnapshotError::LayoutDrift { provenance, .. } => {
                assert!(
                    provenance.is_empty(),
                    "no sidecar => empty provenance clause (back-compat), got: {provenance}"
                );
            }
            other => panic!("expected LayoutDrift, got: {other:?}"),
        }
        let _ = std::fs::remove_dir_all(&dir);
    }
}
