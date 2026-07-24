// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean mathverse trust-receipt <verb>` — build, audit, and prove membership
//! in a Merkle **trust receipt** (P4) over a kernel-verified declaration set.
//!
//! The receipt itself is minted during verification (`per-constant-verify
//! --receipt`, or the stamp path). This command operates on the published
//! artifacts — the receipt JSON and its companion leaves manifest — to give the
//! *consumer* side of P4: anyone can independently re-derive the root (audit) or
//! prove one named theorem is in the certified set (an O(log N) Merkle path),
//! trusting only `blake3` and the published leaves.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

use clean_kernel::env::is_foundational_axiom;
use clean_kernel::Name;

use crate::cli::kv_cache::FingerprintMode;
use crate::cli::per_constant_load::per_constant_verify;
use crate::cli::{MathverseCliError, TrustReceiptCommands};
use crate::graduate::record::expr_canonical_digest;
use crate::verify::trust_receipt::{
    canonical_leaves, leaf_hash, merkle_proof, verify_membership, LeavesManifest, MerkleProof,
    TrustReceipt,
};

/// Dispatch `clean mathverse trust-receipt <verb>`.
pub(crate) fn cmd_trust_receipt(cmd: TrustReceiptCommands) -> Result<(), MathverseCliError> {
    match cmd {
        TrustReceiptCommands::Build(a) => build(a),
        TrustReceiptCommands::Verify(a) => verify(a),
        TrustReceiptCommands::Prove(a) => prove(a),
        TrustReceiptCommands::Merge(a) => merge(a),
        TrustReceiptCommands::Corpus(a) => corpus(a),
        TrustReceiptCommands::FromShards(a) => from_shards(a),
    }
}

/// `from-shards`: build a receipt directly from a stamped `.mathverse` shard dir
/// — the Mathverse-native path. Certifies exactly the constants the shards
/// stamped `KernelVerified`, reading their content + axiom closure straight from
/// the shard bytes (no re-verification, no `.olean` re-walk). The shards carry
/// each constant's type/value and its per-constant confidence, independent of any
/// verify-env elision, so this is a pure read over the persistent artifact.
/// Raw `DeclKind` byte for an axiom. Tied to the enum discriminant so it can
/// never drift: `DeclKind::Axiom == 2` (a hardcoded literal previously read `3`,
/// which is `Opaque` — that off-by-one silently dropped every real axiom from the
/// closure and forged `within_tcb: true`; caught by the P4 soundness audit).
const DECL_KIND_AXIOM: u8 = crate::types::DeclKind::Axiom as u8;

/// Kind-agnostic, name-INDEPENDENT content hash of a shard constant: a blake3
/// over `(decl_kind, level_params, type, value)`, with type/value via the de
/// Bruijn structural [`expr_canonical_digest`]. Works for EVERY kind (incl.
/// inductive families, which are not `Declaration`s), so total KernelVerified
/// coverage is achievable. The leaf binds the name separately.
fn shard_const_content_hash(f: &crate::closure_source::ShardConstFact) -> Option<[u8; 32]> {
    let mut h = blake3::Hasher::new();
    h.update(b"clean.receipt.shardconst.v1\0");
    h.update(&[f.decl_kind]);
    h.update(&(f.level_params.len() as u32).to_le_bytes());
    for lp in &f.level_params {
        h.update(lp.to_string().as_bytes());
        h.update(b"\0");
    }
    h.update(expr_canonical_digest(&f.type_).ok()?.as_bytes());
    match &f.value {
        Some(v) => {
            h.update(b"V");
            h.update(expr_canonical_digest(v).ok()?.as_bytes());
        }
        None => {
            h.update(b"N");
        }
    }
    Some(*h.finalize().as_bytes())
}

fn from_shards(a: crate::cli::TrustReceiptFromShardsArgs) -> Result<(), MathverseCliError> {
    let s = build_receipt_from_shard_dir(
        &a.shard_dir,
        a.source_id.clone(),
        a.out.as_deref(),
        a.out_leaves.as_deref(),
        a.out_provenance.as_deref(),
    )?;
    println!(
        "trust-receipt from-shards: shard_constants={} kernel_verified={} root={} leaves={} within_tcb={}",
        s.shard_constants, s.kernel_verified, s.merkle_root, s.leaf_count, s.tcb_label(),
    );
    Ok(())
}

/// Summary of a receipt built from a stamped shard directory.
pub(crate) struct ShardReceiptSummary {
    pub(crate) shard_constants: usize,
    pub(crate) kernel_verified: usize,
    pub(crate) leaf_count: usize,
    pub(crate) merkle_root: String,
    pub(crate) within_tcb: Option<bool>,
}

impl ShardReceiptSummary {
    pub(crate) fn tcb_label(&self) -> &'static str {
        match self.within_tcb {
            Some(true) => "yes",
            Some(false) => "NO",
            None => "incomplete",
        }
    }
}

/// Build a trust receipt from a stamped `.mathverse` shard directory: certify
/// every constant the shards stamped `KernelVerified`, with the transitive
/// non-foundational-axiom basis over ALL shard constants. Optionally writes the
/// receipt, the auditable leaves manifest, and a provenance record. Shared by the
/// `trust-receipt from-shards` verb and `stamp-verified --receipt` (turnkey
/// stamp+certify), so both paths mint byte-identical receipts.
pub(crate) fn build_receipt_from_shard_dir(
    shard_dir: &Path,
    source_id: Option<String>,
    out: Option<&Path>,
    out_leaves: Option<&Path>,
    out_provenance: Option<&Path>,
) -> Result<ShardReceiptSummary, MathverseCliError> {
    let facts_in = crate::closure_source::shard_dir_facts(shard_dir)
        .map_err(|e| MathverseCliError::TrustReceipt(format!("{}: {e}", shard_dir.display())))?;

    // Facts DAG over EVERY shard constant (ALL kinds — so the axiom walk can
    // traverse inductive-family type refs and reach `complete`), plus a leaf for
    // every KernelVerified constant (total coverage, not just definitional).
    let mut facts: HashMap<Name, (bool, Vec<Name>)> = HashMap::new();
    let mut kv_leaves: Vec<(String, [u8; 32])> = Vec::new();
    let mut kv_names: Vec<Name> = Vec::new();
    let shard_constants = facts_in.len();
    for f in &facts_in {
        let name = f.name.clone();
        let is_axiom = f.decl_kind == DECL_KIND_AXIOM && !is_foundational_axiom(&name);
        let mut refs: HashSet<Name> = f.type_.collect_constants();
        if let Some(v) = &f.value {
            refs.extend(v.collect_constants());
        }
        let mut refs: Vec<Name> = refs.into_iter().collect();
        refs.sort_unstable();
        facts.entry(name.clone()).or_insert((is_axiom, refs));
        if f.kernel_verified {
            if let Some(h) = shard_const_content_hash(f) {
                kv_leaves.push((name.to_string(), h));
                kv_names.push(name);
            }
        }
    }

    // Transitive non-foundational-axiom closure of the KernelVerified set over the
    // facts DAG. A referenced constant that is neither in `facts` nor a
    // foundational axiom is unresolved → the basis is not provably complete (the
    // shard dir isn't self-contained; e.g. a trusted import wasn't stamped).
    let mut visited: HashSet<Name> = HashSet::new();
    let mut work: Vec<Name> = kv_names.clone();
    let mut axioms: BTreeSet<String> = BTreeSet::new();
    let mut complete = true;
    while let Some(name) = work.pop() {
        if !visited.insert(name.clone()) {
            continue;
        }
        match facts.get(&name) {
            Some((is_axiom, refs)) => {
                if *is_axiom {
                    axioms.insert(name.to_string());
                }
                for r in refs {
                    if !visited.contains(r) {
                        work.push(r.clone());
                    }
                }
            }
            None => {
                // Not in the shard set: fine iff it is a foundational axiom /
                // Eq / quotient primitive (never a non-foundational escape).
                if !is_foundational_axiom(&name) {
                    complete = false;
                }
            }
        }
    }

    let axiom_vec: Vec<String> = axioms.into_iter().collect();
    let (receipt, ordered) = TrustReceipt::build(
        &kv_leaves,
        &axiom_vec,
        complete,
        source_id.clone(),
        env!("CARGO_PKG_VERSION"),
    );
    if let Some(p) = out {
        std::fs::write(p, serde_json::to_vec_pretty(&receipt)?)?;
    }
    if let Some(p) = out_leaves {
        let merged = LeavesManifest::new(&kv_leaves, &axiom_vec, complete, source_id.clone());
        std::fs::write(p, serde_json::to_vec_pretty(&merged)?)?;
    }
    if let Some(p) = out_provenance {
        let provenance = ShardReceiptProvenance {
            generated_by: "clean mathverse trust-receipt from-shards (P4)",
            clean_version: env!("CARGO_PKG_VERSION"),
            source_id: source_id.clone(),
            shard_dir: shard_dir.display().to_string(),
            corpus_merkle_root: receipt.merkle_root.clone(),
            leaf_count: ordered.len(),
            shard_constants,
            kernel_verified: kv_leaves.len(),
            within_tcb: receipt.within_tcb,
            axiom_basis_complete: receipt.axiom_basis_complete,
            non_foundational_axioms: receipt.axiom_closure.clone(),
        };
        std::fs::write(p, serde_json::to_vec_pretty(&provenance)?)?;
    }
    Ok(ShardReceiptSummary {
        shard_constants,
        kernel_verified: kv_leaves.len(),
        leaf_count: ordered.len(),
        merkle_root: receipt.merkle_root,
        within_tcb: receipt.within_tcb,
    })
}

/// Provenance record for a `from-shards` corpus receipt.
#[derive(Debug, Serialize)]
struct ShardReceiptProvenance {
    generated_by: &'static str,
    clean_version: &'static str,
    #[serde(skip_serializing_if = "Option::is_none")]
    source_id: Option<String>,
    shard_dir: String,
    corpus_merkle_root: String,
    leaf_count: usize,
    shard_constants: usize,
    kernel_verified: usize,
    within_tcb: Option<bool>,
    axiom_basis_complete: bool,
    non_foundational_axioms: Vec<String>,
}

fn read_json<T: serde::de::DeserializeOwned>(path: &Path) -> Result<T, MathverseCliError> {
    let bytes = std::fs::read(path)?;
    Ok(serde_json::from_slice(&bytes)?)
}

/// `build`: mint a receipt from a leaves manifest (e.g. to re-key an existing
/// leaf set under a new source id). The axiom basis is taken verbatim from the
/// manifest and marked complete iff the manifest carries a non-empty closure.
fn build(a: crate::cli::TrustReceiptBuildArgs) -> Result<(), MathverseCliError> {
    let manifest: LeavesManifest = read_json(&a.leaves)?;
    let named = manifest.to_named_leaves().ok_or_else(|| {
        MathverseCliError::TrustReceipt("leaves manifest has malformed content hashes".to_string())
    })?;
    let source_id = a.source_id.or(manifest.source_id.clone());
    let (receipt, _) = TrustReceipt::build(
        &named,
        &manifest.axiom_closure,
        manifest.axiom_basis_complete,
        source_id,
        env!("CARGO_PKG_VERSION"),
    );
    emit(&receipt, a.out.as_deref())?;
    Ok(())
}

/// `verify`: independently re-derive the receipt's root from the leaves manifest
/// and confirm every claim (root, leaf count, axiom closure, TCB verdict). Exits
/// non-zero on any mismatch — the "any skeptic can re-derive it" gate.
fn verify(a: crate::cli::TrustReceiptVerifyArgs) -> Result<(), MathverseCliError> {
    let receipt: TrustReceipt = read_json(&a.receipt)?;
    let manifest: LeavesManifest = read_json(&a.leaves)?;
    let named = manifest.to_named_leaves().ok_or_else(|| {
        MathverseCliError::TrustReceipt("leaves manifest has malformed content hashes".to_string())
    })?;
    let ok = receipt.verify_against_leaves(&named, &manifest.axiom_closure);
    println!(
        "trust-receipt verify: root={} leaves={} audit={} within_tcb={}",
        receipt.merkle_root,
        receipt.leaf_count,
        if ok { "MATCH" } else { "MISMATCH" },
        match receipt.within_tcb {
            Some(true) => "yes",
            Some(false) => "NO",
            None => "not-computed",
        },
    );
    if ok {
        Ok(())
    } else {
        Err(MathverseCliError::TrustReceipt(
            "receipt does NOT re-derive from the published leaves — audit FAILED".to_string(),
        ))
    }
}

/// `prove`: emit (and self-check) an O(log N) membership proof that `--name` is a
/// leaf under the receipt's root. Proves a named theorem is in the certified set
/// without revealing the rest.
fn prove(a: crate::cli::TrustReceiptProveArgs) -> Result<(), MathverseCliError> {
    let receipt: TrustReceipt = read_json(&a.receipt)?;
    let manifest: LeavesManifest = read_json(&a.leaves)?;
    let named = manifest.to_named_leaves().ok_or_else(|| {
        MathverseCliError::TrustReceipt("leaves manifest has malformed content hashes".to_string())
    })?;
    let (ordered, hashes) = canonical_leaves(&named);
    let root = receipt.root_bytes().ok_or_else(|| {
        MathverseCliError::TrustReceipt("receipt root is not valid hex".to_string())
    })?;

    let idx = ordered
        .iter()
        .position(|(n, _)| n == &a.name)
        .ok_or_else(|| {
            MathverseCliError::TrustReceipt(format!("`{}` is not a leaf of this receipt", a.name))
        })?;
    let (name, content_hash) = ordered[idx].clone();
    let proof: MerkleProof = merkle_proof(&hashes, idx)
        .ok_or_else(|| MathverseCliError::TrustReceipt("leaf index out of range".to_string()))?;
    let leaf = leaf_hash(&name, &content_hash);
    let verified = verify_membership(&root, &leaf, &proof);

    if let Some(p) = a.out.as_deref() {
        std::fs::write(p, serde_json::to_vec_pretty(&proof)?)?;
    }
    println!(
        "trust-receipt prove: name={} steps={} membership={} root={}",
        a.name,
        proof.path.len(),
        if verified { "PROVEN" } else { "FAILED" },
        receipt.merkle_root,
    );
    if verified {
        Ok(())
    } else {
        Err(MathverseCliError::TrustReceipt(
            "membership proof did not verify against the receipt root".to_string(),
        ))
    }
}

/// `merge`: union many per-module leaves manifests into ONE whole-corpus
/// receipt. The corpus root commits to the union of every module's
/// `(name, content_hash)` leaves (canonicalized: sorted + deduped, so a lemma
/// shared verbatim across modules collapses to one leaf); the axiom closure is
/// the union; the corpus is `complete` iff every input module is. This is the
/// composable path to `Mathlib@<sha> → root` — verify per module (in parallel),
/// then merge, no re-walking.
fn merge(a: crate::cli::TrustReceiptMergeArgs) -> Result<(), MathverseCliError> {
    let files = expand_leaves_paths(&a.leaves)?;
    if files.is_empty() {
        return Err(MathverseCliError::TrustReceipt(
            "no leaves manifests found to merge".to_string(),
        ));
    }

    let mut all_leaves: Vec<(String, [u8; 32])> = Vec::new();
    let mut axioms: BTreeSet<String> = BTreeSet::new();
    let mut complete = true;
    for f in &files {
        let m: LeavesManifest = read_json(f)?;
        let named = m.to_named_leaves().ok_or_else(|| {
            MathverseCliError::TrustReceipt(format!("{}: malformed content hashes", f.display()))
        })?;
        all_leaves.extend(named);
        axioms.extend(m.axiom_closure.iter().cloned());
        complete &= m.axiom_basis_complete;
    }
    let axiom_vec: Vec<String> = axioms.into_iter().collect();

    let (receipt, ordered) = TrustReceipt::build(
        &all_leaves,
        &axiom_vec,
        complete,
        a.source_id.clone(),
        env!("CARGO_PKG_VERSION"),
    );
    if let Some(p) = a.out.as_deref() {
        std::fs::write(p, serde_json::to_vec_pretty(&receipt)?)?;
    }
    if let Some(p) = a.out_leaves.as_deref() {
        let merged = LeavesManifest::new(&all_leaves, &axiom_vec, complete, a.source_id.clone());
        std::fs::write(p, serde_json::to_vec_pretty(&merged)?)?;
    }
    let tcb = match receipt.within_tcb {
        Some(true) => "yes",
        Some(false) => "NO",
        None => "incomplete",
    };
    println!(
        "trust-receipt merge: modules={} corpus_root={} leaves={} (deduped from {}) within_tcb={}",
        files.len(),
        receipt.merkle_root,
        ordered.len(),
        all_leaves.len(),
        tcb,
    );
    Ok(())
}

/// Expand `--leaves` inputs: a directory contributes every `*.leaves.json` /
/// `*_leaves.json` under it (recursively); a file is taken as-is.
fn expand_leaves_paths(inputs: &[PathBuf]) -> Result<Vec<PathBuf>, MathverseCliError> {
    let mut out: Vec<PathBuf> = Vec::new();
    for p in inputs {
        if p.is_dir() {
            collect_leaves_files(p, &mut out)?;
        } else if p.is_file() {
            out.push(p.clone());
        } else {
            return Err(MathverseCliError::TrustReceipt(format!(
                "{}: not a file or directory",
                p.display()
            )));
        }
    }
    out.sort();
    out.dedup();
    Ok(out)
}

fn collect_leaves_files(dir: &Path, out: &mut Vec<PathBuf>) -> Result<(), MathverseCliError> {
    for entry in std::fs::read_dir(dir)? {
        let path = entry?.path();
        if path.is_dir() {
            collect_leaves_files(&path, out)?;
        } else {
            let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
            if name.ends_with(".leaves.json") || name.ends_with("_leaves.json") {
                out.push(path);
            }
        }
    }
    Ok(())
}

/// Per-module row in the corpus provenance record.
#[derive(Debug, Serialize)]
struct CorpusModuleRow {
    module: String,
    kernel_verified: usize,
    failed: usize,
    leaves: usize,
    /// `Some(true/false)` when the module's axiom basis was computed completely;
    /// `None` if a dependency was unresolvable.
    within_tcb: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    error: Option<String>,
}

/// The corpus provenance record — the auditable `Mathlib@<sha> → root` artifact.
#[derive(Debug, Serialize)]
struct CorpusProvenance {
    generated_by: &'static str,
    clean_version: &'static str,
    #[serde(skip_serializing_if = "Option::is_none")]
    source_id: Option<String>,
    corpus_merkle_root: String,
    leaf_count: usize,
    within_tcb: Option<bool>,
    axiom_basis_complete: bool,
    non_foundational_axioms: Vec<String>,
    modules_total: usize,
    modules_ok: usize,
    /// Modules that declared no value-bearing constants (nothing to certify) —
    /// benign, do not affect completeness.
    modules_empty: usize,
    modules_errored: usize,
    total_kernel_verified: usize,
    total_failed: usize,
    modules: Vec<CorpusModuleRow>,
}

/// `corpus`: kernel-verify every value-bearing constant of every `.olean` module
/// under `--modules-dir` (`--all-declared` per module, in-process), then union
/// into ONE corpus receipt with a provenance record. Sequential + bounded memory
/// (each module's closure env drops before the next). Per-module failures are
/// recorded and skipped, never abort the run.
/// Outcome of verifying one corpus module — mirrors the three fold branches,
/// plus `Attempting`: a marker written to the checkpoint BEFORE a module is
/// verified. If a run is killed mid-module (OOM / watchdog / crash), that
/// marker is the module's last checkpoint line, so on resume the module is
/// recognized as "this aborted us last time" and SKIPPED (recorded errored) —
/// otherwise a persistently-OOMing module would loop forever, since a killed
/// process never records its own failure.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq)]
enum ModuleStatus {
    Ok,
    Empty,
    Errored,
    Attempting,
}

/// One module's persisted verification result — a checkpoint line. Stores exactly
/// what the corpus fold needs so a replayed module is indistinguishable from a
/// freshly-verified one (leaves as `(name, content_hash_hex)`).
#[derive(Debug, Clone, Serialize, Deserialize)]
struct CheckpointEntry {
    module: String,
    status: ModuleStatus,
    kernel_verified: usize,
    failed: usize,
    axiom_basis_complete: bool,
    #[serde(default)]
    axioms: Vec<String>,
    #[serde(default)]
    leaves: Vec<(String, String)>,
    #[serde(default)]
    error: Option<String>,
}

/// Verify ONE corpus module (per-constant `add_decl`, all declared constants) and
/// package the result as a [`CheckpointEntry`]. Deterministic: the same module
/// under the same closure yields the same leaves/axioms.
fn verify_one_corpus_module(
    module: &Path,
    closure_root: &Path,
    heartbeat: u32,
    module_name: &str,
) -> CheckpointEntry {
    match per_constant_verify(
        module,
        closure_root,
        &[],
        heartbeat,
        None,
        FingerprintMode::Metadata,
        true,
        true, // compute_axioms
        true, // all_declared
        // Receipts read resident values AFTER verification (leaf fingerprints +
        // the axiom walk) — the corpus path must stay eager. See per_constant_load.
        clean_kernel::env::ProofValueElision::None,
        2048,
        None, // no lazy closure lane: receipts run on the eager closure
    ) {
        Ok(r) => CheckpointEntry {
            module: module_name.to_string(),
            status: ModuleStatus::Ok,
            kernel_verified: r.kernel_verified,
            failed: r.failed,
            axiom_basis_complete: r.axiom_basis_complete,
            axioms: r.axiom_closure.clone(),
            leaves: r
                .verified_leaves
                .iter()
                .map(|(n, h)| (n.clone(), crate::verify::trust_receipt::hexcodec::encode(h)))
                .collect(),
            error: None,
        },
        Err(MathverseCliError::StampNoInput(_)) => CheckpointEntry {
            module: module_name.to_string(),
            status: ModuleStatus::Empty,
            kernel_verified: 0,
            failed: 0,
            axiom_basis_complete: true,
            axioms: Vec::new(),
            leaves: Vec::new(),
            error: Some("no value-bearing declarations (skipped)".to_string()),
        },
        Err(e) => CheckpointEntry {
            module: module_name.to_string(),
            status: ModuleStatus::Errored,
            kernel_verified: 0,
            failed: 0,
            axiom_basis_complete: false,
            axioms: Vec::new(),
            leaves: Vec::new(),
            error: Some(e.to_string()),
        },
    }
}

/// Load a JSONL checkpoint into a `module → entry` map (last line wins). Missing
/// file or malformed lines are tolerated (best-effort resume).
fn load_checkpoint(path: &Path) -> HashMap<String, CheckpointEntry> {
    let mut map: HashMap<String, CheckpointEntry> = HashMap::new();
    if let Ok(content) = std::fs::read_to_string(path) {
        for line in content.lines() {
            let line = line.trim();
            if line.is_empty() {
                continue;
            }
            if let Ok(e) = serde_json::from_str::<CheckpointEntry>(line) {
                map.insert(e.module.clone(), e);
            }
        }
    }
    map
}

/// Append one module's result as a JSONL line — O(1), so an 8169-module run
/// checkpoints without rewriting a growing file each step.
fn append_checkpoint(path: &Path, entry: &CheckpointEntry) {
    use std::io::Write;
    if let Ok(mut f) = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)
    {
        if let Ok(line) = serde_json::to_string(entry) {
            let _ = writeln!(f, "{line}");
        }
    }
}

/// Decode a checkpoint leaf's hex content-hash back to bytes.
fn decode_leaf_hash(hex: &str) -> Option<[u8; 32]> {
    crate::verify::trust_receipt::hexcodec::decode(hex)?
        .try_into()
        .ok()
}

fn corpus(a: crate::cli::TrustReceiptCorpusArgs) -> Result<(), MathverseCliError> {
    let mut modules: Vec<PathBuf> = Vec::new();
    collect_olean_modules(&a.modules_dir, &mut modules)?;
    modules.sort();
    if a.limit > 0 && modules.len() > a.limit {
        modules.truncate(a.limit);
    }
    if modules.is_empty() {
        return Err(MathverseCliError::TrustReceipt(format!(
            "{}: no .olean modules found",
            a.modules_dir.display()
        )));
    }

    // Resume: replay any modules already recorded in the checkpoint instead of
    // re-verifying them. Keyed by module name; last line wins.
    let done: HashMap<String, CheckpointEntry> = match a.checkpoint.as_deref() {
        Some(p) => load_checkpoint(p),
        None => HashMap::new(),
    };
    if !done.is_empty() {
        eprintln!(
            "trust-receipt corpus: resuming — {} module(s) replayed from checkpoint",
            done.len()
        );
    }

    let mut all_leaves: Vec<(String, [u8; 32])> = Vec::new();
    let mut axioms: BTreeSet<String> = BTreeSet::new();
    let mut complete = true;
    let mut rows: Vec<CorpusModuleRow> = Vec::new();
    let (mut modules_ok, mut modules_empty, mut modules_errored) = (0usize, 0usize, 0usize);
    let (mut total_kv, mut total_failed) = (0usize, 0usize);

    for (i, module) in modules.iter().enumerate() {
        let module_name = module
            .strip_prefix(&a.closure_root)
            .unwrap_or(module)
            .display()
            .to_string();

        // Verify the module, OR replay it from the checkpoint if already recorded.
        let entry = match done.get(&module_name) {
            // A module whose last checkpoint line is `Attempting` KILLED a prior run
            // mid-verification (OOM / watchdog / crash — a killed process can't
            // record its own failure). Skip it so the corpus makes progress instead
            // of dying on it again; record it errored (honest: basis not complete).
            Some(cached) if cached.status == ModuleStatus::Attempting => {
                eprintln!(
                    "trust-receipt corpus: [{}/{}] {module_name} — SKIPPED (aborted a prior run; likely OOM/timeout)",
                    i + 1,
                    modules.len()
                );
                let e = CheckpointEntry {
                    module: module_name.clone(),
                    status: ModuleStatus::Errored,
                    kernel_verified: 0,
                    failed: 0,
                    axiom_basis_complete: false,
                    axioms: Vec::new(),
                    leaves: Vec::new(),
                    error: Some(
                        "aborted on a prior attempt (likely OOM/timeout) — skipped".to_string(),
                    ),
                };
                if let Some(p) = a.checkpoint.as_deref() {
                    append_checkpoint(p, &e);
                }
                e
            }
            Some(cached) => {
                eprintln!(
                    "trust-receipt corpus: [{}/{}] {module_name} (cached)",
                    i + 1,
                    modules.len()
                );
                cached.clone()
            }
            None => {
                eprintln!(
                    "trust-receipt corpus: [{}/{}] verifying {module_name}",
                    i + 1,
                    modules.len()
                );
                // Write an ATTEMPTING marker BEFORE verifying: if this module kills
                // the process, its last line stays `Attempting` and the next resume
                // skips it (above). On success the result line overwrites it
                // (load is last-line-wins).
                if let Some(p) = a.checkpoint.as_deref() {
                    append_checkpoint(
                        p,
                        &CheckpointEntry {
                            module: module_name.clone(),
                            status: ModuleStatus::Attempting,
                            kernel_verified: 0,
                            failed: 0,
                            axiom_basis_complete: false,
                            axioms: Vec::new(),
                            leaves: Vec::new(),
                            error: None,
                        },
                    );
                }
                let e =
                    verify_one_corpus_module(module, &a.closure_root, a.heartbeat, &module_name);
                if let Some(p) = a.checkpoint.as_deref() {
                    append_checkpoint(p, &e);
                }
                e
            }
        };

        // Fold the entry (cached or fresh) into the accumulators identically.
        match entry.status {
            ModuleStatus::Ok => {
                modules_ok += 1;
                total_kv += entry.kernel_verified;
                total_failed += entry.failed;
                complete &= entry.axiom_basis_complete;
                axioms.extend(entry.axioms.iter().cloned());
                let within = if entry.axiom_basis_complete {
                    Some(entry.axioms.is_empty())
                } else {
                    None
                };
                rows.push(CorpusModuleRow {
                    module: module_name,
                    kernel_verified: entry.kernel_verified,
                    failed: entry.failed,
                    leaves: entry.leaves.len(),
                    within_tcb: within,
                    error: None,
                });
                for (name, hex) in &entry.leaves {
                    if let Some(h) = decode_leaf_hash(hex) {
                        all_leaves.push((name.clone(), h));
                    }
                }
            }
            // A module that declares NO value-bearing constants (all instances /
            // inductive families / axioms) is BENIGN: it contributes no leaves and
            // must NOT break corpus completeness. Every OTHER error (unopenable
            // olean, unresolved closure) is real and marks the basis not-complete.
            ModuleStatus::Empty => {
                modules_empty += 1;
                rows.push(CorpusModuleRow {
                    module: module_name,
                    kernel_verified: 0,
                    failed: 0,
                    leaves: 0,
                    within_tcb: None,
                    error: Some("no value-bearing declarations (skipped)".to_string()),
                });
            }
            // `Attempting` never reaches here (resolved to a terminal status above);
            // fold it as an error defensively so a stray marker marks incomplete
            // rather than being silently dropped.
            ModuleStatus::Errored | ModuleStatus::Attempting => {
                modules_errored += 1;
                complete = false;
                rows.push(CorpusModuleRow {
                    module: module_name,
                    kernel_verified: 0,
                    failed: 0,
                    leaves: 0,
                    within_tcb: None,
                    error: entry.error.clone(),
                });
            }
        }
    }

    let axiom_vec: Vec<String> = axioms.into_iter().collect();
    let (receipt, ordered) = TrustReceipt::build(
        &all_leaves,
        &axiom_vec,
        complete,
        a.source_id.clone(),
        env!("CARGO_PKG_VERSION"),
    );

    if let Some(p) = a.out.as_deref() {
        std::fs::write(p, serde_json::to_vec_pretty(&receipt)?)?;
    }
    if let Some(p) = a.out_leaves.as_deref() {
        let merged = LeavesManifest::new(&all_leaves, &axiom_vec, complete, a.source_id.clone());
        std::fs::write(p, serde_json::to_vec_pretty(&merged)?)?;
    }
    let provenance = CorpusProvenance {
        generated_by: "clean mathverse trust-receipt corpus (P4)",
        clean_version: env!("CARGO_PKG_VERSION"),
        source_id: a.source_id.clone(),
        corpus_merkle_root: receipt.merkle_root.clone(),
        leaf_count: ordered.len(),
        within_tcb: receipt.within_tcb,
        axiom_basis_complete: receipt.axiom_basis_complete,
        non_foundational_axioms: receipt.axiom_closure.clone(),
        modules_total: modules.len(),
        modules_ok,
        modules_empty,
        modules_errored,
        total_kernel_verified: total_kv,
        total_failed,
        modules: rows,
    };
    if let Some(p) = a.out_provenance.as_deref() {
        std::fs::write(p, serde_json::to_vec_pretty(&provenance)?)?;
    }

    let tcb = match receipt.within_tcb {
        Some(true) => "yes",
        Some(false) => "NO",
        None => "incomplete",
    };
    println!(
        "trust-receipt corpus: modules={} (ok={} empty={} errored={}) kernel_verified={} failed={} \
         corpus_root={} leaves={} within_tcb={}",
        modules.len(),
        modules_ok,
        modules_empty,
        modules_errored,
        total_kv,
        total_failed,
        receipt.merkle_root,
        ordered.len(),
        tcb,
    );
    Ok(())
}

/// Recursively collect base `.olean` module files under `dir`, skipping the
/// `.olean.private` / `.olean.server` / `.olean.hash` companions.
fn collect_olean_modules(dir: &Path, out: &mut Vec<PathBuf>) -> Result<(), MathverseCliError> {
    for entry in std::fs::read_dir(dir)? {
        let path = entry?.path();
        if path.is_dir() {
            collect_olean_modules(&path, out)?;
        } else if path.extension().is_some_and(|e| e == "olean") {
            // `x.olean` has extension "olean"; `x.olean.private` has extension
            // "private", so the extension check already excludes companions.
            out.push(path);
        }
    }
    Ok(())
}

fn emit(receipt: &TrustReceipt, out: Option<&Path>) -> Result<(), MathverseCliError> {
    let bytes = serde_json::to_vec_pretty(receipt)?;
    if let Some(p) = out {
        std::fs::write(p, &bytes)?;
    }
    println!(
        "trust-receipt build: root={} leaves={} axiom_basis_complete={}",
        receipt.merkle_root, receipt.leaf_count, receipt.axiom_basis_complete
    );
    Ok(())
}

#[cfg(test)]
mod axiom_classification_tests {
    use super::*;
    use crate::export::kernel_export::KernelShardBuilder;
    use clean_kernel::expr::Expr;
    use clean_kernel::level::Level;
    use clean_kernel::name::Name;
    use clean_kernel::Declaration;

    // `theorem N : Prop := <axiom>` — the proof term references `axiom_name`, so
    // this theorem genuinely rests on that axiom.
    fn thm_on_axiom(name: &str, axiom_name: &str) -> Declaration {
        Declaration::Theorem {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::sort(Level::zero()),
            value: Expr::const_(Name::from_string(axiom_name), vec![]),
        }
    }

    // `axiom N : Prop` — a real `DeclKind::Axiom` (byte 2). Its NAME decides
    // whether it counts against the 3-axiom TCB claim.
    fn axiom_named(name: &str) -> Declaration {
        Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::sort(Level::zero()),
        }
    }

    /// The axiom-kind discriminant must equal `DeclKind::Axiom` (2), NOT the old
    /// hardcoded `3` (which is `Opaque`). Guards the off-by-one the P4 soundness
    /// audit caught: with `DECL_KIND_AXIOM == 3`, real axioms (byte 2) were never
    /// classified, so a non-foundational axiom silently dropped from the closure
    /// and `within_tcb` was forged `true`.
    #[test]
    fn decl_kind_axiom_discriminant_is_axiom_not_opaque() {
        assert_eq!(DECL_KIND_AXIOM, crate::types::DeclKind::Axiom as u8);
        assert_eq!(DECL_KIND_AXIOM, 2);
        assert_ne!(DECL_KIND_AXIOM, crate::types::DeclKind::Opaque as u8);
    }

    /// S1 REGRESSION: a KernelVerified theorem that rests on a NON-foundational
    /// real axiom (`DeclKind::Axiom`, byte 2) must be flagged — the axiom appears
    /// in the closure and `within_tcb` is `Some(false)`. Pre-fix (DECL_KIND_AXIOM
    /// == 3) this returned `Some(true)` with an empty closure — the forgery.
    #[test]
    fn nonfoundational_axiom_dependency_is_flagged_not_within_tcb() {
        let mut b = KernelShardBuilder::new();
        b.add_declaration(&thm_on_axiom("N", "Evil"), &[]).unwrap();
        b.add_declaration(&axiom_named("Evil"), &[]).unwrap();
        let dir = tempfile::tempdir().unwrap();
        b.write_to_file(dir.path().join("m.mathverse")).unwrap();

        let s = build_receipt_from_shard_dir(dir.path(), None, None, None, None).unwrap();
        assert_eq!(
            s.within_tcb,
            Some(false),
            "a theorem resting on a non-foundational axiom is NOT within the 3-axiom TCB"
        );
    }

    /// A KernelVerified theorem resting only on a FOUNDATIONAL axiom (one of
    /// {propext, Quot.sound, Classical.choice}) IS within-TCB: the axiom is a real
    /// `DeclKind::Axiom` but `is_foundational_axiom` filters it, so the closure of
    /// non-foundational axioms is empty and `within_tcb` is `Some(true)`.
    #[test]
    fn foundational_axiom_dependency_stays_within_tcb() {
        let mut b = KernelShardBuilder::new();
        b.add_declaration(&thm_on_axiom("N", "propext"), &[])
            .unwrap();
        b.add_declaration(&axiom_named("propext"), &[]).unwrap();
        let dir = tempfile::tempdir().unwrap();
        b.write_to_file(dir.path().join("m.mathverse")).unwrap();

        let s = build_receipt_from_shard_dir(dir.path(), None, None, None, None).unwrap();
        assert_eq!(
            s.within_tcb,
            Some(true),
            "resting only on a foundational (TCB) axiom is within-TCB"
        );
    }
}

#[cfg(test)]
mod checkpoint_tests {
    use super::*;

    /// A leaf's content hash survives the checkpoint hex round-trip exactly — the
    /// bytes replayed from a checkpoint equal the freshly-computed bytes, so a
    /// resumed module contributes an IDENTICAL leaf (hence identical root).
    #[test]
    fn leaf_hash_hex_round_trips() {
        let h: [u8; 32] = std::array::from_fn(|i| (i as u8).wrapping_mul(7).wrapping_add(1));
        let hex = crate::verify::trust_receipt::hexcodec::encode(&h);
        assert_eq!(decode_leaf_hash(&hex), Some(h));
        assert_eq!(decode_leaf_hash("not-hex"), None);
    }

    /// A checkpoint JSONL round-trips: append two module entries, load them back,
    /// and the map preserves status/counts/leaves. Last line wins on a dup key.
    #[test]
    fn checkpoint_jsonl_round_trips_and_last_wins() {
        let dir = tempfile::tempdir().unwrap();
        let cp = dir.path().join("cp.jsonl");

        let a = CheckpointEntry {
            module: "Mathlib/A".to_string(),
            status: ModuleStatus::Ok,
            kernel_verified: 3,
            failed: 0,
            axiom_basis_complete: true,
            axioms: vec![],
            leaves: vec![("A.foo".to_string(), "00ff".repeat(16))],
            error: None,
        };
        let b_empty = CheckpointEntry {
            module: "Mathlib/B".to_string(),
            status: ModuleStatus::Empty,
            kernel_verified: 0,
            failed: 0,
            axiom_basis_complete: true,
            axioms: vec![],
            leaves: vec![],
            error: Some("no value-bearing declarations (skipped)".to_string()),
        };
        // A stale first write for A that a later line must override.
        let a_stale = CheckpointEntry {
            kernel_verified: 999,
            ..a.clone()
        };
        append_checkpoint(&cp, &a_stale);
        append_checkpoint(&cp, &b_empty);
        append_checkpoint(&cp, &a); // last A wins

        let map = load_checkpoint(&cp);
        assert_eq!(map.len(), 2, "two distinct modules");
        assert_eq!(
            map["Mathlib/A"].kernel_verified, 3,
            "last line wins over stale"
        );
        assert_eq!(map["Mathlib/A"].leaves.len(), 1);
        assert_eq!(map["Mathlib/B"].status, ModuleStatus::Empty);
    }

    /// A missing checkpoint file loads as empty (a fresh run), not an error.
    #[test]
    fn missing_checkpoint_is_empty() {
        let dir = tempfile::tempdir().unwrap();
        assert!(load_checkpoint(&dir.path().join("nope.jsonl")).is_empty());
    }

    /// The attempt-marker protocol: an `Attempting` line written before a module
    /// verifies survives as its last line iff the run was killed mid-module (so a
    /// resume can skip it); a successful result line overwrites it (last-wins).
    #[test]
    fn attempting_marker_survives_a_kill_but_is_overwritten_by_success() {
        let dir = tempfile::tempdir().unwrap();
        let cp = dir.path().join("cp.jsonl");
        let marker = |m: &str, s: ModuleStatus| CheckpointEntry {
            module: m.to_string(),
            status: s,
            kernel_verified: 0,
            failed: 0,
            axiom_basis_complete: false,
            axioms: vec![],
            leaves: vec![],
            error: None,
        };

        // Module "killed": only an Attempting line (process died before a result).
        append_checkpoint(&cp, &marker("Mathlib/Killed", ModuleStatus::Attempting));
        // Module "done": Attempting THEN a terminal result → result wins.
        append_checkpoint(&cp, &marker("Mathlib/Done", ModuleStatus::Attempting));
        append_checkpoint(&cp, &marker("Mathlib/Done", ModuleStatus::Ok));

        let map = load_checkpoint(&cp);
        assert_eq!(
            map["Mathlib/Killed"].status,
            ModuleStatus::Attempting,
            "a killer module's last line stays Attempting → resume skips it"
        );
        assert_eq!(
            map["Mathlib/Done"].status,
            ModuleStatus::Ok,
            "a completed module's result overwrites its Attempting marker"
        );
    }
}
