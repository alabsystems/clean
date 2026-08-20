// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Semantic module diff.
//!
//! This module computes the difference between two `Module` values at the
//! structural level, ignoring cosmetic differences that arise from how the
//! producer happened to arena-allocate identifiers.
//!
//! # What is ignored
//!
//! * `FuncId`, `BlockId`, `ValueId`, `StructId`, `EnumId`, `RecordId`,
//!   `ClosureTyId`, `FuncTyId`, `TyId` numbering. Two modules that are
//!   identical up to a renumbering of these ids are considered equal.
//! * Declaration order of functions/structs/enums/records/closure types
//!   in the module.
//! * Claim-style debug metadata: `SourceSpan` and lexical-scope indices on
//!   instruction nodes, plus function `value_names` and scope trees. These do
//!   not affect execution or proof authority. `source_provenance` is explicitly
//!   excluded from this list: it is proof-relevant function metadata.
//!
//! # What is compared
//!
//! * The set of function names (added / removed).
//! * Per matched function: block shape (number of blocks reachable from
//!   entry), block parameter types, and instruction bodies positionally
//!   after block alignment.
//! * Per matched instruction: the `Inst` variant and all type/constant/
//!   literal payloads it carries, compared via a structural fingerprint
//!   that resolves id references through each module's own tables.
//! * `ProofAnnotation` sets attached to each function and each instruction
//!   node (unless `--ignore-proofs` is set).
//! * Module proof state: `proof_obligations` (matched by claim — kind, scope
//!   function name, description, formula, and embedded source identity — with `status` reported as a
//!   change), `proof_certificates` (matched by obligation claim + prover +
//!   evidence), and per-instruction `proof_context` (its `assumes`/`establishes`
//!   obligation references resolved to claim keys). All unless `--ignore-proofs`
//!   is set, which suppresses every proof comparison and preserves the older
//!   proof-insensitive behavior.
//!
//! # Alignment algorithm
//!
//! 1. Functions are matched by name. Added/removed names are reported.
//! 2. Within a matched function pair, blocks are walked in deterministic
//!    DFS preorder starting from each function's `entry` block, following
//!    successor edges in the order they appear in the terminator. Any
//!    blocks not reachable from entry are appended in block-id order so
//!    dead blocks still contribute to the diff.
//! 3. The i-th block visited in A is matched with the i-th block visited
//!    in B. If the walks produce different counts, the trailing blocks
//!    are reported as `Added` / `Removed`.
//! 4. Within a matched block pair, instructions are compared positionally.
//!    Because the walk defines a canonical block numbering on each side,
//!    operand `ValueId`s are remapped through a `value_map` keyed by
//!    each side's SSA layout so that cross-module fingerprints line up
//!    after renumbering.
//!
//! The matcher is deterministic: it never re-orders on its own, and it
//! never performs a best-match search. Consumers get stable output across
//! runs.
//!
//! # Exit-code contract (for the `trust-ir-diff` CLI)
//!
//! * `0` — the two modules are structurally isomorphic (empty `Diff`).
//! * `1` — at least one structural difference was found.
//! * `2` — parse or validation error (the CLI, not this module, maps errors
//!   to this code; this module never parses).
//!
//! # Limitations (non-goals)
//!
//! * No attempt is made to decide semantic equivalence. Two functions that
//!   compute the same IR program via different instruction shapes will be
//!   reported as different. That is the verifier's job, not the diff tool's.
//! * No three-way merge is produced.

use crate::{
    AttrEntry, AttrValue, Block, Function, Module,
    constant::Constant,
    dialect::DialectInst,
    inst::{BindingFrameDef, BindingSlot, Inst, SwitchCase},
    node::InstrNode,
    proof::{
        Divergence, ProofAnnotation, ProofCertificate, ProofContext, ProofEvidence,
        ProofObligation, write_proof_obligation_source_identity_stable,
    },
    ty::{
        ClosureTy, EnumDef, EnumVariant, FatPtrKind, FieldDef, FuncTy, RecordDef, SetRepr,
        StructDef, Ty,
    },
    value::{
        BlockId, ClosureTyId, EnumId, FuncId, FuncTyId, ProofId, ProofTag, RecordId, StructId,
        TyId, ValueId,
    },
};
use core::fmt::Write as _;
use std::collections::HashMap;

// -----------------------------------------------------------------------------
// Public diff types
// -----------------------------------------------------------------------------

/// Options controlling diff behavior.
#[derive(Debug, Clone, Copy, Default)]
pub struct DiffOptions {
    /// If true, `ProofAnnotation`s on functions and instruction nodes are
    /// not compared. Two modules that differ only in their proof coverage
    /// are then reported as equal.
    pub ignore_proofs: bool,
}

/// Result of comparing two modules.
#[derive(Debug, Clone, PartialEq)]
pub struct Diff {
    pub module_name_a: String,
    pub module_name_b: String,
    pub changes: Vec<FuncChange>,
    /// Module-level proof-state changes: differences in `proof_obligations`
    /// and `proof_certificates`. Empty when `ignore_proofs` is set or when
    /// the proof state matches. Per-instruction proof state (`proofs` and
    /// `proof_context`) is reported inside `changes` via `InstrChange`.
    pub proof_state_changes: Vec<ProofStateChange>,
}

impl Diff {
    /// Returns `true` when there are no recorded differences.
    pub fn is_empty(&self) -> bool {
        self.changes.is_empty() && self.proof_state_changes.is_empty()
    }

    /// Exit code for CLI use: 0 if isomorphic, 1 if different.
    ///
    /// Parse/validation errors are the CLI's concern and use exit code 2.
    pub fn exit_code(&self) -> i32 {
        if self.is_empty() { 0 } else { 1 }
    }
}

/// A function-level change.
#[derive(Debug, Clone, PartialEq)]
pub enum FuncChange {
    /// Function name present in module B but not in module A.
    Added { name: String },
    /// Function name present in module A but not in module B.
    Removed { name: String },
    /// Function exists on both sides but their bodies differ.
    Changed {
        name: String,
        /// Changes in the function's own `proofs` vector. Empty when
        /// `ignore_proofs` is set or when proofs match.
        proof_changes: Vec<ProofChange>,
        /// Changes at the block level.
        block_changes: Vec<BlockChange>,
        /// Function-metadata changes (producer and semantic source provenance).
        /// NOT gated by `ignore_proofs` — provenance is not proof coverage.
        meta_changes: Vec<MetaChange>,
    },
}

/// A function-metadata change on a matched function (non-proof, non-body):
/// currently the producer tag and semantic source-provenance carrier.
#[derive(Debug, Clone, PartialEq)]
pub struct MetaChange {
    /// Which metadata field changed (e.g. `"producer"`).
    pub field: String,
    /// Rendered A-side value; `"-"` when absent on that side.
    pub before: String,
    /// Rendered B-side value; `"-"` when absent on that side.
    pub after: String,
}

/// A block-level change within a matched function.
#[derive(Debug, Clone, PartialEq)]
pub enum BlockChange {
    /// The i-th block visited in B has no counterpart in A.
    /// `visit` is the DFS visit index (0 = entry).
    Added { visit: usize },
    /// The i-th block visited in A has no counterpart in B.
    Removed { visit: usize },
    /// Block structure differs (parameter count or parameter types).
    StructureDiffers { visit: usize, detail: String },
    /// Block bodies differ.
    InstrDiff {
        visit: usize,
        instr_changes: Vec<InstrChange>,
    },
}

/// An instruction-level change within a matched block.
#[derive(Debug, Clone, PartialEq)]
pub enum InstrChange {
    /// Instruction appears in B at this index but not in A.
    Added { index: usize, summary: String },
    /// Instruction appears in A at this index but not in B.
    Removed { index: usize, summary: String },
    /// Instructions at this index differ. `before` / `after` are one-line
    /// summaries suitable for unified-diff output.
    Replaced {
        index: usize,
        before: String,
        after: String,
    },
}

/// A proof-annotation-level change on a function or instruction node.
#[derive(Debug, Clone, PartialEq)]
pub enum ProofChange {
    Added { name: String },
    Removed { name: String },
}

/// A module-level proof-state change.
///
/// Obligations and certificates are matched across modules by a structural
/// fingerprint that ignores the arena `ProofId` numbering (consistent with
/// the rest of the diff), so renumbering a module's proof table alone never
/// surfaces here. An obligation is keyed by its *claim* — kind, formula,
/// description, and (function-name-resolved) scope — and its `status` is the
/// mutable field that produces a `ObligationStatusChanged` when it differs.
#[derive(Debug, Clone, PartialEq)]
pub enum ProofStateChange {
    /// An obligation present in B but not in A. `obligation` is the matched
    /// claim key; `status` is its status on the B side.
    ObligationAdded { obligation: String, status: String },
    /// An obligation present in A but not in B. `status` is its A-side status.
    ObligationRemoved { obligation: String, status: String },
    /// An obligation present on both sides whose status differs.
    ObligationStatusChanged {
        obligation: String,
        before: String,
        after: String,
    },
    /// A certificate present in B but not in A.
    CertificateAdded { certificate: String },
    /// A certificate present in A but not in B.
    CertificateRemoved { certificate: String },
}

// -----------------------------------------------------------------------------
// Public API
// -----------------------------------------------------------------------------

/// Diff two modules with default options.
pub fn diff(a: &Module, b: &Module) -> Diff {
    diff_with(a, b, DiffOptions::default())
}

/// Diff two modules with explicit options.
pub fn diff_with(a: &Module, b: &Module, opts: DiffOptions) -> Diff {
    let mut changes = Vec::new();

    // Build name-indexed maps of functions on each side.
    let mut a_fns: HashMap<&str, &Function> = HashMap::new();
    for f in &a.functions {
        a_fns.insert(f.name.as_str(), f);
    }
    let mut b_fns: HashMap<&str, &Function> = HashMap::new();
    for f in &b.functions {
        b_fns.insert(f.name.as_str(), f);
    }

    // Collect the union of names deterministically.
    let mut names: Vec<&str> = a_fns.keys().copied().collect();
    for k in b_fns.keys() {
        if !a_fns.contains_key(*k) {
            names.push(*k);
        }
    }
    names.sort();

    for name in names {
        let fa = a_fns.get(name).copied();
        let fb = b_fns.get(name).copied();
        match (fa, fb) {
            (Some(_), None) => changes.push(FuncChange::Removed {
                name: name.to_string(),
            }),
            (None, Some(_)) => changes.push(FuncChange::Added {
                name: name.to_string(),
            }),
            (Some(fa), Some(fb)) => {
                let mut proof_changes = if opts.ignore_proofs {
                    Vec::new()
                } else {
                    proof_diff(&fa.proofs, &fb.proofs)
                };
                // The separate-compilation contract is proof-ish: a changed
                // `requires`/`ensures`/`params`/`proved` is reported through the
                // proof channel (already gated by `ignore_proofs` and already
                // promoting the function to `Changed`).
                if !opts.ignore_proofs {
                    let sa = summary_fp(fa.summary.as_ref());
                    let sb = summary_fp(fb.summary.as_ref());
                    if sa != sb {
                        proof_changes.push(ProofChange::Removed {
                            name: format!("summary {sa}"),
                        });
                        proof_changes.push(ProofChange::Added {
                            name: format!("summary {sb}"),
                        });
                    }
                }
                // Producer provenance (v23) is function metadata, not proof
                // coverage: a producer flip is reported even under
                // `ignore_proofs`.
                let mut meta_changes = Vec::new();
                if fa.producer != fb.producer {
                    meta_changes.push(MetaChange {
                        field: "producer".to_string(),
                        before: producer_fp(fa.producer.as_ref()),
                        after: producer_fp(fb.producer.as_ref()),
                    });
                }
                if fa.source_provenance != fb.source_provenance {
                    meta_changes.push(MetaChange {
                        field: "source_provenance".to_string(),
                        before: source_provenance_fp(fa.source_provenance.as_ref()),
                        after: source_provenance_fp(fb.source_provenance.as_ref()),
                    });
                }
                let block_changes = diff_function(a, b, fa, fb, opts);
                if !proof_changes.is_empty()
                    || !block_changes.is_empty()
                    || !meta_changes.is_empty()
                {
                    changes.push(FuncChange::Changed {
                        name: name.to_string(),
                        proof_changes,
                        block_changes,
                        meta_changes,
                    });
                }
            }
            (None, None) => unreachable!(),
        }
    }

    let proof_state_changes = if opts.ignore_proofs {
        Vec::new()
    } else {
        proof_state_diff(a, b)
    };

    Diff {
        module_name_a: a.name.clone(),
        module_name_b: b.name.clone(),
        changes,
        proof_state_changes,
    }
}

// -----------------------------------------------------------------------------
// Function-level diff
// -----------------------------------------------------------------------------

fn diff_function(
    ma: &Module,
    mb: &Module,
    fa: &Function,
    fb: &Function,
    opts: DiffOptions,
) -> Vec<BlockChange> {
    let walk_a = walk_blocks(fa);
    let walk_b = walk_blocks(fb);

    // Build a_order[block_id] = visit_index and the ValueId renumber map.
    // The value map assigns each ValueId defined in the function (both
    // block params and instruction results) a canonical index based on
    // DFS walk order.
    let va_map = build_value_map(fa, &walk_a);
    let vb_map = build_value_map(fb, &walk_b);

    // Precompute canonical block numbers for successor remapping.
    let ba_map: HashMap<BlockId, u32> = walk_a
        .iter()
        .enumerate()
        .map(|(i, &bid)| (bid, i as u32))
        .collect();
    let bb_map: HashMap<BlockId, u32> = walk_b
        .iter()
        .enumerate()
        .map(|(i, &bid)| (bid, i as u32))
        .collect();

    let mut changes = Vec::new();
    let n = walk_a.len().max(walk_b.len());
    for i in 0..n {
        match (walk_a.get(i), walk_b.get(i)) {
            (Some(&ba), Some(&bb)) => {
                let blk_a = fa.blocks.iter().find(|b| b.id == ba).expect("walk id");
                let blk_b = fb.blocks.iter().find(|b| b.id == bb).expect("walk id");

                // Compare block parameter types (number + fingerprint).
                if blk_a.params.len() != blk_b.params.len() {
                    changes.push(BlockChange::StructureDiffers {
                        visit: i,
                        detail: format!(
                            "block param count: {} vs {}",
                            blk_a.params.len(),
                            blk_b.params.len()
                        ),
                    });
                    continue;
                }
                let mut param_mismatch = None;
                for (pi, ((_, ta), (_, tb))) in
                    blk_a.params.iter().zip(blk_b.params.iter()).enumerate()
                {
                    if fp_ty(ma, ta) != fp_ty(mb, tb) {
                        param_mismatch = Some(format!(
                            "block param {} type: {} vs {}",
                            pi,
                            render_ty(ma, ta),
                            render_ty(mb, tb)
                        ));
                        break;
                    }
                }
                if let Some(detail) = param_mismatch {
                    changes.push(BlockChange::StructureDiffers { visit: i, detail });
                    continue;
                }

                let instr_changes = diff_block_body(
                    ma, mb, blk_a, blk_b, &va_map, &vb_map, &ba_map, &bb_map, opts,
                );
                if !instr_changes.is_empty() {
                    changes.push(BlockChange::InstrDiff {
                        visit: i,
                        instr_changes,
                    });
                }
            }
            (Some(_), None) => changes.push(BlockChange::Removed { visit: i }),
            (None, Some(_)) => changes.push(BlockChange::Added { visit: i }),
            (None, None) => unreachable!(),
        }
    }
    changes
}

/// DFS preorder walk of reachable blocks from entry, with unreachable
/// blocks appended in block-id order.
fn walk_blocks(f: &Function) -> Vec<BlockId> {
    let by_id: HashMap<BlockId, &Block> = f.blocks.iter().map(|b| (b.id, b)).collect();
    let mut visited: std::collections::HashSet<BlockId> = std::collections::HashSet::new();
    let mut order: Vec<BlockId> = Vec::new();
    let mut stack: Vec<BlockId> = Vec::new();
    if by_id.contains_key(&f.entry) {
        stack.push(f.entry);
    }
    while let Some(bid) = stack.pop() {
        if !visited.insert(bid) {
            continue;
        }
        order.push(bid);
        let blk = match by_id.get(&bid) {
            Some(b) => b,
            None => continue,
        };
        let succs = block_successors(blk);
        // Push in reverse so first successor is visited first on pop.
        for s in succs.iter().rev() {
            if !visited.contains(s) && by_id.contains_key(s) {
                stack.push(*s);
            }
        }
    }
    // Append any unreachable blocks in id order for deterministic output.
    let mut leftover: Vec<BlockId> = f
        .blocks
        .iter()
        .map(|b| b.id)
        .filter(|bid| !visited.contains(bid))
        .collect();
    leftover.sort();
    order.extend(leftover);
    order
}

fn block_successors(blk: &Block) -> Vec<BlockId> {
    let Some(term) = blk.body.last() else {
        return Vec::new();
    };
    match &term.inst {
        Inst::Br { target, .. } => vec![*target],
        Inst::CondBr {
            then_target,
            else_target,
            ..
        } => vec![*then_target, *else_target],
        Inst::Switch { default, cases, .. } => {
            let mut v: Vec<BlockId> = cases.iter().map(|c| c.target).collect();
            v.push(*default);
            v
        }
        // An invoke branches to its normal continuation or its landing pad.
        Inst::Invoke {
            normal_dest,
            unwind_dest,
            ..
        } => vec![*normal_dest, *unwind_dest],
        _ => Vec::new(),
    }
}

/// Build a canonical mapping from ValueId to a u32 index.
///
/// The index is the order in which the value is encountered during the
/// DFS walk. Block params come first in each block (in declared order),
/// then instruction results in order. The same walk is used on both
/// sides so that operand references, which are compared via this map,
/// line up across modules after SSA renumbering.
fn build_value_map(f: &Function, walk: &[BlockId]) -> HashMap<ValueId, u32> {
    let mut m = HashMap::new();
    let mut next: u32 = 0;
    let by_id: HashMap<BlockId, &Block> = f.blocks.iter().map(|b| (b.id, b)).collect();
    for bid in walk {
        let Some(blk) = by_id.get(bid) else { continue };
        for (v, _) in &blk.params {
            m.entry(*v).or_insert_with(|| {
                let i = next;
                next += 1;
                i
            });
        }
        for node in &blk.body {
            for r in &node.results {
                m.entry(*r).or_insert_with(|| {
                    let i = next;
                    next += 1;
                    i
                });
            }
        }
    }
    m
}

// -----------------------------------------------------------------------------
// Block-body diff
// -----------------------------------------------------------------------------

#[allow(clippy::too_many_arguments)]
fn diff_block_body(
    ma: &Module,
    mb: &Module,
    ba: &Block,
    bb: &Block,
    va: &HashMap<ValueId, u32>,
    vb: &HashMap<ValueId, u32>,
    ba_map: &HashMap<BlockId, u32>,
    bb_map: &HashMap<BlockId, u32>,
    opts: DiffOptions,
) -> Vec<InstrChange> {
    let mut changes = Vec::new();
    let n = ba.body.len().max(bb.body.len());
    for i in 0..n {
        match (ba.body.get(i), bb.body.get(i)) {
            (Some(na), Some(nb)) => {
                let fa_key = fp_inst(ma, &na.inst, va, ba_map);
                let fb_key = fp_inst(mb, &nb.inst, vb, bb_map);
                let inst_eq = fa_key == fb_key;

                let proofs_eq = if opts.ignore_proofs {
                    true
                } else {
                    fp_proofs(&na.proofs) == fp_proofs(&nb.proofs)
                        && fp_proof_context(ma, na.proof_context.as_ref())
                            == fp_proof_context(mb, nb.proof_context.as_ref())
                };

                if !inst_eq || !proofs_eq {
                    changes.push(InstrChange::Replaced {
                        index: i,
                        before: render_inst(ma, na, opts),
                        after: render_inst(mb, nb, opts),
                    });
                }
            }
            (Some(na), None) => changes.push(InstrChange::Removed {
                index: i,
                summary: render_inst(ma, na, opts),
            }),
            (None, Some(nb)) => changes.push(InstrChange::Added {
                index: i,
                summary: render_inst(mb, nb, opts),
            }),
            (None, None) => unreachable!(),
        }
    }
    changes
}

// -----------------------------------------------------------------------------
// Proof diff
// -----------------------------------------------------------------------------

fn proof_diff(a: &[ProofAnnotation], b: &[ProofAnnotation]) -> Vec<ProofChange> {
    let a_keys: Vec<String> = a.iter().map(fp_proof).collect();
    let b_keys: Vec<String> = b.iter().map(fp_proof).collect();
    let a_set: std::collections::HashSet<&str> = a_keys.iter().map(String::as_str).collect();
    let b_set: std::collections::HashSet<&str> = b_keys.iter().map(String::as_str).collect();

    let mut out = Vec::new();
    let mut removed: Vec<&str> = a_keys
        .iter()
        .map(String::as_str)
        .filter(|k| !b_set.contains(k))
        .collect();
    removed.sort();
    removed.dedup();
    for r in removed {
        out.push(ProofChange::Removed {
            name: r.to_string(),
        });
    }
    let mut added: Vec<&str> = b_keys
        .iter()
        .map(String::as_str)
        .filter(|k| !a_set.contains(k))
        .collect();
    added.sort();
    added.dedup();
    for a in added {
        out.push(ProofChange::Added {
            name: a.to_string(),
        });
    }
    out
}

fn fp_proofs(ps: &[ProofAnnotation]) -> String {
    let mut keys: Vec<String> = ps.iter().map(fp_proof).collect();
    keys.sort();
    keys.join(",")
}

// -----------------------------------------------------------------------------
// Module-level proof-state diff (obligations + certificates)
// -----------------------------------------------------------------------------

/// Diff the module-level proof state: `proof_obligations` and
/// `proof_certificates`.
///
/// Like the rest of this module, the comparison is insensitive to arena id
/// renumbering and declaration order. Obligations are matched across modules
/// by their *claim* — kind, scope (function name, not `FuncId`), description,
/// formula, and embedded source identity — so that the same obligation renumbered in B's proof table
/// still lines up with A's. The `status` field is the mutable label that, when
/// it differs for a matched claim, is reported as a status change. Certificates
/// are matched by their claim's obligation key plus prover and evidence.
fn proof_state_diff(a: &Module, b: &Module) -> Vec<ProofStateChange> {
    let mut out = Vec::new();

    // --- Obligations: match by claim key, compare status -----------------
    // Map claim -> status for each side. Duplicates keep the first occurrence
    // (a module should not carry two obligations with an identical claim, but
    // if it does the match is still deterministic by declaration order).
    let mut a_obl: HashMap<String, &ProofObligation> = HashMap::new();
    for o in &a.proof_obligations {
        a_obl.entry(fp_obligation_claim(a, o)).or_insert(o);
    }
    let mut b_obl: HashMap<String, &ProofObligation> = HashMap::new();
    for o in &b.proof_obligations {
        b_obl.entry(fp_obligation_claim(b, o)).or_insert(o);
    }

    let mut obl_keys: Vec<&str> = a_obl.keys().map(String::as_str).collect();
    for k in b_obl.keys() {
        if !a_obl.contains_key(k) {
            obl_keys.push(k);
        }
    }
    obl_keys.sort();
    for k in obl_keys {
        match (a_obl.get(k), b_obl.get(k)) {
            (Some(oa), None) => out.push(ProofStateChange::ObligationRemoved {
                obligation: k.to_string(),
                status: oa.status.to_string(),
            }),
            (None, Some(ob)) => out.push(ProofStateChange::ObligationAdded {
                obligation: k.to_string(),
                status: ob.status.to_string(),
            }),
            (Some(oa), Some(ob)) => {
                if oa.status != ob.status {
                    out.push(ProofStateChange::ObligationStatusChanged {
                        obligation: k.to_string(),
                        before: oa.status.to_string(),
                        after: ob.status.to_string(),
                    });
                }
            }
            (None, None) => unreachable!(),
        }
    }

    // --- Certificates: match by full structural fingerprint --------------
    let a_certs: Vec<String> = a
        .proof_certificates
        .iter()
        .map(|c| fp_certificate(a, c))
        .collect();
    let b_certs: Vec<String> = b
        .proof_certificates
        .iter()
        .map(|c| fp_certificate(b, c))
        .collect();
    let a_cert_set: std::collections::HashSet<&str> = a_certs.iter().map(String::as_str).collect();
    let b_cert_set: std::collections::HashSet<&str> = b_certs.iter().map(String::as_str).collect();

    let mut removed: Vec<&str> = a_certs
        .iter()
        .map(String::as_str)
        .filter(|k| !b_cert_set.contains(k))
        .collect();
    removed.sort();
    removed.dedup();
    for r in removed {
        out.push(ProofStateChange::CertificateRemoved {
            certificate: r.to_string(),
        });
    }
    let mut added: Vec<&str> = b_certs
        .iter()
        .map(String::as_str)
        .filter(|k| !a_cert_set.contains(k))
        .collect();
    added.sort();
    added.dedup();
    for a in added {
        out.push(ProofStateChange::CertificateAdded {
            certificate: a.to_string(),
        });
    }

    out
}

/// Stable, id-renumbering-insensitive key for the *claim* an obligation makes:
/// its kind, scope (resolved to the function name), description, formula, and
/// embedded source/public identity.
/// Deliberately excludes `id` (arena index) and `status` (the mutable label
/// whose changes `proof_state_diff` reports separately).
fn fp_obligation_claim(m: &Module, o: &ProofObligation) -> String {
    let mut s = String::new();
    let _ = write!(s, "kind={}", o.kind);
    let func = o
        .function
        .and_then(|fid| m.functions.iter().find(|f| f.id == fid))
        .map(|f| f.name.as_str());
    match func {
        Some(name) => {
            let _ = write!(s, ";fn={name}");
        }
        None => s.push_str(";fn=_"),
    }
    let _ = write!(s, ";desc={}", o.description);
    match &o.formula {
        Some(f) => {
            let _ = write!(s, ";formula[{}]={}", f.schema, f.payload);
            if let Some(smt) = &f.smtlib {
                let _ = write!(s, ";smt={smt}");
            }
            if let Some(sort) = &f.sort {
                let _ = write!(s, ";sort={sort}");
            }
        }
        None => s.push_str(";formula=_"),
    }
    let mut source_bytes = Vec::new();
    write_proof_obligation_source_identity_stable(&mut source_bytes, o.source.as_ref());
    s.push_str(";source=");
    for byte in source_bytes {
        let _ = write!(s, "{byte:02x}");
    }
    s
}

/// Resolve a `ProofId` to the claim key of the obligation it names within `m`,
/// or a renumber-stable placeholder when the id has no matching obligation.
fn obligation_claim_by_id(m: &Module, id: ProofId) -> String {
    match m.proof_obligations.iter().find(|o| o.id == id) {
        Some(o) => fp_obligation_claim(m, o),
        // Dangling reference: fall back to the raw index so a difference still
        // surfaces, but keep it visibly distinct from a resolved claim.
        None => format!("obl#{}", id.index()),
    }
}

/// Structural fingerprint of a certificate. The obligation is referenced by
/// its claim key (so renumbering the proof table does not surface here), and
/// the prover and evidence are compared structurally.
fn fp_certificate(m: &Module, c: &ProofCertificate) -> String {
    format!(
        "obl={};prover={};ev={}",
        obligation_claim_by_id(m, c.obligation),
        c.prover,
        fp_evidence(&c.evidence)
    )
}

fn fp_evidence(e: &ProofEvidence) -> String {
    match e {
        ProofEvidence::SmtProof(bytes) => {
            let mut s = String::from("smt:");
            for byte in bytes {
                let _ = write!(s, "{byte:02x}");
            }
            s
        }
        ProofEvidence::LeanProof(term) => format!("lean:{term}"),
        ProofEvidence::KaniHarness(h) => format!("kani:{h}"),
        ProofEvidence::GammaCrownBound {
            epsilon,
            verified_layers,
        } => format!("gcrown:{}:{verified_layers}", epsilon.to_bits()),
        ProofEvidence::TranslationValidation {
            rule_name,
            smt_hash,
        } => {
            let mut s = format!("tv:{rule_name}:");
            for byte in smt_hash {
                let _ = write!(s, "{byte:02x}");
            }
            s
        }
        ProofEvidence::Trusted(reason) => format!("trusted:{reason}"),
        ProofEvidence::InheritedFromCallee { callee, obligation } => {
            // Callee `FuncId` is left as a raw index here: certificates do not
            // carry the module they came from, and the obligation reference is
            // already an arena id. This keeps the fingerprint total without
            // pretending an id resolves to a name out of context.
            format!("inherited:{}:{}", callee.index(), obligation.index())
        }
        ProofEvidence::CleanCic {
            term,
            context,
            lineage,
            // The kernel re-check directive is not part of this textual diff
            // fingerprint (consistent with the textual display format); it
            // travels in the structured serde/binary format.
            kernel_recheck: _,
        } => {
            let mut s = String::from("cleancic:");
            for byte in term {
                let _ = write!(s, "{byte:02x}");
            }
            s.push(':');
            for byte in context {
                let _ = write!(s, "{byte:02x}");
            }
            let _ = write!(s, ":{lineage}");
            s
        }
    }
}

/// Stable fingerprint of a node's per-call `ProofContext`. Both `assumes` and
/// `establishes` reference module obligation ids; each is resolved to the
/// obligation's claim key within the node's own module so the comparison is
/// insensitive to proof-table renumbering. The two id lists are sorted so that
/// reordering the references alone does not register as a difference.
fn fp_proof_context(m: &Module, ctx: Option<&ProofContext>) -> String {
    let Some(ctx) = ctx else {
        return String::new();
    };
    let mut assumes: Vec<String> = ctx
        .assumes
        .iter()
        .map(|id| obligation_claim_by_id(m, *id))
        .collect();
    assumes.sort();
    let mut establishes: Vec<String> = ctx
        .establishes
        .iter()
        .map(|id| obligation_claim_by_id(m, *id))
        .collect();
    establishes.sort();
    format!(
        "assumes=[{}];establishes=[{}]",
        assumes.join("|"),
        establishes.join("|")
    )
}

/// Rendered producer-provenance value (v23) for a [`MetaChange`]; `-` marks an
/// absent tag so `None -> Some(...)` transitions render as `- -> trust`.
fn producer_fp(p: Option<&crate::Producer>) -> String {
    p.map_or_else(|| "-".to_string(), ToString::to_string)
}

/// Render the complete proof-relevant source carrier in deterministic order.
/// Do not fingerprint only its stored binding digest: a forged carrier that
/// leaves that digest stale must still be visible in an audit diff.
fn source_provenance_fp(p: Option<&crate::SourceProvenance>) -> String {
    let Some(p) = p else {
        return "-".to_string();
    };
    let mut out = format!(
        "schema={};compiler={};semantic={};binding={};loops=[",
        p.schema, p.compiler_source_digest, p.semantic_body_digest, p.binding_digest,
    );
    for (loop_index, source_loop) in p.loops.iter().enumerate() {
        if loop_index != 0 {
            out.push('|');
        }
        let _ = write!(
            out,
            "{}:{}:bb{}:(",
            source_loop.source_loop_id,
            source_loop.hir_local_id,
            source_loop.header.index(),
        );
        for (binding_index, binding) in source_loop.bindings.iter().enumerate() {
            if binding_index != 0 {
                out.push(',');
            }
            let (place, index) = match binding.place {
                crate::SourcePlace::FunctionParameter { index } => ("fn", index),
                crate::SourcePlace::LoopParameter { index } => ("loop", index),
            };
            let _ = write!(
                out,
                "{:?}:{}:{place}{index}",
                binding.name, binding.hir_local_id,
            );
        }
        out.push(')');
    }
    out.push(']');
    out
}

/// Order-stable structural fingerprint of a function's separate-compilation
/// contract. `None` and an empty summary both fingerprint to the empty marker so
/// only a real contract change is reported.
fn summary_fp(s: Option<&crate::FunctionSummary>) -> String {
    // R3 #8: `proved` is part of the contract — fold it into the triviality test, so
    // a `None -> Some(proved, empty)` or `proved=false -> true` transition on an
    // otherwise-empty summary is still fingerprinted (was collapsing to the same `∅`
    // marker as `None`). Only a genuinely empty, param-less, UNPROVED summary is ≡ None.
    let Some(s) = s.filter(|s| !(s.is_empty() && s.params.is_empty() && !s.proved)) else {
        return "∅".to_string();
    };
    // Fingerprint ALL four ProofFormula fields: smtlib/sort are what the verifier
    // dispatches/solves on (independent of the opaque payload), so a changed SMT
    // rendering of a published contract must be reported (audit 2026-06-25 F3).
    let clause = |c: &crate::ProofFormula| {
        format!(
            "{}|{}|{}|{}",
            c.schema,
            c.payload,
            c.smtlib.as_deref().unwrap_or(""),
            c.sort.as_deref().unwrap_or(""),
        )
    };
    let req: Vec<String> = s.requires.iter().map(clause).collect();
    let ens: Vec<String> = s.ensures.iter().map(clause).collect();
    format!(
        "proved={};params=[{}];requires=[{}];ensures=[{}]",
        s.proved,
        s.params.join(","),
        req.join(";"),
        ens.join(";"),
    )
}

fn fp_proof(p: &ProofAnnotation) -> String {
    match p {
        ProofAnnotation::InBounds => "InBounds".to_string(),
        ProofAnnotation::NotNull => "NotNull".to_string(),
        ProofAnnotation::ValidBorrow => "ValidBorrow".to_string(),
        ProofAnnotation::UniqueBorrow => "UniqueBorrow".to_string(),
        ProofAnnotation::SharedBorrow => "SharedBorrow".to_string(),
        ProofAnnotation::ValidDealloc => "ValidDealloc".to_string(),
        ProofAnnotation::NoOverflow => "NoOverflow".to_string(),
        ProofAnnotation::NoWrap => "NoWrap".to_string(),
        ProofAnnotation::DivNonZero => "DivNonZero".to_string(),
        ProofAnnotation::ShiftInRange => "ShiftInRange".to_string(),
        ProofAnnotation::Pure => "Pure".to_string(),
        ProofAnnotation::Terminates => "Terminates".to_string(),
        ProofAnnotation::Deterministic => "Deterministic".to_string(),
        ProofAnnotation::Associative => "Associative".to_string(),
        ProofAnnotation::Commutative => "Commutative".to_string(),
        ProofAnnotation::DataRaceFree => "DataRaceFree".to_string(),
        ProofAnnotation::Tainted => "Tainted".to_string(),
        ProofAnnotation::TrustedSink => "TrustedSink".to_string(),
        ProofAnnotation::FreshSymbolicHavoc => "FreshSymbolicHavoc".to_string(),
        ProofAnnotation::AtomicOrdering(o) => format!("AtomicOrdering({:?})", o),
        ProofAnnotation::BoundedOutput { lo, hi } => {
            format!("BoundedOutput({},{})", lo.to_bits(), hi.to_bits())
        }
        ProofAnnotation::Monotonic => "Monotonic".to_string(),
        ProofAnnotation::NoAlias => "NoAlias".to_string(),
        ProofAnnotation::Aligned(n) => format!("Aligned({n})"),
        ProofAnnotation::NoPanic => "NoPanic".to_string(),
        ProofAnnotation::NoUndef => "NoUndef".to_string(),
        ProofAnnotation::ReadonlyTable => "ReadonlyTable".to_string(),
        ProofAnnotation::AppendOnlyBuffer => "AppendOnlyBuffer".to_string(),
        ProofAnnotation::AtomicSetInsert => "AtomicSetInsert".to_string(),
        ProofAnnotation::ParallelMap => "ParallelMap".to_string(),
        ProofAnnotation::BoundedLoop(n) => format!("BoundedLoop({n})"),
        ProofAnnotation::DivergenceClass(d) => match d {
            Divergence::Uniform => "DivergenceClass(Uniform)".to_string(),
            Divergence::Low => "DivergenceClass(Low)".to_string(),
            Divergence::High => "DivergenceClass(High)".to_string(),
        },
        // Fusion obligation carrier (clean-expr): fingerprint structurally via
        // its Debug form so semantic diff can detect a changed goal/hypotheses.
        #[cfg(feature = "clean-expr")]
        ProofAnnotation::Goal(ob) => format!("Goal({ob:?})"),
        ProofAnnotation::ProofRef(id) => format!("ProofRef({})", id.index()),
        ProofAnnotation::ValueRange { lo, hi } => format!("ValueRange({lo},{hi})"),
        ProofAnnotation::KnownBits { zeros, ones } => format!("KnownBits({zeros},{ones})"),
        ProofAnnotation::BranchWeights(w) => format!(
            "BranchWeights({})",
            w.iter()
                .map(|x| x.to_string())
                .collect::<Vec<_>>()
                .join(",")
        ),
        ProofAnnotation::Custom(ProofTag(t)) => format!("Custom({t})"),
        ProofAnnotation::Wrapping => "Wrapping".to_string(),
    }
}

// -----------------------------------------------------------------------------
// Fingerprinting
// -----------------------------------------------------------------------------

/// Fingerprint an `Inst` to a canonical string. The fingerprint ignores
/// raw `ValueId` / `BlockId` / type-table-id numbering by substituting
/// the canonical visit-order indices from the supplied maps.
fn fp_inst(
    m: &Module,
    inst: &Inst,
    vm: &HashMap<ValueId, u32>,
    bm: &HashMap<BlockId, u32>,
) -> String {
    let mut s = String::new();
    let vv = |v: &ValueId| -> String {
        match vm.get(v) {
            Some(i) => format!("v{i}"),
            None => format!("v?{}", v.0),
        }
    };
    let vb = |b: &BlockId| -> String {
        match bm.get(b) {
            Some(i) => format!("b{i}"),
            None => format!("b?{}", b.0),
        }
    };

    match inst {
        Inst::BinOp { op, ty, lhs, rhs } => {
            let _ = write!(s, "BinOp({op:?},{},{},{})", fp_ty(m, ty), vv(lhs), vv(rhs));
        }
        Inst::SeqMapAddK { ty, seq, k } => {
            let _ = write!(s, "SeqMapAddK({},{},{k})", fp_ty(m, ty), vv(seq));
        }
        Inst::SeqMapNot { ty, seq } => {
            let _ = write!(s, "SeqMapNot({},{})", fp_ty(m, ty), vv(seq));
        }
        Inst::SeqMap { ty, seq, fwd } => {
            // The element function is a FuncId; resolve it by NAME (like Call)
            // so id renumbering does not surface in the fingerprint.
            let name = m
                .functions
                .iter()
                .find(|f| f.id == *fwd)
                .map(|f| f.name.as_str())
                .unwrap_or("<unknown>");
            let _ = write!(s, "SeqMap({},{},{name})", fp_ty(m, ty), vv(seq));
        }
        Inst::UnOp { op, ty, operand } => {
            let _ = write!(s, "UnOp({op:?},{},{})", fp_ty(m, ty), vv(operand));
        }
        Inst::Overflow { op, ty, lhs, rhs } => {
            let _ = write!(
                s,
                "Overflow({op:?},{},{},{})",
                fp_ty(m, ty),
                vv(lhs),
                vv(rhs)
            );
        }
        Inst::ICmp { op, ty, lhs, rhs } => {
            let _ = write!(s, "ICmp({op:?},{},{},{})", fp_ty(m, ty), vv(lhs), vv(rhs));
        }
        Inst::FCmp { op, ty, lhs, rhs } => {
            let _ = write!(s, "FCmp({op:?},{},{},{})", fp_ty(m, ty), vv(lhs), vv(rhs));
        }
        Inst::Cast {
            op,
            src_ty,
            dst_ty,
            operand,
        } => {
            let _ = write!(
                s,
                "Cast({op:?},{},{},{})",
                fp_ty(m, src_ty),
                fp_ty(m, dst_ty),
                vv(operand)
            );
        }
        Inst::PtrData { ptr_ty, ptr } => {
            let _ = write!(s, "PtrData({},{})", fp_ty(m, ptr_ty), vv(ptr));
        }
        Inst::PtrMetadata {
            ptr_ty,
            metadata_ty,
            ptr,
        } => {
            let _ = write!(
                s,
                "PtrMetadata({},{},{})",
                fp_ty(m, ptr_ty),
                fp_ty(m, metadata_ty),
                vv(ptr)
            );
        }
        Inst::PtrFromParts {
            ptr_ty,
            metadata_ty,
            data,
            metadata,
        } => {
            let _ = write!(
                s,
                "PtrFromParts({},{},{},{})",
                fp_ty(m, ptr_ty),
                fp_ty(m, metadata_ty),
                vv(data),
                vv(metadata)
            );
        }
        Inst::Load {
            ty,
            ptr,
            volatile,
            align,
        } => {
            let _ = write!(
                s,
                "Load({},{},{volatile},{:?})",
                fp_ty(m, ty),
                vv(ptr),
                align
            );
        }
        Inst::Store {
            ty,
            ptr,
            value,
            volatile,
            align,
        } => {
            let _ = write!(
                s,
                "Store({},{},{},{volatile},{:?})",
                fp_ty(m, ty),
                vv(ptr),
                vv(value),
                align
            );
        }
        Inst::Alloca { ty, count, align } => {
            let cnt = count.map(|c| vv(&c)).unwrap_or_else(|| "_".to_string());
            let _ = write!(s, "Alloca({},{cnt},{:?})", fp_ty(m, ty), align);
        }
        Inst::HeapAlloc {
            ty,
            count,
            align,
            origin,
        } => {
            let cnt = count.map(|c| vv(&c)).unwrap_or_else(|| "_".to_string());
            let _ = write!(
                s,
                "HeapAlloc({},{cnt},{:?},{:?})",
                fp_ty(m, ty),
                align,
                origin
            );
        }
        Inst::GEP {
            pointee_ty,
            base,
            indices,
            inbounds,
        } => {
            let idx = indices.iter().map(vv).collect::<Vec<_>>().join(",");
            let _ = write!(
                s,
                "GEP({},{},[{idx}],{inbounds})",
                fp_ty(m, pointee_ty),
                vv(base)
            );
        }
        Inst::AtomicLoad { ty, ptr, ordering } => {
            let _ = write!(s, "AtomicLoad({},{},{ordering:?})", fp_ty(m, ty), vv(ptr));
        }
        Inst::AtomicStore {
            ty,
            ptr,
            value,
            ordering,
        } => {
            let _ = write!(
                s,
                "AtomicStore({},{},{},{ordering:?})",
                fp_ty(m, ty),
                vv(ptr),
                vv(value)
            );
        }
        Inst::AtomicRMW {
            op,
            ty,
            ptr,
            value,
            ordering,
        } => {
            let _ = write!(
                s,
                "AtomicRMW({op:?},{},{},{},{ordering:?})",
                fp_ty(m, ty),
                vv(ptr),
                vv(value)
            );
        }
        Inst::CmpXchg {
            ty,
            ptr,
            expected,
            desired,
            success,
            failure,
        } => {
            let _ = write!(
                s,
                "CmpXchg({},{},{},{},{success:?},{failure:?})",
                fp_ty(m, ty),
                vv(ptr),
                vv(expected),
                vv(desired)
            );
        }
        Inst::Fence { ordering } => {
            let _ = write!(s, "Fence({ordering:?})");
        }
        Inst::Br { target, args } => {
            let argstr = args.iter().map(vv).collect::<Vec<_>>().join(",");
            let _ = write!(s, "Br({},[{argstr}])", vb(target));
        }
        Inst::CondBr {
            cond,
            then_target,
            then_args,
            else_target,
            else_args,
        } => {
            let t = then_args.iter().map(vv).collect::<Vec<_>>().join(",");
            let e = else_args.iter().map(vv).collect::<Vec<_>>().join(",");
            let _ = write!(
                s,
                "CondBr({},{},[{t}],{},[{e}])",
                vv(cond),
                vb(then_target),
                vb(else_target)
            );
        }
        Inst::Switch {
            value,
            default,
            default_args,
            cases,
            ..
        } => {
            let d = default_args.iter().map(vv).collect::<Vec<_>>().join(",");
            let mut cs = String::new();
            for (ci, c) in cases.iter().enumerate() {
                if ci > 0 {
                    cs.push(',');
                }
                let a = c.args.iter().map(vv).collect::<Vec<_>>().join(",");
                let _ = write!(cs, "{{{},{}", fp_constant(m, &c.value), vb(&c.target));
                let _ = write!(cs, ",[{a}]}}");
            }
            let _ = write!(s, "Switch({},{},[{d}],[{cs}])", vv(value), vb(default));
        }
        Inst::Call { callee, args } => {
            // Callee is a FuncId; resolve it by the callee function's *name*
            // when possible so that id renumbering does not surface here.
            let name = m
                .functions
                .iter()
                .find(|f| f.id == *callee)
                .map(|f| f.name.as_str())
                .unwrap_or("<unknown>");
            let a = args.iter().map(vv).collect::<Vec<_>>().join(",");
            let _ = write!(s, "Call({name},[{a}])");
        }
        Inst::CallIndirect {
            callee,
            sig,
            args,
            calling_conv,
        } => {
            let a = args.iter().map(vv).collect::<Vec<_>>().join(",");
            let _ = write!(
                s,
                "CallIndirect({},{},[{a}],{calling_conv})",
                vv(callee),
                fp_func_ty_ref(m, *sig)
            );
        }
        Inst::Return { values } => {
            let vs = values.iter().map(vv).collect::<Vec<_>>().join(",");
            let _ = write!(s, "Return([{vs}])");
        }
        Inst::ExtractField {
            ty,
            aggregate,
            field,
        } => {
            let _ = write!(
                s,
                "ExtractField({},{},{field})",
                fp_ty(m, ty),
                vv(aggregate)
            );
        }
        Inst::InsertField {
            ty,
            aggregate,
            field,
            value,
        } => {
            let _ = write!(
                s,
                "InsertField({},{},{field},{})",
                fp_ty(m, ty),
                vv(aggregate),
                vv(value)
            );
        }
        Inst::ExtractElement { ty, array, index } => {
            let _ = write!(
                s,
                "ExtractElement({},{},{})",
                fp_ty(m, ty),
                vv(array),
                vv(index)
            );
        }
        Inst::InsertElement {
            ty,
            array,
            index,
            value,
        } => {
            let _ = write!(
                s,
                "InsertElement({},{},{},{})",
                fp_ty(m, ty),
                vv(array),
                vv(index),
                vv(value)
            );
        }
        Inst::Const { ty, value } => {
            let _ = write!(s, "Const({},{})", fp_ty(m, ty), fp_constant(m, value));
        }
        Inst::NullPtr => s.push_str("NullPtr"),
        Inst::GlobalAddr { global } => {
            let _ = write!(s, "GlobalAddr({})", global.index());
        }
        Inst::Undef { ty } => {
            let _ = write!(s, "Undef({})", fp_ty(m, ty));
        }
        Inst::Assume { cond } => {
            let _ = write!(s, "Assume({})", vv(cond));
        }
        Inst::Assert { cond } => {
            let _ = write!(s, "Assert({})", vv(cond));
        }
        Inst::Unreachable => s.push_str("Unreachable"),
        Inst::Copy { ty, operand } => {
            let _ = write!(s, "Copy({},{})", fp_ty(m, ty), vv(operand));
        }
        Inst::Select {
            ty,
            cond,
            then_val,
            else_val,
        } => {
            let _ = write!(
                s,
                "Select({},{},{},{})",
                fp_ty(m, ty),
                vv(cond),
                vv(then_val),
                vv(else_val)
            );
        }
        Inst::Borrow { ptr } => {
            let _ = write!(s, "Borrow({})", vv(ptr));
        }
        Inst::BorrowMut { ptr } => {
            let _ = write!(s, "BorrowMut({})", vv(ptr));
        }
        Inst::EndBorrow { borrow_ptr } => {
            let _ = write!(s, "EndBorrow({})", vv(borrow_ptr));
        }
        Inst::Retain { ptr } => {
            let _ = write!(s, "Retain({})", vv(ptr));
        }
        Inst::Release { ptr } => {
            let _ = write!(s, "Release({})", vv(ptr));
        }
        Inst::IsUnique { ptr } => {
            let _ = write!(s, "IsUnique({})", vv(ptr));
        }
        Inst::Dealloc { ptr } => {
            let _ = write!(s, "Dealloc({})", vv(ptr));
        }
        Inst::OpenFrame { def } => {
            let _ = write!(s, "OpenFrame({})", fp_binding_frame_def(m, def));
        }
        Inst::BindSlot { frame, slot, value } => {
            let _ = write!(s, "BindSlot({},{slot},{})", vv(frame), vv(value));
        }
        Inst::LoadSlot { frame, slot, ty } => {
            let _ = write!(s, "LoadSlot({},{slot},{})", vv(frame), fp_ty(m, ty));
        }
        Inst::CloseFrame { frame } => {
            let _ = write!(s, "CloseFrame({})", vv(frame));
        }
        Inst::CoroSuspend {
            frame,
            state_slot,
            next_state,
            value,
        } => {
            let _ = write!(
                s,
                "CoroSuspend({},{state_slot},{next_state},{})",
                vv(frame),
                vv(value)
            );
        }
        Inst::Invoke {
            callee,
            args,
            normal_dest,
            normal_args,
            unwind_dest,
        } => {
            // Resolve callee by name so id renumbering does not surface (same
            // rationale as the `Call` arm above).
            let name = m
                .functions
                .iter()
                .find(|f| f.id == *callee)
                .map(|f| f.name.as_str())
                .unwrap_or("<unknown>");
            let a = args.iter().map(vv).collect::<Vec<_>>().join(",");
            let na = normal_args.iter().map(vv).collect::<Vec<_>>().join(",");
            let _ = write!(
                s,
                "Invoke({name},[{a}],{},[{na}],{})",
                vb(normal_dest),
                vb(unwind_dest)
            );
        }
        Inst::LandingPad {
            is_cleanup,
            catch_type_indices,
        } => {
            let c = catch_type_indices
                .iter()
                .map(|i| i.to_string())
                .collect::<Vec<_>>()
                .join(",");
            let _ = write!(s, "LandingPad({is_cleanup},[{c}])");
        }
        Inst::Resume { exn } => {
            let _ = write!(s, "Resume({})", vv(exn));
        }
        Inst::DialectOp(d) => {
            let _ = write!(s, "DialectOp({})", fp_dialect(m, d, vm));
        }
    }
    s
}

fn fp_binding_frame_def(m: &Module, def: &BindingFrameDef) -> String {
    let mut s = String::new();
    // Do not include the frame id — it's function-local and may renumber.
    let _ = write!(s, "{{name={}", def.name);
    for (i, slot) in def.slots.iter().enumerate() {
        let _ = write!(s, ",slot{i}:{}:{}", slot.name, fp_ty(m, &slot.ty));
        // silence BindingSlot unused import if no tests touch it
        let _: &BindingSlot = slot;
    }
    s.push('}');
    s
}

fn fp_dialect(m: &Module, d: &DialectInst, vm: &HashMap<ValueId, u32>) -> String {
    let mut s = String::new();
    let _ = write!(s, "{}.{}:v{}", d.dialect, d.op, d.version);
    for v in &d.operands {
        let key = match vm.get(v) {
            Some(i) => format!("v{i}"),
            None => format!("v?{}", v.0),
        };
        let _ = write!(s, ";op={key}");
    }
    for t in &d.result_tys {
        let _ = write!(s, ";rt={}", fp_ty(m, t));
    }
    let mut attrs: Vec<&AttrEntry> = d.attrs.iter().collect();
    attrs.sort_by(|a, b| a.name.cmp(&b.name));
    for a in attrs {
        let _ = write!(s, ";a[{}]={}", a.name, fp_attr(m, &a.value));
    }
    s
}

fn fp_attr(m: &Module, v: &AttrValue) -> String {
    match v {
        AttrValue::I64(x) => format!("i64:{x}"),
        AttrValue::U64(x) => format!("u64:{x}"),
        AttrValue::F64(x) => format!("f64:{}", x.to_bits()),
        AttrValue::Bool(x) => format!("bool:{x}"),
        AttrValue::Str(x) => format!("str:{x}"),
        AttrValue::Bytes(x) => {
            let mut h = String::from("bytes:");
            for b in x {
                let _ = write!(h, "{b:02x}");
            }
            h
        }
        AttrValue::Ty(t) => format!("ty:{}", fp_ty(m, t)),
    }
}

/// Structural fingerprint of a `Ty`. Table references (`Struct`, `Enum`,
/// `Record`, `Closure`, `Func`, `Array`) are resolved against `m` and
/// rendered by definition rather than by id index.
fn fp_ty(m: &Module, t: &Ty) -> String {
    match t {
        Ty::I8 => "i8".into(),
        Ty::I16 => "i16".into(),
        Ty::I32 => "i32".into(),
        Ty::I64 => "i64".into(),
        Ty::I128 => "i128".into(),
        Ty::U8 => "u8".into(),
        Ty::U16 => "u16".into(),
        Ty::U32 => "u32".into(),
        Ty::U64 => "u64".into(),
        Ty::U128 => "u128".into(),
        Ty::Isize => "isize".into(),
        Ty::Usize => "usize".into(),
        Ty::Char => "char".into(),
        Ty::Error => "error".into(),
        Ty::F16 => "f16".into(),
        Ty::F32 => "f32".into(),
        Ty::F64 => "f64".into(),
        Ty::Bool => "bool".into(),
        Ty::Ptr => "ptr".into(),
        Ty::FatPtr(kind) => format!("fatptr<{}>", fp_fat_ptr_kind(m, kind)),
        Ty::Unit => "unit".into(),
        Ty::Never => "never".into(),
        Ty::Struct(id) => fp_struct_ref(m, *id),
        Ty::Array(elem, n) => format!("arr[{};{}]", fp_tyid_ref(m, *elem), n),
        Ty::Vector(elem, lanes) => format!("vec<{lanes}x{}>", fp_ty(m, elem)),
        Ty::Tuple(ts) => {
            let mut s = String::from("tuple(");
            for (i, t) in ts.iter().enumerate() {
                if i > 0 {
                    s.push(',');
                }
                s.push_str(&fp_ty(m, t));
            }
            s.push(')');
            s
        }
        Ty::Enum(id) => fp_enum_ref(m, *id),
        Ty::Func(id) => fp_func_ty_ref(m, *id),
        Ty::Ref(inner) => format!("&{}", fp_ty(m, inner)),
        Ty::RefMut(inner) => format!("&mut {}", fp_ty(m, inner)),
        Ty::PtrConst(inner) => format!("*const {}", fp_ty(m, inner)),
        Ty::PtrMut(inner) => format!("*mut {}", fp_ty(m, inner)),
        Ty::Rc(inner) => format!("Rc<{}>", fp_ty(m, inner)),
        Ty::Set(elem, repr) => format!(
            "set<{},{}>",
            fp_tyid_ref(m, *elem),
            match repr {
                SetRepr::Bitset => "bitset",
                SetRepr::Boxed => "boxed",
            }
        ),
        Ty::Sequence(elem) => format!("seq<{}>", fp_tyid_ref(m, *elem)),
        Ty::Record(id) => fp_record_ref(m, *id),
        Ty::Closure(id) => fp_closure_ref(m, *id),
        // The predicate is resolved into the fingerprint rather than cited by
        // id: two structurally identical refinements must fingerprint the same
        // even if their modules interned in a different order.
        Ty::Refine(base, pred) => format!(
            "refine<{},{}>",
            fp_tyid_ref(m, *base),
            match m.predicates.get(pred.as_usize()) {
                Some(p) => format!("{p}"),
                None => format!("pred#{}", pred.index()),
            }
        ),
    }
}

fn fp_fat_ptr_kind(m: &Module, kind: &FatPtrKind) -> String {
    match kind {
        FatPtrKind::Slice(elem) => format!("slice {}", fp_tyid_ref(m, *elem)),
        FatPtrKind::Str => "str".to_string(),
        FatPtrKind::TraitObject { trait_id } => format!("dyn.{trait_id}"),
    }
}

fn fp_tyid_ref(m: &Module, id: TyId) -> String {
    match m.types.get(id.as_usize()) {
        Some(t) => fp_ty(m, t),
        None => format!("ty#{}", id.0),
    }
}

fn fp_struct_ref(m: &Module, id: StructId) -> String {
    let sd: Option<&StructDef> = m.structs.iter().find(|s| s.id == id);
    match sd {
        Some(sd) => {
            // `repr` is part of the ABI contract (Rust vs C vs transparent vs
            // packed(N)) — two structs identical in name/size/align/fields but
            // differing in repr are ABI-incompatible, so it MUST participate in
            // the fingerprint or `trust-ir-diff` would report them as identical.
            let mut s = format!(
                "struct({},size={:?},align={:?},repr={:?}",
                sd.name, sd.size, sd.align, sd.repr
            );
            for f in &sd.fields {
                let _ = write!(s, ",{}", fp_field(m, f));
            }
            s.push(')');
            s
        }
        None => format!("struct#{}", id.0),
    }
}

fn fp_enum_ref(m: &Module, id: EnumId) -> String {
    let ed: Option<&EnumDef> = m.enums.iter().find(|e| e.id == id);
    match ed {
        Some(ed) => {
            let mut s = format!("enum({}", ed.name);
            for v in &ed.variants {
                let _ = write!(s, ",{}", fp_variant(m, v));
            }
            // Canonical-layout identity, not spelling: fingerprint the
            // EFFECTIVE discriminants and the RESOLVED tag repr, so an
            // explicit `A = 0, B = 1` spelling of the implicit default (and a
            // `repr(u8)` hint naming the tag the canonical rule picks anyway)
            // fingerprints equal. An ill-formed assignment (duplicates /
            // overflow / unfittable hint) falls back to the raw fields so two
            // differently-broken defs still compare unequal.
            match ed.effective_discriminants() {
                Some(discs) => {
                    let _ = write!(s, ";discs{discs:?}");
                }
                None => {
                    let _ = write!(s, ";raw_discs{:?}", ed.discriminants);
                }
            }
            match ed.canonical_tag_repr() {
                Some(tag) => {
                    let _ = write!(s, ";tag={tag}");
                }
                None => {
                    let _ = write!(s, ";tag=unavailable(hint={:?})", ed.repr);
                }
            }
            match &ed.layout {
                None => s.push_str(";layout=canonical"),
                Some(layout) => {
                    let _ = write!(s, ";layout={}:{}:", layout.size, layout.align);
                    match &layout.encoding {
                        // Distinct from the `layout=canonical` spelling above:
                        // that one means NO descriptor, this one is a declared
                        // tag-free image. Confusing them would make an enum
                        // that gained a descriptor look unchanged.
                        crate::ty::EnumTagEncoding::Untagged => {
                            s.push_str("untagged");
                        }
                        crate::ty::EnumTagEncoding::Direct { tag_offset } => {
                            let _ = write!(s, "direct@{tag_offset}");
                        }
                        crate::ty::EnumTagEncoding::Niche {
                            untagged_variant,
                            niche_variants_start,
                            niche_variants_end,
                            niche_start,
                            niche_offset,
                            niche_ty,
                        } => {
                            let _ = write!(
                                s,
                                "niche:{untagged_variant}:{niche_variants_start}:{niche_variants_end}:{niche_start}@{niche_offset}:{niche_ty}"
                            );
                        }
                    }
                    let _ = write!(s, ":offsets={:?}", layout.variant_field_offsets);
                }
            }
            s.push(')');
            s
        }
        None => format!("enum#{}", id.0),
    }
}

fn fp_variant(m: &Module, v: &EnumVariant) -> String {
    let mut s = format!("[{}", v.name);
    for t in &v.fields {
        let _ = write!(s, ",{}", fp_ty(m, t));
    }
    s.push(']');
    s
}

fn fp_record_ref(m: &Module, id: RecordId) -> String {
    let rd: Option<&RecordDef> = m.records.iter().find(|r| r.id == id);
    match rd {
        Some(rd) => {
            let mut s = format!("record({}", rd.name);
            for f in &rd.fields {
                let _ = write!(s, ",{}", fp_field(m, f));
            }
            s.push(')');
            s
        }
        None => format!("record#{}", id.0),
    }
}

fn fp_field(m: &Module, f: &FieldDef) -> String {
    format!("{}:{}:{:?}", f.name, fp_ty(m, &f.ty), f.offset)
}

fn fp_closure_ref(m: &Module, id: ClosureTyId) -> String {
    let ct: Option<&ClosureTy> = m.closure_types.get(id.as_usize());
    match ct {
        Some(ct) => {
            let mut s = format!("closure({}", fp_func_ty_ref(m, ct.func));
            for t in &ct.captures {
                let _ = write!(s, ",{}", fp_ty(m, t));
            }
            s.push(')');
            s
        }
        None => format!("closure#{}", id.0),
    }
}

fn fp_func_ty_ref(m: &Module, id: FuncTyId) -> String {
    let ft: Option<&FuncTy> = m.func_types.get(id.as_usize());
    match ft {
        Some(ft) => {
            let mut s = String::from("functy(");
            for (i, p) in ft.params.iter().enumerate() {
                if i > 0 {
                    s.push(',');
                }
                s.push_str(&fp_ty(m, p));
            }
            s.push(';');
            for (i, r) in ft.returns.iter().enumerate() {
                if i > 0 {
                    s.push(',');
                }
                s.push_str(&fp_ty(m, r));
            }
            if ft.is_vararg {
                s.push_str(";vararg");
            }
            s.push(')');
            s
        }
        None => format!("functy#{}", id.0),
    }
}

fn fp_constant(m: &Module, c: &Constant) -> String {
    match c {
        Constant::Int(x) => format!("i:{x}"),
        // v24: distinct fingerprint prefix — a canonical U128 never collides
        // with an Int value, and the prefix keeps the fingerprint honest.
        Constant::U128(x) => format!("u:{x}"),
        // v25 Bytes: hex fingerprint with the utf8 claim spelled in.
        Constant::Bytes { data, utf8 } => {
            let hex: String = data.iter().map(|b| format!("{b:02x}")).collect();
            format!("by:{}:{hex}", if *utf8 { "u" } else { "r" })
        }
        Constant::Float(x) => format!("f:{}", x.to_bits()),
        Constant::Bool(x) => format!("b:{x}"),
        Constant::Aggregate(cs) => {
            let mut s = String::from("agg(");
            for (i, c) in cs.iter().enumerate() {
                if i > 0 {
                    s.push(',');
                }
                s.push_str(&fp_constant(m, c));
            }
            s.push(')');
            s
        }
        Constant::Array(cs) => {
            let mut s = String::from("array(");
            for (i, c) in cs.iter().enumerate() {
                if i > 0 {
                    s.push(',');
                }
                s.push_str(&fp_constant(m, c));
            }
            s.push(')');
            s
        }
        Constant::Vector(cs) => {
            let mut s = String::from("vec(");
            for (i, c) in cs.iter().enumerate() {
                if i > 0 {
                    s.push(',');
                }
                s.push_str(&fp_constant(m, c));
            }
            s.push(')');
            s
        }
        Constant::Sequence(cs) => {
            let mut s = String::from("seq(");
            for (i, c) in cs.iter().enumerate() {
                if i > 0 {
                    s.push(',');
                }
                s.push_str(&fp_constant(m, c));
            }
            s.push(')');
            s
        }
        Constant::Set(cs) => {
            let mut s = String::from("set(");
            for (i, c) in cs.iter().enumerate() {
                if i > 0 {
                    s.push(',');
                }
                s.push_str(&fp_constant(m, c));
            }
            s.push(')');
            s
        }
        Constant::Record(fs) => {
            let mut s = String::from("rec(");
            for (i, (n, c)) in fs.iter().enumerate() {
                if i > 0 {
                    s.push(',');
                }
                let _ = write!(s, "{n}={}", fp_constant(m, c));
            }
            s.push(')');
            s
        }
        Constant::Closure { func, captures } => {
            // Resolve FuncId via the module's function table when possible,
            // for the same reason calls do.
            let name = m
                .functions
                .iter()
                .find(|f| f.id == *func)
                .map(|f| f.name.as_str())
                .unwrap_or("<unknown>");
            let mut s = format!("cls({name}");
            for c in captures {
                let _ = write!(s, ",{}", fp_constant(m, c));
            }
            s.push(')');
            s
        }
        Constant::FnDef(func) => {
            let name = m
                .functions
                .iter()
                .find(|f| f.id == *func)
                .map(|f| f.name.as_str())
                .unwrap_or("<unknown>");
            format!("fndef({name})")
        }
        Constant::SymbolAddr { symbol, addend } => {
            format!("symaddr({symbol},{addend})")
        }
        Constant::PhantomData => "phantomdata".to_string(),
    }
}

// `FuncId` is referenced in `Call` by id, but fingerprinted by name above.
// Import kept explicit so a tighter follow-up doesn't drop it.
const _FN_ID_REF: fn(&FuncId) -> u32 = |f| f.0;

// -----------------------------------------------------------------------------
// Rendering (for `Replaced.before/after` strings and `to_text`)
// -----------------------------------------------------------------------------

fn render_inst(m: &Module, node: &InstrNode, opts: DiffOptions) -> String {
    // Deliberately concise; we render the same structural shape used for
    // fingerprinting but through the module's display/debug in a way that
    // humans can scan. For stability across platforms we go through our
    // own formatter, not `Debug`.
    let mut s = render_inst_core(m, &node.inst);
    if !opts.ignore_proofs && !node.proofs.is_empty() {
        s.push_str(" !{");
        for (i, p) in node.proofs.iter().enumerate() {
            if i > 0 {
                s.push(',');
            }
            s.push_str(&fp_proof(p));
        }
        s.push('}');
    }
    if !opts.ignore_proofs && node.proof_context.is_some() {
        let _ = write!(
            s,
            " ctx{{{}}}",
            fp_proof_context(m, node.proof_context.as_ref())
        );
    }
    s
}

fn render_inst_core(m: &Module, inst: &Inst) -> String {
    // Use our structural format (without canonical renumbering maps).
    // Operand ValueIds / BlockIds are rendered as raw indices here since
    // the maps only make sense inside a diffing pass.
    let mut s = String::new();
    match inst {
        Inst::BinOp { op, ty, lhs, rhs } => {
            let _ = write!(
                s,
                "binop {:?} {} %{} %{}",
                op,
                render_ty(m, ty),
                lhs.0,
                rhs.0
            );
        }
        Inst::SeqMapAddK { ty, seq, k } => {
            let _ = write!(s, "seq_map_add_k {} %{} {k}", render_ty(m, ty), seq.0);
        }
        Inst::SeqMapNot { ty, seq } => {
            let _ = write!(s, "seq_map_not {} %{}", render_ty(m, ty), seq.0);
        }
        Inst::SeqMap { ty, seq, fwd } => {
            let name = m
                .functions
                .iter()
                .find(|f| f.id == *fwd)
                .map(|f| f.name.as_str())
                .unwrap_or("<unknown>");
            let _ = write!(s, "seq_map {} %{} @{name}", render_ty(m, ty), seq.0);
        }
        Inst::UnOp { op, ty, operand } => {
            let _ = write!(s, "unop {:?} {} %{}", op, render_ty(m, ty), operand.0);
        }
        Inst::Overflow { op, ty, lhs, rhs } => {
            let _ = write!(
                s,
                "overflow {:?} {} %{} %{}",
                op,
                render_ty(m, ty),
                lhs.0,
                rhs.0
            );
        }
        Inst::ICmp { op, ty, lhs, rhs } => {
            let _ = write!(
                s,
                "icmp {:?} {} %{} %{}",
                op,
                render_ty(m, ty),
                lhs.0,
                rhs.0
            );
        }
        Inst::FCmp { op, ty, lhs, rhs } => {
            let _ = write!(
                s,
                "fcmp {:?} {} %{} %{}",
                op,
                render_ty(m, ty),
                lhs.0,
                rhs.0
            );
        }
        Inst::Cast {
            op,
            src_ty,
            dst_ty,
            operand,
        } => {
            let _ = write!(
                s,
                "cast {:?} {} -> {} %{}",
                op,
                render_ty(m, src_ty),
                render_ty(m, dst_ty),
                operand.0
            );
        }
        Inst::Load { ty, ptr, .. } => {
            let _ = write!(s, "load {} %{}", render_ty(m, ty), ptr.0);
        }
        Inst::Store { ty, ptr, value, .. } => {
            let _ = write!(s, "store {} %{} %{}", render_ty(m, ty), ptr.0, value.0);
        }
        Inst::Alloca { ty, .. } => {
            let _ = write!(s, "alloca {}", render_ty(m, ty));
        }
        Inst::HeapAlloc { ty, origin, .. } => {
            let _ = write!(s, "heap_alloc {:?} {}", origin, render_ty(m, ty));
        }
        Inst::GEP {
            pointee_ty,
            base,
            indices,
            inbounds,
        } => {
            let mut rest = String::new();
            for i in indices {
                let _ = write!(rest, " %{}", i.0);
            }
            let ib = if *inbounds { " inbounds" } else { "" };
            let _ = write!(
                s,
                "gep{} {} %{}{}",
                ib,
                render_ty(m, pointee_ty),
                base.0,
                rest
            );
        }
        Inst::PtrData { ptr_ty, ptr } => {
            let _ = write!(s, "ptr.data {} %{}", render_ty(m, ptr_ty), ptr.0);
        }
        Inst::PtrMetadata {
            ptr_ty,
            metadata_ty,
            ptr,
        } => {
            let _ = write!(
                s,
                "ptr.metadata {} %{} -> {}",
                render_ty(m, ptr_ty),
                ptr.0,
                render_ty(m, metadata_ty)
            );
        }
        Inst::PtrFromParts {
            ptr_ty,
            metadata_ty,
            data,
            metadata,
        } => {
            let _ = write!(
                s,
                "ptr.from_parts {} ptr %{} {} %{}",
                render_ty(m, ptr_ty),
                data.0,
                render_ty(m, metadata_ty),
                metadata.0
            );
        }
        Inst::AtomicLoad { ty, ptr, ordering } => {
            let _ = write!(
                s,
                "atomic.load {} %{} {:?}",
                render_ty(m, ty),
                ptr.0,
                ordering
            );
        }
        Inst::AtomicStore {
            ty,
            ptr,
            value,
            ordering,
        } => {
            let _ = write!(
                s,
                "atomic.store {} %{} %{} {:?}",
                render_ty(m, ty),
                ptr.0,
                value.0,
                ordering
            );
        }
        Inst::AtomicRMW {
            op,
            ty,
            ptr,
            value,
            ordering,
        } => {
            let _ = write!(
                s,
                "atomic.rmw {:?} {} %{} %{} {:?}",
                op,
                render_ty(m, ty),
                ptr.0,
                value.0,
                ordering
            );
        }
        Inst::CmpXchg {
            ty,
            ptr,
            expected,
            desired,
            success,
            failure,
        } => {
            let _ = write!(
                s,
                "cmpxchg {} %{} %{} %{} {:?} {:?}",
                render_ty(m, ty),
                ptr.0,
                expected.0,
                desired.0,
                success,
                failure
            );
        }
        Inst::Fence { ordering } => {
            let _ = write!(s, "fence {:?}", ordering);
        }
        Inst::Br { target, args } => {
            let mut rest = String::new();
            for a in args {
                let _ = write!(rest, " %{}", a.0);
            }
            let _ = write!(s, "br b{}{}", target.0, rest);
        }
        Inst::CondBr {
            cond,
            then_target,
            then_args,
            else_target,
            else_args,
        } => {
            let mut ts = String::new();
            for a in then_args {
                let _ = write!(ts, " %{}", a.0);
            }
            let mut es = String::new();
            for a in else_args {
                let _ = write!(es, " %{}", a.0);
            }
            let _ = write!(
                s,
                "cond_br %{} b{}{} b{}{}",
                cond.0, then_target.0, ts, else_target.0, es
            );
        }
        Inst::Switch {
            value,
            default,
            default_args,
            cases,
            ..
        } => {
            let mut da = String::new();
            for a in default_args {
                let _ = write!(da, " %{}", a.0);
            }
            let _ = write!(s, "switch %{} default b{}{}", value.0, default.0, da);
            for c in cases {
                let mut cs = String::new();
                for a in &c.args {
                    let _ = write!(cs, " %{}", a.0);
                }
                let _ = write!(
                    s,
                    ", case {} b{}{}",
                    render_constant(m, &c.value),
                    c.target.0,
                    cs
                );
                let _: &SwitchCase = c;
            }
        }
        Inst::Call { callee, args } => {
            let name = m
                .functions
                .iter()
                .find(|f| f.id == *callee)
                .map(|f| f.name.as_str())
                .unwrap_or("<unknown>");
            let mut rest = String::new();
            for a in args {
                let _ = write!(rest, " %{}", a.0);
            }
            let _ = write!(s, "call @{name}{rest}");
        }
        Inst::CallIndirect {
            callee,
            sig,
            args,
            calling_conv,
        } => {
            let mut rest = String::new();
            for a in args {
                let _ = write!(rest, " %{}", a.0);
            }
            let _ = write!(
                s,
                "call_indirect %{} sig={} cc={calling_conv}{rest}",
                callee.0,
                fp_func_ty_ref(m, *sig)
            );
        }
        Inst::Return { values } => {
            let mut rest = String::new();
            for v in values {
                let _ = write!(rest, " %{}", v.0);
            }
            let _ = write!(s, "return{rest}");
        }
        Inst::ExtractField {
            ty,
            aggregate,
            field,
        } => {
            let _ = write!(
                s,
                "extractfield {} %{} .{}",
                render_ty(m, ty),
                aggregate.0,
                field
            );
        }
        Inst::InsertField {
            ty,
            aggregate,
            field,
            value,
        } => {
            let _ = write!(
                s,
                "insertfield {} %{} .{} %{}",
                render_ty(m, ty),
                aggregate.0,
                field,
                value.0
            );
        }
        Inst::ExtractElement { ty, array, index } => {
            let _ = write!(
                s,
                "extractelem {} %{} %{}",
                render_ty(m, ty),
                array.0,
                index.0
            );
        }
        Inst::InsertElement {
            ty,
            array,
            index,
            value,
        } => {
            let _ = write!(
                s,
                "insertelem {} %{} %{} %{}",
                render_ty(m, ty),
                array.0,
                index.0,
                value.0
            );
        }
        Inst::Const { ty, value } => {
            let _ = write!(
                s,
                "const {} = {}",
                render_ty(m, ty),
                render_constant(m, value)
            );
        }
        Inst::NullPtr => s.push_str("nullptr"),
        Inst::GlobalAddr { global } => {
            let _ = write!(s, "global_addr @global.{}", global.index());
        }
        Inst::Undef { ty } => {
            let _ = write!(s, "undef {}", render_ty(m, ty));
        }
        Inst::Assume { cond } => {
            let _ = write!(s, "assume %{}", cond.0);
        }
        Inst::Assert { cond } => {
            let _ = write!(s, "assert %{}", cond.0);
        }
        Inst::Unreachable => s.push_str("unreachable"),
        Inst::Copy { ty, operand } => {
            let _ = write!(s, "copy {} %{}", render_ty(m, ty), operand.0);
        }
        Inst::Select {
            ty,
            cond,
            then_val,
            else_val,
        } => {
            let _ = write!(
                s,
                "select {} %{} ? %{} : %{}",
                render_ty(m, ty),
                cond.0,
                then_val.0,
                else_val.0
            );
        }
        Inst::Borrow { ptr } => {
            let _ = write!(s, "borrow %{}", ptr.0);
        }
        Inst::BorrowMut { ptr } => {
            let _ = write!(s, "borrow_mut %{}", ptr.0);
        }
        Inst::EndBorrow { borrow_ptr } => {
            let _ = write!(s, "end_borrow %{}", borrow_ptr.0);
        }
        Inst::Retain { ptr } => {
            let _ = write!(s, "retain %{}", ptr.0);
        }
        Inst::Release { ptr } => {
            let _ = write!(s, "release %{}", ptr.0);
        }
        Inst::IsUnique { ptr } => {
            let _ = write!(s, "is_unique %{}", ptr.0);
        }
        Inst::Dealloc { ptr } => {
            let _ = write!(s, "dealloc %{}", ptr.0);
        }
        Inst::OpenFrame { def } => {
            let _ = write!(s, "open_frame #{} {}", def.id.0, def.name);
        }
        Inst::BindSlot { frame, slot, value } => {
            let _ = write!(s, "bind_slot %{} .{} %{}", frame.0, slot, value.0);
        }
        Inst::LoadSlot { frame, slot, ty } => {
            let _ = write!(s, "load_slot %{} .{} {}", frame.0, slot, render_ty(m, ty));
        }
        Inst::CloseFrame { frame } => {
            let _ = write!(s, "close_frame %{}", frame.0);
        }
        Inst::CoroSuspend {
            frame,
            state_slot,
            next_state,
            value,
        } => {
            let _ = write!(
                s,
                "coro_suspend %{}, {state_slot}, {next_state}, %{}",
                frame.0, value.0
            );
        }
        Inst::Invoke {
            callee,
            args,
            normal_dest,
            normal_args,
            unwind_dest,
        } => {
            let name = m
                .functions
                .iter()
                .find(|f| f.id == *callee)
                .map(|f| f.name.as_str())
                .unwrap_or("<unknown>");
            let mut a = String::new();
            for (i, arg) in args.iter().enumerate() {
                let _ = write!(a, "{}%{}", if i > 0 { ", " } else { "" }, arg.0);
            }
            let mut na = String::new();
            for (i, arg) in normal_args.iter().enumerate() {
                let _ = write!(na, "{}%{}", if i > 0 { ", " } else { "" }, arg.0);
            }
            let _ = write!(
                s,
                "invoke @{name}({a}) to bb{}({na}) unwind bb{}",
                normal_dest.index(),
                unwind_dest.index()
            );
        }
        Inst::LandingPad {
            is_cleanup,
            catch_type_indices,
        } => {
            let _ = write!(s, "landingpad");
            if *is_cleanup {
                let _ = write!(s, " cleanup");
            }
            if !catch_type_indices.is_empty() {
                let _ = write!(s, " catch");
                for (i, idx) in catch_type_indices.iter().enumerate() {
                    let _ = write!(s, "{} {idx}", if i > 0 { "," } else { "" });
                }
            }
        }
        Inst::Resume { exn } => {
            let _ = write!(s, "resume %{}", exn.0);
        }
        Inst::DialectOp(d) => {
            let _ = write!(s, "dialect {}.{} v{}", d.dialect, d.op, d.version);
        }
    }
    s
}

fn render_ty(m: &Module, t: &Ty) -> String {
    // We use the structural fingerprint as the display form for diffs.
    // It's unambiguous and doesn't depend on arena ids.
    fp_ty(m, t)
}

fn render_constant(m: &Module, c: &Constant) -> String {
    fp_constant(m, c)
}

// -----------------------------------------------------------------------------
// Output formatting
// -----------------------------------------------------------------------------

impl Diff {
    /// Render the diff as human-readable unified-diff-style text.
    ///
    /// Empty output when `self.is_empty()`.
    pub fn to_text(&self) -> String {
        if self.is_empty() {
            return String::new();
        }
        let mut s = String::new();
        let _ = writeln!(s, "--- {}\n+++ {}", self.module_name_a, self.module_name_b);
        for c in &self.changes {
            match c {
                FuncChange::Added { name } => {
                    let _ = writeln!(s, "+ function @{name}");
                }
                FuncChange::Removed { name } => {
                    let _ = writeln!(s, "- function @{name}");
                }
                FuncChange::Changed {
                    name,
                    proof_changes,
                    block_changes,
                    meta_changes,
                } => {
                    let _ = writeln!(s, "~ function @{name}");
                    for mc in meta_changes {
                        let _ = writeln!(s, "    ~ {}: {} -> {}", mc.field, mc.before, mc.after);
                    }
                    for pc in proof_changes {
                        match pc {
                            ProofChange::Added { name } => {
                                let _ = writeln!(s, "    + proof {name}");
                            }
                            ProofChange::Removed { name } => {
                                let _ = writeln!(s, "    - proof {name}");
                            }
                        }
                    }
                    for bc in block_changes {
                        match bc {
                            BlockChange::Added { visit } => {
                                let _ = writeln!(s, "    + block (visit {visit})");
                            }
                            BlockChange::Removed { visit } => {
                                let _ = writeln!(s, "    - block (visit {visit})");
                            }
                            BlockChange::StructureDiffers { visit, detail } => {
                                let _ = writeln!(s, "    ~ block (visit {visit}): {detail}");
                            }
                            BlockChange::InstrDiff {
                                visit,
                                instr_changes,
                            } => {
                                let _ = writeln!(s, "    ~ block (visit {visit})");
                                for ic in instr_changes {
                                    match ic {
                                        InstrChange::Added { index, summary } => {
                                            let _ = writeln!(s, "        + [{index}] {summary}");
                                        }
                                        InstrChange::Removed { index, summary } => {
                                            let _ = writeln!(s, "        - [{index}] {summary}");
                                        }
                                        InstrChange::Replaced {
                                            index,
                                            before,
                                            after,
                                        } => {
                                            let _ = writeln!(s, "        - [{index}] {before}");
                                            let _ = writeln!(s, "        + [{index}] {after}");
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        for psc in &self.proof_state_changes {
            match psc {
                ProofStateChange::ObligationAdded { obligation, status } => {
                    let _ = writeln!(s, "+ obligation {obligation} [{status}]");
                }
                ProofStateChange::ObligationRemoved { obligation, status } => {
                    let _ = writeln!(s, "- obligation {obligation} [{status}]");
                }
                ProofStateChange::ObligationStatusChanged {
                    obligation,
                    before,
                    after,
                } => {
                    let _ = writeln!(s, "~ obligation {obligation}: {before} -> {after}");
                }
                ProofStateChange::CertificateAdded { certificate } => {
                    let _ = writeln!(s, "+ certificate {certificate}");
                }
                ProofStateChange::CertificateRemoved { certificate } => {
                    let _ = writeln!(s, "- certificate {certificate}");
                }
            }
        }
        s
    }

    /// Render the diff as JSON.
    ///
    /// # Schema (version 1)
    ///
    /// ```text
    /// {
    ///   "schema_version": 1,
    ///   "module_a": "<name>",
    ///   "module_b": "<name>",
    ///   "changes": [
    ///     { "kind": "func_added",   "name": "<fn>" },
    ///     { "kind": "func_removed", "name": "<fn>" },
    ///     { "kind": "func_changed",
    ///       "name": "<fn>",
    ///       "meta": [
    ///         { "field": "producer", "before": "...", "after": "..." }
    ///       ],
    ///       "proofs": [
    ///         { "kind": "proof_added",   "name": "..." },
    ///         { "kind": "proof_removed", "name": "..." }
    ///       ],
    ///       "blocks": [
    ///         { "kind": "block_added",   "visit": <n> },
    ///         { "kind": "block_removed", "visit": <n> },
    ///         { "kind": "block_structure", "visit": <n>, "detail": "..." },
    ///         { "kind": "block_instrs",  "visit": <n>,
    ///           "instrs": [
    ///             { "kind": "added",    "index": <n>, "summary": "..." },
    ///             { "kind": "removed",  "index": <n>, "summary": "..." },
    ///             { "kind": "replaced", "index": <n>,
    ///               "before": "...", "after": "..." }
    ///           ]
    ///         }
    ///       ]
    ///     }
    ///   ],
    ///   "proof_state": [
    ///     { "kind": "obligation_added",   "obligation": "...", "status": "..." },
    ///     { "kind": "obligation_removed", "obligation": "...", "status": "..." },
    ///     { "kind": "obligation_status_changed",
    ///       "obligation": "...", "before": "...", "after": "..." },
    ///     { "kind": "certificate_added",   "certificate": "..." },
    ///     { "kind": "certificate_removed", "certificate": "..." }
    ///   ]
    /// }
    /// ```
    pub fn to_json(&self) -> String {
        let mut s = String::new();
        s.push('{');
        let _ = write!(s, "\"schema_version\":1,");
        let _ = write!(s, "\"module_a\":{},", json_string(&self.module_name_a));
        let _ = write!(s, "\"module_b\":{},", json_string(&self.module_name_b));
        s.push_str("\"changes\":[");
        for (i, c) in self.changes.iter().enumerate() {
            if i > 0 {
                s.push(',');
            }
            match c {
                FuncChange::Added { name } => {
                    let _ = write!(
                        s,
                        "{{\"kind\":\"func_added\",\"name\":{}}}",
                        json_string(name)
                    );
                }
                FuncChange::Removed { name } => {
                    let _ = write!(
                        s,
                        "{{\"kind\":\"func_removed\",\"name\":{}}}",
                        json_string(name)
                    );
                }
                FuncChange::Changed {
                    name,
                    proof_changes,
                    block_changes,
                    meta_changes,
                } => {
                    let _ = write!(
                        s,
                        "{{\"kind\":\"func_changed\",\"name\":{},\"meta\":[",
                        json_string(name)
                    );
                    for (mi, mc) in meta_changes.iter().enumerate() {
                        if mi > 0 {
                            s.push(',');
                        }
                        let _ = write!(
                            s,
                            "{{\"field\":{},\"before\":{},\"after\":{}}}",
                            json_string(&mc.field),
                            json_string(&mc.before),
                            json_string(&mc.after)
                        );
                    }
                    s.push_str("],\"proofs\":[");
                    for (pi, pc) in proof_changes.iter().enumerate() {
                        if pi > 0 {
                            s.push(',');
                        }
                        match pc {
                            ProofChange::Added { name } => {
                                let _ = write!(
                                    s,
                                    "{{\"kind\":\"proof_added\",\"name\":{}}}",
                                    json_string(name)
                                );
                            }
                            ProofChange::Removed { name } => {
                                let _ = write!(
                                    s,
                                    "{{\"kind\":\"proof_removed\",\"name\":{}}}",
                                    json_string(name)
                                );
                            }
                        }
                    }
                    s.push_str("],\"blocks\":[");
                    for (bi, bc) in block_changes.iter().enumerate() {
                        if bi > 0 {
                            s.push(',');
                        }
                        match bc {
                            BlockChange::Added { visit } => {
                                let _ = write!(s, "{{\"kind\":\"block_added\",\"visit\":{visit}}}");
                            }
                            BlockChange::Removed { visit } => {
                                let _ =
                                    write!(s, "{{\"kind\":\"block_removed\",\"visit\":{visit}}}");
                            }
                            BlockChange::StructureDiffers { visit, detail } => {
                                let _ = write!(
                                    s,
                                    "{{\"kind\":\"block_structure\",\"visit\":{visit},\"detail\":{}}}",
                                    json_string(detail)
                                );
                            }
                            BlockChange::InstrDiff {
                                visit,
                                instr_changes,
                            } => {
                                let _ = write!(
                                    s,
                                    "{{\"kind\":\"block_instrs\",\"visit\":{visit},\"instrs\":["
                                );
                                for (ii, ic) in instr_changes.iter().enumerate() {
                                    if ii > 0 {
                                        s.push(',');
                                    }
                                    match ic {
                                        InstrChange::Added { index, summary } => {
                                            let _ = write!(
                                                s,
                                                "{{\"kind\":\"added\",\"index\":{index},\"summary\":{}}}",
                                                json_string(summary)
                                            );
                                        }
                                        InstrChange::Removed { index, summary } => {
                                            let _ = write!(
                                                s,
                                                "{{\"kind\":\"removed\",\"index\":{index},\"summary\":{}}}",
                                                json_string(summary)
                                            );
                                        }
                                        InstrChange::Replaced {
                                            index,
                                            before,
                                            after,
                                        } => {
                                            let _ = write!(
                                                s,
                                                "{{\"kind\":\"replaced\",\"index\":{index},\"before\":{},\"after\":{}}}",
                                                json_string(before),
                                                json_string(after)
                                            );
                                        }
                                    }
                                }
                                s.push_str("]}");
                            }
                        }
                    }
                    s.push_str("]}");
                }
            }
        }
        s.push_str("],\"proof_state\":[");
        for (i, psc) in self.proof_state_changes.iter().enumerate() {
            if i > 0 {
                s.push(',');
            }
            match psc {
                ProofStateChange::ObligationAdded { obligation, status } => {
                    let _ = write!(
                        s,
                        "{{\"kind\":\"obligation_added\",\"obligation\":{},\"status\":{}}}",
                        json_string(obligation),
                        json_string(status)
                    );
                }
                ProofStateChange::ObligationRemoved { obligation, status } => {
                    let _ = write!(
                        s,
                        "{{\"kind\":\"obligation_removed\",\"obligation\":{},\"status\":{}}}",
                        json_string(obligation),
                        json_string(status)
                    );
                }
                ProofStateChange::ObligationStatusChanged {
                    obligation,
                    before,
                    after,
                } => {
                    let _ = write!(
                        s,
                        "{{\"kind\":\"obligation_status_changed\",\"obligation\":{},\"before\":{},\"after\":{}}}",
                        json_string(obligation),
                        json_string(before),
                        json_string(after)
                    );
                }
                ProofStateChange::CertificateAdded { certificate } => {
                    let _ = write!(
                        s,
                        "{{\"kind\":\"certificate_added\",\"certificate\":{}}}",
                        json_string(certificate)
                    );
                }
                ProofStateChange::CertificateRemoved { certificate } => {
                    let _ = write!(
                        s,
                        "{{\"kind\":\"certificate_removed\",\"certificate\":{}}}",
                        json_string(certificate)
                    );
                }
            }
        }
        s.push(']');
        s.push('}');
        s
    }
}

fn json_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

// -----------------------------------------------------------------------------
// Tests
// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        Block, CallingConv, Function, Linkage, Module,
        inst::{BinOp, Inst, SwitchCase},
        node::InstrNode,
        ty::{
            EnumDef, EnumLayoutDescriptor, EnumTagEncoding, EnumVariant, FieldDef, FuncTy,
            RecordDef, StructDef, StructRepr, Ty,
        },
        value::{BlockId, EnumId, FuncId, FuncTyId, RecordId, StructId, ValueId},
    };

    /// R3 #8: a proved-but-empty summary must NOT fingerprint to the same `∅` marker
    /// as `None` (or as an UNPROVED empty summary), so a `None -> Some(proved)` or a
    /// `proved=false -> true` transition is reported by the diff.
    #[test]
    fn summary_fp_distinguishes_proved_empty_from_none() {
        let none_fp = summary_fp(None);
        let unproved_empty = crate::FunctionSummary::default();
        let proved_empty = crate::FunctionSummary {
            proved: true,
            ..Default::default()
        };
        assert_eq!(
            summary_fp(Some(&unproved_empty)),
            none_fp,
            "unproved empty ≡ None"
        );
        assert_ne!(
            summary_fp(Some(&proved_empty)),
            none_fp,
            "a proved (empty) summary must be distinguishable from None"
        );
    }

    /// v23: a producer-provenance flip on an otherwise-identical function is a
    /// real change — reported via `meta_changes`, and NOT suppressed by
    /// `--ignore-proofs` (provenance is metadata, not proof coverage).
    #[test]
    fn producer_change_is_reported_and_survives_ignore_proofs() {
        let a = single_return_module("m", 0, 0);
        let mut b_mod = single_return_module("m", 0, 0);
        b_mod.functions[0].producer = Some(crate::Producer::Clean);

        for opts in [
            DiffOptions::default(),
            DiffOptions {
                ignore_proofs: true,
            },
        ] {
            let d = diff_with(&a, &b_mod, opts);
            assert!(
                !d.is_empty(),
                "producer flip must surface (ignore_proofs={})",
                opts.ignore_proofs
            );
            match &d.changes[0] {
                FuncChange::Changed {
                    name, meta_changes, ..
                } => {
                    assert_eq!(name, "main");
                    assert_eq!(meta_changes.len(), 1);
                    assert_eq!(meta_changes[0].field, "producer");
                    assert_eq!(meta_changes[0].before, "-");
                    assert_eq!(meta_changes[0].after, "clean");
                }
                other => panic!("expected Changed, got {other:?}"),
            }
            let text = d.to_text();
            assert!(text.contains("~ producer: - -> clean"), "{text}");
            let json = d.to_json();
            assert!(
                json.contains(
                    "\"meta\":[{\"field\":\"producer\",\"before\":\"-\",\"after\":\"clean\"}]"
                ),
                "{json}"
            );
        }

        // Same producer on both sides: no change.
        let mut a2 = single_return_module("m", 0, 0);
        a2.functions[0].producer = Some(crate::Producer::Clean);
        assert!(diff(&a2, &b_mod).is_empty());
    }

    #[test]
    fn source_provenance_change_is_reported_and_survives_ignore_proofs() {
        let a = single_return_module("m", 0, 0);
        let mut b_mod = a.clone();
        b_mod.functions[0].source_provenance = Some(crate::SourceProvenance::new(
            crate::proof::ProofDigest::sha256([1; 32]),
            crate::proof::ProofDigest::sha256([2; 32]),
            Vec::new(),
        ));

        for opts in [
            DiffOptions::default(),
            DiffOptions {
                ignore_proofs: true,
            },
        ] {
            let result = diff_with(&a, &b_mod, opts);
            assert_eq!(result.changes.len(), 1);
            let FuncChange::Changed { meta_changes, .. } = &result.changes[0] else {
                panic!("expected changed function");
            };
            assert_eq!(meta_changes.len(), 1);
            assert_eq!(meta_changes[0].field, "source_provenance");
            assert_eq!(meta_changes[0].before, "-");
            assert!(meta_changes[0].after.contains("schema=1"));
        }
    }

    /// v32/v33 debug names and lexical scopes are claim-style diagnostics,
    /// like source spans. They do not change execution or proof authority and
    /// therefore stay outside the semantic diff.
    #[test]
    fn debug_metadata_is_ignored_as_cosmetic() {
        let a = single_return_module("m", 0, 0);
        let mut b_mod = a.clone();
        let file = b_mod.intern_file("src/main.rs");
        let function = &mut b_mod.functions[0];
        function.value_names = Some(vec![(v(0), "unit value".to_string())]);
        function.scopes = Some(vec![crate::ScopeData {
            parent: None,
            span: Some(crate::SourceSpan {
                file,
                line: 1,
                col: 0,
            }),
        }]);
        function.blocks[0].body[0].span = Some(crate::SourceSpan {
            file,
            line: 1,
            col: 4,
        });
        function.blocks[0].body[0].scope = Some(0);

        for opts in [
            DiffOptions::default(),
            DiffOptions {
                ignore_proofs: true,
            },
        ] {
            let d = diff_with(&a, &b_mod, opts);
            assert!(
                d.is_empty(),
                "debug metadata must stay cosmetic (ignore_proofs={}): {}",
                opts.ignore_proofs,
                d.to_text()
            );
        }
    }

    // Helpers --------------------------------------------------------------

    fn make_unit_ft(m: &mut Module) -> FuncTyId {
        m.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::Unit],
            is_vararg: false,
        })
    }

    fn v(n: u32) -> ValueId {
        ValueId::new(n)
    }

    fn b(n: u32) -> BlockId {
        BlockId::new(n)
    }

    /// Build a module with a single `@main` function that returns unit.
    fn single_return_module(name: &str, value_base: u32, block_base: u32) -> Module {
        let mut m = Module::new(name);
        let ft = make_unit_ft(&mut m);
        let entry = b(block_base);
        let mut f = Function::new(FuncId::new(0), "main", ft, entry);
        f.calling_conv = CallingConv::C;
        f.linkage = Linkage::External;
        let mut blk = Block::new(entry);
        // %N = const Unit = Unit
        blk.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::Unit,
                value: Constant::Aggregate(vec![]),
            })
            .with_result(v(value_base)),
        );
        blk.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        f.blocks.push(blk);
        m.add_function(f);
        m
    }

    // 1. same module produces empty diff ------------------------------------

    #[test]
    fn same_module_diffs_empty() {
        let a = single_return_module("m", 0, 0);
        let d = diff(&a, &a);
        assert!(d.is_empty(), "{}", d.to_text());
        assert_eq!(d.exit_code(), 0);
    }

    // 2. id renumbering produces no diff ------------------------------------

    #[test]
    fn id_renumbering_produces_no_diff() {
        let a = single_return_module("m", 0, 0);
        let b = single_return_module("m", 42, 17);
        let d = diff(&a, &b);
        assert!(d.is_empty(), "{}", d.to_text());
    }

    // 2b. a changed separate-compilation contract is reported (and suppressed
    //     under ignore_proofs) -------------------------------------------------

    #[test]
    fn function_summary_change_is_a_proof_change() {
        use crate::{FunctionSummary, ProofFormula};
        let a = single_return_module("m", 0, 0);
        let mut b = single_return_module("m", 0, 0);
        b.functions[0].summary = Some(
            FunctionSummary::new()
                .ensuring(ProofFormula::smtlib2("(> result 0)", "Bool"))
                .proved(),
        );
        // Default options: the contract change shows up as a function change.
        let d = diff(&a, &b);
        assert!(!d.is_empty(), "a contract change must be reported");
        // ignore_proofs suppresses it (the contract is proof-ish).
        let d2 = diff_with(
            &a,
            &b,
            DiffOptions {
                ignore_proofs: true,
            },
        );
        assert!(
            d2.is_empty(),
            "ignore_proofs must suppress the contract change: {}",
            d2.to_text()
        );
    }

    // 3. declaration-order-only difference in functions --------------------

    #[test]
    fn declaration_order_produces_no_diff() {
        let mut m_a = Module::new("m");
        let ft = make_unit_ft(&mut m_a);
        // A declares foo then bar.
        for (idx, name) in [(0u32, "foo"), (1u32, "bar")].iter() {
            let mut f = Function::new(FuncId::new(*idx), *name, ft, b(0));
            let mut blk = Block::new(b(0));
            blk.body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            f.blocks.push(blk);
            m_a.add_function(f);
        }

        let mut m_b = Module::new("m");
        let ft = make_unit_ft(&mut m_b);
        // B declares bar then foo (and also renumbers ids).
        for (idx, name) in [(5u32, "bar"), (99u32, "foo")].iter() {
            let mut f = Function::new(FuncId::new(*idx), *name, ft, b(7));
            let mut blk = Block::new(b(7));
            blk.body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            f.blocks.push(blk);
            m_b.add_function(f);
        }

        let d = diff(&m_a, &m_b);
        assert!(d.is_empty(), "{}", d.to_text());
    }

    // 4. added instruction is reported ------------------------------------

    #[test]
    fn added_instruction_reports_exactly_that_instruction() {
        let mut a = Module::new("m");
        let ft_i = a.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let mut fa = Function::new(FuncId::new(0), "main", ft_i, b(0));
        let mut blk = Block::new(b(0));
        blk.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(v(0)),
        );
        blk.body
            .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
        fa.blocks.push(blk);
        a.add_function(fa);

        let mut b_mod = Module::new("m");
        let ft_i = b_mod.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let mut fb = Function::new(FuncId::new(0), "main", ft_i, b(0));
        let mut blk = Block::new(b(0));
        blk.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(v(0)),
        );
        blk.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(0),
                rhs: v(0),
            })
            .with_result(v(1)),
        );
        blk.body
            .push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
        fb.blocks.push(blk);
        b_mod.add_function(fb);

        let d = diff(&a, &b_mod);
        assert_eq!(d.changes.len(), 1);
        match &d.changes[0] {
            FuncChange::Changed {
                name,
                block_changes,
                ..
            } => {
                assert_eq!(name, "main");
                assert_eq!(block_changes.len(), 1);
                match &block_changes[0] {
                    BlockChange::InstrDiff {
                        visit,
                        instr_changes,
                    } => {
                        assert_eq!(*visit, 0);
                        // We expect the add inserted at position 1 AND the
                        // return to shift — so Replaced at index 1 + Added
                        // at index 2 (the return), OR an Added at index 1
                        // and a Replaced at index 2. Because the diff is
                        // positional, the most natural report is:
                        //   [1] Const is now BinOp (Replaced)
                        //   [2] nothing -> Return (Added)
                        // The first-block-instr-case is reported as either
                        // Replaced or Added; check the aggregate is sound.
                        assert!(
                            !instr_changes.is_empty(),
                            "expected instruction changes, got none"
                        );
                        // There must be exactly one extra instruction in B.
                        let mut added = 0i32;
                        let mut removed = 0i32;
                        let mut replaced = 0i32;
                        for ic in instr_changes {
                            match ic {
                                InstrChange::Added { .. } => added += 1,
                                InstrChange::Removed { .. } => removed += 1,
                                InstrChange::Replaced { .. } => replaced += 1,
                            }
                        }
                        assert_eq!(added - removed, 1, "net change should be +1 instruction");
                        assert!(added + replaced >= 1);
                    }
                    other => panic!("expected InstrDiff, got {other:?}"),
                }
            }
            other => panic!("expected Changed, got {other:?}"),
        }
        assert_eq!(d.exit_code(), 1);
    }

    // 5. JSON output is valid JSON ----------------------------------------

    #[test]
    fn json_output_is_valid_json() {
        let a = single_return_module("m", 0, 0);
        let mut b_mod = single_return_module("m", 0, 0);
        // Force a difference: add a second function.
        let ft = make_unit_ft(&mut b_mod);
        let mut f = Function::new(FuncId::new(99), "extra", ft, b(0));
        let mut blk = Block::new(b(0));
        blk.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        f.blocks.push(blk);
        b_mod.add_function(f);

        let d = diff(&a, &b_mod);
        let j = d.to_json();
        // Round-trip through serde_json to prove it parses.
        let _v: serde_json::Value = serde_json::from_str(&j).expect("to_json must emit valid JSON");
    }

    // 6. struct id renumbering produces no diff ----------------------------

    #[test]
    fn struct_id_renumbering_produces_no_diff() {
        // Module A: one struct { x: i32, y: i32 }; main returns unit.
        let mut a = Module::new("m");
        let sa = a.add_struct(StructDef {
            id: StructId::new(3),
            name: "P".into(),
            fields: vec![
                FieldDef {
                    name: "x".into(),
                    ty: Ty::I32,
                    offset: None,
                },
                FieldDef {
                    name: "y".into(),
                    ty: Ty::I32,
                    offset: None,
                },
            ],
            size: None,
            align: None,
            repr: Default::default(),
        });
        let ft = a.add_func_type(FuncTy {
            params: vec![Ty::Struct(sa)],
            returns: vec![Ty::Unit],
            is_vararg: false,
        });
        let mut f = Function::new(FuncId::new(0), "main", ft, b(0));
        let mut blk = Block::new(b(0));
        blk.params.push((v(0), Ty::Struct(sa)));
        blk.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        f.blocks.push(blk);
        a.add_function(f);

        // Module B: same struct with id=17 instead of 3.
        let mut b_mod = Module::new("m");
        let sb = b_mod.add_struct(StructDef {
            id: StructId::new(17),
            name: "P".into(),
            fields: vec![
                FieldDef {
                    name: "x".into(),
                    ty: Ty::I32,
                    offset: None,
                },
                FieldDef {
                    name: "y".into(),
                    ty: Ty::I32,
                    offset: None,
                },
            ],
            size: None,
            align: None,
            repr: Default::default(),
        });
        let ft = b_mod.add_func_type(FuncTy {
            params: vec![Ty::Struct(sb)],
            returns: vec![Ty::Unit],
            is_vararg: false,
        });
        let mut f = Function::new(FuncId::new(0), "main", ft, b(0));
        let mut blk = Block::new(b(0));
        blk.params.push((v(0), Ty::Struct(sb)));
        blk.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        f.blocks.push(blk);
        b_mod.add_function(f);

        let d = diff(&a, &b_mod);
        assert!(d.is_empty(), "{}", d.to_text());
    }

    // 6b. struct repr difference IS a diff --------------------------------

    #[test]
    fn struct_repr_difference_produces_diff() {
        // Two modules whose only difference is a struct's ABI repr (C vs Rust).
        // size/align/name/fields all identical, but repr is part of the ABI
        // contract, so `trust-ir-diff` MUST report a change.
        fn module_with_repr(repr: StructRepr) -> Module {
            let mut m = Module::new("m");
            let s = m.add_struct(StructDef {
                id: StructId::new(0),
                name: "P".into(),
                fields: vec![FieldDef {
                    name: "x".into(),
                    ty: Ty::I32,
                    offset: None,
                }],
                size: Some(4),
                align: Some(4),
                repr,
            });
            let ft = m.add_func_type(FuncTy {
                params: vec![Ty::Struct(s)],
                returns: vec![Ty::Unit],
                is_vararg: false,
            });
            let mut f = Function::new(FuncId::new(0), "main", ft, b(0));
            let mut blk = Block::new(b(0));
            blk.params.push((v(0), Ty::Struct(s)));
            blk.body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            f.blocks.push(blk);
            m.add_function(f);
            m
        }

        let a = module_with_repr(StructRepr::C);
        let b_mod = module_with_repr(StructRepr::Rust);
        let d = diff(&a, &b_mod);
        assert!(
            !d.is_empty(),
            "differing struct repr (C vs Rust) must produce a diff"
        );
    }

    // 7. record id renumbering produces no diff ---------------------------

    #[test]
    fn record_id_renumbering_produces_no_diff() {
        let mut a = Module::new("m");
        let ra = a.add_record(RecordDef {
            id: RecordId::new(2),
            name: "R".into(),
            fields: vec![FieldDef {
                name: "a".into(),
                ty: Ty::I32,
                offset: None,
            }],
        });
        let ft = a.add_func_type(FuncTy {
            params: vec![Ty::Record(ra)],
            returns: vec![Ty::Unit],
            is_vararg: false,
        });
        let mut f = Function::new(FuncId::new(0), "main", ft, b(0));
        let mut blk = Block::new(b(0));
        blk.params.push((v(0), Ty::Record(ra)));
        blk.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        f.blocks.push(blk);
        a.add_function(f);

        let mut b_mod = Module::new("m");
        let rb = b_mod.add_record(RecordDef {
            id: RecordId::new(99),
            name: "R".into(),
            fields: vec![FieldDef {
                name: "a".into(),
                ty: Ty::I32,
                offset: None,
            }],
        });
        let ft = b_mod.add_func_type(FuncTy {
            params: vec![Ty::Record(rb)],
            returns: vec![Ty::Unit],
            is_vararg: false,
        });
        let mut f = Function::new(FuncId::new(0), "main", ft, b(0));
        let mut blk = Block::new(b(0));
        blk.params.push((v(0), Ty::Record(rb)));
        blk.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        f.blocks.push(blk);
        b_mod.add_function(f);

        let d = diff(&a, &b_mod);
        assert!(d.is_empty(), "{}", d.to_text());
    }

    // 8. block id renumbering produces no diff ----------------------------

    #[test]
    fn block_id_renumbering_produces_no_diff() {
        fn mk(name: &str, entry_id: u32, other_id: u32) -> Module {
            let mut m = Module::new(name);
            let ft = make_unit_ft(&mut m);
            let mut f = Function::new(FuncId::new(0), "main", ft, b(entry_id));
            // entry -> other -> return
            let mut entry = Block::new(b(entry_id));
            entry.body.push(InstrNode::new(Inst::Br {
                target: b(other_id),
                args: vec![],
            }));
            let mut other = Block::new(b(other_id));
            other
                .body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            f.blocks.push(entry);
            f.blocks.push(other);
            m.add_function(f);
            m
        }

        let a = mk("m", 0, 1);
        let b1 = mk("m", 50, 99);
        let d = diff(&a, &b1);
        assert!(d.is_empty(), "{}", d.to_text());
    }

    // 9. proof annotation with/without --ignore-proofs --------------------

    #[test]
    fn proof_added_without_flag_produces_diff() {
        let a = single_return_module("m", 0, 0);
        let mut b_mod = single_return_module("m", 0, 0);
        b_mod.functions[0].proofs.push(ProofAnnotation::Pure);

        let d = diff(&a, &b_mod);
        assert!(!d.is_empty(), "expected diff when proof differs");

        let d2 = diff_with(
            &a,
            &b_mod,
            DiffOptions {
                ignore_proofs: true,
            },
        );
        assert!(d2.is_empty(), "{}", d2.to_text());
    }

    #[test]
    fn instruction_level_proof_added_without_flag_produces_diff() {
        let a = single_return_module("m", 0, 0);
        let mut b_mod = single_return_module("m", 0, 0);
        // Attach InBounds to the first instruction of the first block.
        b_mod.functions[0].blocks[0].body[0]
            .proofs
            .push(ProofAnnotation::InBounds);

        let d = diff(&a, &b_mod);
        assert!(!d.is_empty());
        match &d.changes[0] {
            FuncChange::Changed { block_changes, .. } => {
                assert!(!block_changes.is_empty());
            }
            other => panic!("expected Changed, got {other:?}"),
        }

        let d2 = diff_with(
            &a,
            &b_mod,
            DiffOptions {
                ignore_proofs: true,
            },
        );
        assert!(d2.is_empty(), "{}", d2.to_text());
    }

    // 10. function added / removed are sorted -----------------------------

    #[test]
    fn function_added_and_removed_are_sorted() {
        // A has: aaa, bbb
        // B has: bbb, ccc
        // Expect: Removed("aaa") and Added("ccc") in sorted order.
        let mut a = Module::new("m");
        let ft = make_unit_ft(&mut a);
        for name in ["aaa", "bbb"] {
            let mut f = Function::new(FuncId::new(0), name, ft, b(0));
            let mut blk = Block::new(b(0));
            blk.body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            f.blocks.push(blk);
            a.add_function(f);
        }

        let mut b_mod = Module::new("m");
        let ft = make_unit_ft(&mut b_mod);
        for name in ["bbb", "ccc"] {
            let mut f = Function::new(FuncId::new(0), name, ft, b(0));
            let mut blk = Block::new(b(0));
            blk.body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            f.blocks.push(blk);
            b_mod.add_function(f);
        }

        let d = diff(&a, &b_mod);
        // Filter to names to check ordering.
        let names: Vec<&str> = d
            .changes
            .iter()
            .map(|c| match c {
                FuncChange::Added { name } => name.as_str(),
                FuncChange::Removed { name } => name.as_str(),
                FuncChange::Changed { name, .. } => name.as_str(),
            })
            .collect();
        assert_eq!(names, vec!["aaa", "ccc"]);
        // Confirm their kinds.
        assert!(matches!(&d.changes[0], FuncChange::Removed { .. }));
        assert!(matches!(&d.changes[1], FuncChange::Added { .. }));
    }

    // 11. block count mismatch reports block-level diff --------------------

    #[test]
    fn block_count_mismatch_reports_block_level_diff() {
        let mut a = Module::new("m");
        let ft = make_unit_ft(&mut a);
        let mut f = Function::new(FuncId::new(0), "main", ft, b(0));
        let mut blk = Block::new(b(0));
        blk.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        f.blocks.push(blk);
        a.add_function(f);

        let mut b_mod = Module::new("m");
        let ft = make_unit_ft(&mut b_mod);
        let mut f = Function::new(FuncId::new(0), "main", ft, b(0));
        // Two blocks: entry branches to other, which returns.
        let mut entry = Block::new(b(0));
        entry.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![],
        }));
        let mut other = Block::new(b(1));
        other
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        f.blocks.push(entry);
        f.blocks.push(other);
        b_mod.add_function(f);

        let d = diff(&a, &b_mod);
        assert!(!d.is_empty());
        match &d.changes[0] {
            FuncChange::Changed { block_changes, .. } => {
                assert!(
                    block_changes
                        .iter()
                        .any(|bc| matches!(bc, BlockChange::Added { .. })),
                    "expected a BlockChange::Added for the extra block"
                );
            }
            other => panic!("expected Changed, got {other:?}"),
        }
    }

    // 12. different binop reports replaced ---------------------------------

    #[test]
    fn different_binop_reports_replaced() {
        let mk = |op: BinOp| -> Module {
            let mut m = Module::new("m");
            let ft = m.add_func_type(FuncTy {
                params: vec![Ty::I32, Ty::I32],
                returns: vec![Ty::I32],
                is_vararg: false,
            });
            let mut f = Function::new(FuncId::new(0), "main", ft, b(0));
            let mut blk = Block::new(b(0));
            blk.params.push((v(0), Ty::I32));
            blk.params.push((v(1), Ty::I32));
            blk.body.push(
                InstrNode::new(Inst::BinOp {
                    op,
                    ty: Ty::I32,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2)),
            );
            blk.body
                .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
            f.blocks.push(blk);
            m.add_function(f);
            m
        };

        let d = diff(&mk(BinOp::Add), &mk(BinOp::Sub));
        assert!(!d.is_empty());
        let mut found_replaced = false;
        if let FuncChange::Changed { block_changes, .. } = &d.changes[0] {
            for bc in block_changes {
                if let BlockChange::InstrDiff { instr_changes, .. } = bc {
                    for ic in instr_changes {
                        if let InstrChange::Replaced { .. } = ic {
                            found_replaced = true;
                        }
                    }
                }
            }
        }
        assert!(found_replaced, "expected Replaced for Add vs Sub");
    }

    // 13. icmp eq vs ne reports replaced -----------------------------------

    #[test]
    fn icmp_eq_vs_ne_reports_replaced() {
        use crate::inst::ICmpOp;
        let mk = |op: ICmpOp| -> Module {
            let mut m = Module::new("m");
            let ft = m.add_func_type(FuncTy {
                params: vec![Ty::I32, Ty::I32],
                returns: vec![Ty::Bool],
                is_vararg: false,
            });
            let mut f = Function::new(FuncId::new(0), "main", ft, b(0));
            let mut blk = Block::new(b(0));
            blk.params.push((v(0), Ty::I32));
            blk.params.push((v(1), Ty::I32));
            blk.body.push(
                InstrNode::new(Inst::ICmp {
                    op,
                    ty: Ty::I32,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2)),
            );
            blk.body
                .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
            f.blocks.push(blk);
            m.add_function(f);
            m
        };
        let d = diff(&mk(ICmpOp::Eq), &mk(ICmpOp::Ne));
        assert!(!d.is_empty());
    }

    // 14. fingerprint distinguishes primitive types ------------------------

    #[test]
    fn fp_primitive_types_distinct() {
        let m = Module::new("m");
        assert_ne!(fp_ty(&m, &Ty::I32), fp_ty(&m, &Ty::I64));
        assert_ne!(fp_ty(&m, &Ty::I32), fp_ty(&m, &Ty::U32));
        assert_ne!(fp_ty(&m, &Ty::F32), fp_ty(&m, &Ty::F64));
        assert_ne!(fp_ty(&m, &Ty::Ptr), fp_ty(&m, &Ty::Unit));
    }

    #[test]
    fn fp_vector_types_distinguish_lane_count_and_element_type() {
        let m = Module::new("m");
        let v4i32 = Ty::Vector(Box::new(Ty::I32), 4);
        let v8i32 = Ty::Vector(Box::new(Ty::I32), 8);
        let v4u32 = Ty::Vector(Box::new(Ty::U32), 4);

        assert_ne!(fp_ty(&m, &v4i32), fp_ty(&m, &v8i32));
        assert_ne!(fp_ty(&m, &v4i32), fp_ty(&m, &v4u32));
    }

    #[test]
    fn enum_fingerprint_binds_layout_but_not_field_names() {
        let build = |tag_offset, field_name: &str| {
            let mut module = Module::new("m");
            let mut def = EnumDef::new(
                EnumId::new(0),
                "E",
                vec![EnumVariant {
                    name: "V".into(),
                    fields: vec![Ty::I32],
                    field_names: vec![field_name.into()],
                }],
            );
            def.layout = Some(EnumLayoutDescriptor {
                encoding: EnumTagEncoding::Direct { tag_offset },
                size: 8,
                align: 4,
                variant_field_offsets: vec![vec![0]],
            });
            module.add_enum(def);
            module
        };
        let base = build(4, "left");
        let renamed = build(4, "right");
        let moved = build(0, "left");
        assert_eq!(
            fp_ty(&base, &Ty::Enum(EnumId::new(0))),
            fp_ty(&renamed, &Ty::Enum(EnumId::new(0)))
        );
        assert_ne!(
            fp_ty(&base, &Ty::Enum(EnumId::new(0))),
            fp_ty(&moved, &Ty::Enum(EnumId::new(0)))
        );
    }

    #[test]
    fn diff_reports_vector_lane_count_and_element_type_differences() {
        let vector_param_module = |ty: Ty| -> Module {
            let mut m = Module::new("m");
            let ft = m.add_func_type(FuncTy {
                params: vec![ty.clone()],
                returns: vec![],
                is_vararg: false,
            });
            let mut f = Function::new(FuncId::new(0), "main", ft, b(0));
            let mut blk = Block::new(b(0));
            blk.params.push((v(0), ty));
            blk.body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            f.blocks.push(blk);
            m.add_function(f);
            m
        };

        let base = vector_param_module(Ty::Vector(Box::new(Ty::I32), 4));
        for (changed, expected) in [
            (
                vector_param_module(Ty::Vector(Box::new(Ty::I32), 8)),
                "vec<8xi32>",
            ),
            (
                vector_param_module(Ty::Vector(Box::new(Ty::U32), 4)),
                "vec<4xu32>",
            ),
        ] {
            let d = diff(&base, &changed);
            let text = d.to_text();
            assert!(!d.is_empty(), "{text}");
            assert!(text.contains("vec<4xi32>"), "{text}");
            assert!(text.contains(expected), "{text}");
        }
    }

    // 15. int vs float with same bits are distinct -------------------------

    #[test]
    fn fp_int_constant_distinct_from_float_with_same_bits() {
        let m = Module::new("m");
        let i = Constant::Int(0);
        let f = Constant::Float(0.0);
        assert_ne!(fp_constant(&m, &i), fp_constant(&m, &f));
    }

    // 16. SwitchCase reference is consumed (compile-time smoke)   ---------

    #[test]
    fn switch_case_type_is_used() {
        // Force the import path so a refactor that accidentally drops
        // `SwitchCase` from the imports breaks at compile time rather than
        // silently changing behavior.
        let _sc = SwitchCase {
            value: Constant::Int(0),
            target: b(0),
            args: vec![],
        };
    }

    // 17. to_text empty when no diff --------------------------------------

    #[test]
    fn to_text_empty_when_isomorphic() {
        let a = single_return_module("m", 0, 0);
        let d = diff(&a, &a);
        assert!(d.to_text().is_empty());
    }

    // 18. module proof-state diff: obligation status ----------------------

    #[test]
    fn obligation_status_change_is_reported_and_hidden_by_ignore_proofs() {
        use crate::proof::{ObligationKind, ProofStatus};

        let mk = |status: ProofStatus| -> Module {
            let mut m = single_return_module("m", 0, 0);
            m.proof_obligations.push(ProofObligation::new(
                ProofId::new(0),
                ObligationKind::Postcondition,
                status,
                "result is non-negative",
            ));
            m
        };

        let a = mk(ProofStatus::Pending);
        let b_mod = mk(ProofStatus::Discharged);

        let d = diff(&a, &b_mod);
        assert!(!d.is_empty(), "status change must surface");
        assert!(d.changes.is_empty(), "only proof state changed, not bodies");
        assert_eq!(d.proof_state_changes.len(), 1);
        match &d.proof_state_changes[0] {
            ProofStateChange::ObligationStatusChanged { before, after, .. } => {
                assert_eq!(before, "pending");
                assert_eq!(after, "discharged");
            }
            other => panic!("expected ObligationStatusChanged, got {other:?}"),
        }

        // --ignore-proofs hides it.
        let d2 = diff_with(
            &a,
            &b_mod,
            DiffOptions {
                ignore_proofs: true,
            },
        );
        assert!(d2.is_empty(), "{}", d2.to_text());
    }

    // 19. obligation status diff is insensitive to ProofId renumbering -----

    #[test]
    fn obligation_match_ignores_proof_id_renumbering() {
        use crate::proof::{ObligationKind, ProofStatus};

        let mk = |id: u32| -> Module {
            let mut m = single_return_module("m", 0, 0);
            m.proof_obligations.push(ProofObligation::new(
                ProofId::new(id),
                ObligationKind::Precondition,
                ProofStatus::Discharged,
                "x > 0",
            ));
            m
        };

        // Same claim, same status, different arena id => no diff.
        let d = diff(&mk(0), &mk(42));
        assert!(d.is_empty(), "{}", d.to_text());
    }

    #[test]
    fn obligation_claim_fingerprint_binds_every_embedded_source_identity_field() {
        use crate::ProofDigest;
        use crate::proof::{
            ObligationKind, ProofObligationSourceIdentity, ProofObligationSourceRange, ProofStatus,
            PublicObligationIdentity,
        };

        let mut base = single_return_module("m", 0, 0);
        base.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(0),
                ObligationKind::Precondition,
                ProofStatus::Pending,
                "x > 0",
            )
            .with_source(
                ProofObligationSourceIdentity::new("rust:crate::f", "assertion α")
                    .with_range(ProofObligationSourceRange {
                        file: 2,
                        start_line: 11,
                        start_col: 3,
                        end_line: 12,
                        end_col: 9,
                    })
                    .with_public(PublicObligationIdentity {
                        obligation_id: "vc:crate::f:0".to_string(),
                        semantic_digest: ProofDigest::sha256([7; 32]),
                    }),
            ),
        );
        let mutations: &[fn(&mut ProofObligationSourceIdentity)] = &[
            |source| source.source_id.push('!'),
            |source| source.assertion_id.push('!'),
            |source| source.range.as_mut().unwrap().file += 1,
            |source| source.range.as_mut().unwrap().start_line += 1,
            |source| source.range.as_mut().unwrap().start_col += 1,
            |source| source.range.as_mut().unwrap().end_line += 1,
            |source| source.range.as_mut().unwrap().end_col += 1,
            |source| source.public.as_mut().unwrap().obligation_id.push('!'),
            |source| source.public.as_mut().unwrap().semantic_digest.bytes[0] ^= 1,
        ];
        for mutate in mutations {
            let mut changed = base.clone();
            mutate(changed.proof_obligations[0].source.as_mut().unwrap());
            let result = diff(&base, &changed);
            assert_eq!(
                result.proof_state_changes.len(),
                2,
                "source mutation must remove the old claim and add the new claim: {}",
                result.to_text()
            );
            assert!(
                result
                    .proof_state_changes
                    .iter()
                    .any(|change| matches!(change, ProofStateChange::ObligationRemoved { .. }))
            );
            assert!(
                result
                    .proof_state_changes
                    .iter()
                    .any(|change| matches!(change, ProofStateChange::ObligationAdded { .. }))
            );
        }
    }

    // 20. missing certificate is reported ----------------------------------

    #[test]
    fn missing_certificate_is_reported() {
        use crate::proof::{ObligationKind, ProofStatus};

        let with_cert = |include: bool| -> Module {
            let mut m = single_return_module("m", 0, 0);
            m.proof_obligations.push(ProofObligation::new(
                ProofId::new(0),
                ObligationKind::MemorySafety,
                ProofStatus::Discharged,
                "no out-of-bounds access",
            ));
            if include {
                m.proof_certificates.push(ProofCertificate {
                    obligation: ProofId::new(0),
                    prover: "ay".into(),
                    evidence: ProofEvidence::SmtProof(vec![1, 2, 3]),
                });
            }
            m
        };

        let a = with_cert(true);
        let b_mod = with_cert(false);

        let d = diff(&a, &b_mod);
        assert!(!d.is_empty());
        assert_eq!(d.proof_state_changes.len(), 1);
        assert!(matches!(
            &d.proof_state_changes[0],
            ProofStateChange::CertificateRemoved { .. }
        ));

        // The reverse direction reports it as added.
        let d_rev = diff(&b_mod, &a);
        assert!(matches!(
            &d_rev.proof_state_changes[0],
            ProofStateChange::CertificateAdded { .. }
        ));

        // --ignore-proofs hides the missing certificate.
        let d2 = diff_with(
            &a,
            &b_mod,
            DiffOptions {
                ignore_proofs: true,
            },
        );
        assert!(d2.is_empty(), "{}", d2.to_text());
    }

    // 21. per-call proof_context difference is reported --------------------

    #[test]
    fn differing_proof_context_on_call_is_reported() {
        use crate::proof::{ObligationKind, ProofStatus};
        use crate::value::FuncTyId;

        // Build a module with a callee `g` and a caller `main` whose single
        // call node carries a `proof_context`. The two modules differ only in
        // which obligation the context `assumes`.
        let mk = |assume_id: u32| -> Module {
            let mut m = Module::new("m");
            m.add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::Unit],
                is_vararg: false,
            });

            // Two obligations so the context can reference either.
            m.proof_obligations.push(
                ProofObligation::new(
                    ProofId::new(0),
                    ObligationKind::Postcondition,
                    ProofStatus::Discharged,
                    "g returns even",
                )
                .with_function(FuncId::new(1)),
            );
            m.proof_obligations.push(
                ProofObligation::new(
                    ProofId::new(1),
                    ObligationKind::Postcondition,
                    ProofStatus::Discharged,
                    "g returns positive",
                )
                .with_function(FuncId::new(1)),
            );

            // Callee g (id 1).
            let mut g = Function::new(FuncId::new(1), "g", FuncTyId::new(0), b(0));
            let mut gblk = Block::new(b(0));
            gblk.body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            g.blocks.push(gblk);
            m.add_function(g);

            // Caller main (id 0) calls g with a proof_context.
            let mut f = Function::new(FuncId::new(0), "main", FuncTyId::new(0), b(0));
            let mut blk = Block::new(b(0));
            blk.body.push(
                InstrNode::new(Inst::Call {
                    callee: FuncId::new(1),
                    args: vec![],
                })
                .with_proof_context(ProofContext {
                    assumes: vec![ProofId::new(assume_id)],
                    establishes: vec![],
                }),
            );
            blk.body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            f.blocks.push(blk);
            m.add_function(f);
            m
        };

        // Context assumes obligation 0 vs obligation 1 — distinct claims.
        let a = mk(0);
        let b_mod = mk(1);

        let d = diff(&a, &b_mod);
        assert!(!d.is_empty(), "differing proof_context must surface");
        let mut found = false;
        for c in &d.changes {
            if let FuncChange::Changed {
                name,
                block_changes,
                ..
            } = c
                && name == "main"
            {
                for bc in block_changes {
                    if let BlockChange::InstrDiff { instr_changes, .. } = bc {
                        for ic in instr_changes {
                            if let InstrChange::Replaced { before, after, .. } = ic {
                                assert!(before.contains("ctx{"), "before: {before}");
                                assert!(after.contains("ctx{"), "after: {after}");
                                found = true;
                            }
                        }
                    }
                }
            }
        }
        assert!(found, "expected a Replaced call node citing proof context");

        // --ignore-proofs hides the proof_context difference.
        let d2 = diff_with(
            &a,
            &b_mod,
            DiffOptions {
                ignore_proofs: true,
            },
        );
        assert!(d2.is_empty(), "{}", d2.to_text());
    }

    // 22. proof_context reference reordering alone is not a diff -----------

    #[test]
    fn proof_context_reference_order_is_insensitive() {
        use crate::proof::{ObligationKind, ProofStatus};
        use crate::value::FuncTyId;

        let mk = |assumes: Vec<u32>| -> Module {
            let mut m = Module::new("m");
            m.add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::Unit],
                is_vararg: false,
            });
            for (i, desc) in ["a", "b"].iter().enumerate() {
                m.proof_obligations.push(ProofObligation::new(
                    ProofId::new(i as u32),
                    ObligationKind::Precondition,
                    ProofStatus::Discharged,
                    *desc,
                ));
            }
            let mut g = Function::new(FuncId::new(1), "g", FuncTyId::new(0), b(0));
            let mut gblk = Block::new(b(0));
            gblk.body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            g.blocks.push(gblk);
            m.add_function(g);

            let mut f = Function::new(FuncId::new(0), "main", FuncTyId::new(0), b(0));
            let mut blk = Block::new(b(0));
            blk.body.push(
                InstrNode::new(Inst::Call {
                    callee: FuncId::new(1),
                    args: vec![],
                })
                .with_proof_context(ProofContext {
                    assumes: assumes.into_iter().map(ProofId::new).collect(),
                    establishes: vec![],
                }),
            );
            blk.body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            f.blocks.push(blk);
            m.add_function(f);
            m
        };

        // Same reference set, different order => no diff.
        let d = diff(&mk(vec![0, 1]), &mk(vec![1, 0]));
        assert!(d.is_empty(), "{}", d.to_text());
    }

    // 23. proof-state JSON output round-trips ------------------------------

    #[test]
    fn proof_state_json_is_valid() {
        use crate::proof::{ObligationKind, ProofStatus};

        let mut a = single_return_module("m", 0, 0);
        a.proof_obligations.push(ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Pending,
            "p",
        ));
        let mut b_mod = single_return_module("m", 0, 0);
        b_mod.proof_obligations.push(ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Discharged,
            "p",
        ));

        let d = diff(&a, &b_mod);
        let j = d.to_json();
        let v: serde_json::Value = serde_json::from_str(&j).expect("to_json must emit valid JSON");
        let ps = v["proof_state"].as_array().expect("proof_state array");
        assert_eq!(ps.len(), 1);
        assert_eq!(ps[0]["kind"], "obligation_status_changed");
        assert_eq!(ps[0]["before"], "pending");
        assert_eq!(ps[0]["after"], "discharged");
    }
}
