// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Per-range `.mathverse` emission for sharded verify** — the production
//! provenance-shard output a sharded run was missing (design note §8 follow-up).
//!
//! # The gap this closes
//!
//! A shard runs the FULL deterministic replay (§3.1) and its [`ShardWriter`]
//! therefore holds the WHOLE corpus's `KernelVerified` constants — but the only
//! mergeable artifact was [`ShardVerdicts`] (serials/names/counts), so a sharded
//! run could not produce the real `.mathverse` provenance shard the unsharded
//! stream writes. This module carves each shard's OWN serial range out of the
//! full-replay writer into a per-shard `.mathverse`, and merges the per-shard
//! artifacts back into one equivalent to the unsharded run.
//!
//! # How the subset and merge stay faithful
//!
//! The full-replay writer holds the translator-synthesized definitional
//! prelude (emitted ONCE before the line loop, `super::emit_defs`) followed by
//! the KV constants in line order: every `KernelVerified` line appends exactly
//! the constants it emits, and rejects touch the writer not at all. The
//! [`ShardRecorder`](super::shard_verify) records both windows — the prelude's
//! slots and this range's own — and a range shard carries BOTH, because a shard
//! declaring theorems whose types and proof values reference `isabelle.def.*`
//! constants it does not carry is exactly the shard whose theorems the
//! consumer's dependency loader rejects. The merge then collapses the `N`
//! prelude copies by exact content identity. [`copy_constant_into`] re-flattens one
//! constant's type+value through the SAME lowering path the original build used
//! (`reconstruct_single_subdag` → `lower_kernel_expr`), so both the per-range
//! subset and the merge are genuine `.mathverse` shards built by the existing
//! writer — no new format. Re-adding constants in serial order reproduces the
//! unsharded declaration set and verdicts (the equivalence proved at fixture
//! scale by `tests/isabelle_shard_determinism.rs`).

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use crate::hol::opentheory_shard::lower_kernel_expr;
use crate::shard::{ShardReader, ShardWriter};
use crate::shard_reconstruct::reconstruct_single_subdag;
use crate::types::{AxiomProfile, MathverseConstantHeader, NO_VALUE};

use super::shard_verify::{stream_shard_recorded, ShardSpec, ShardVerdicts};
use super::StreamError;

/// Wrap any error carrying a message as a [`StreamError::Io`] (`std::io::Error::other`).
fn io_err(msg: impl std::fmt::Display) -> StreamError {
    StreamError::Io(std::io::Error::other(msg.to_string()))
}

/// A constant's **content identity in the destination writer** — the dedup key
/// [`copy_constant_into`] uses to collapse the shared definitional prelude that
/// every range shard carries, without ever collapsing two distinct declarations.
///
/// [`ShardWriter`] hash-conses expressions, levels and strings, so *within one
/// `dst`* two constants share `(type_idx, value_idx)` **iff** their type and
/// value expressions are structurally equal (equal indices trivially imply equal
/// exprs; equal exprs yield equal indices by bottom-up hash-consing). Adding the
/// name, the universe-parameter names, every verdict-bearing header byte and the
/// axiom profile makes this an EXACT content identity, not a name heuristic: a
/// constant is skipped only when a byte-for-byte identical declaration is
/// already present, and two declarations sharing a name but differing in
/// anything at all get different keys and are BOTH kept.
#[derive(PartialEq, Eq, Hash)]
struct ConstKey {
    name: String,
    /// Destination-arena type index (hash-consed ⇒ structural identity).
    type_idx: u32,
    /// Destination-arena value index (`NO_VALUE` for an axiom).
    value_idx: u32,
    /// Universe-parameter names, in declaration order.
    level_names: Vec<String>,
    /// `(source_system, import_confidence, content_domain, decl_kind)`.
    verdict_bytes: [u8; 4],
    axiom_profile: AxiomProfile,
}

/// Copy the constant at `idx` in `src` into `dst`, re-flattening its type and
/// value through the same `reconstruct → lower` path the original shard build
/// used, so `dst` accumulates a genuine, self-contained subset (its own arena).
/// Preserves every verdict-bearing header field (name, confidence, domain,
/// decl-kind, axiom profile, universe params); re-points the name/type/value/
/// level-param indices into `dst`.
///
/// `seen` carries the [`ConstKey`]s already written to `dst`. Returns `true` when
/// a header was appended, `false` when an identical declaration was already
/// there (the shared prelude's `N - 1` redundant copies).
///
/// # Errors
/// [`StreamError::Io`] if `idx` is out of range, the universe-parameter string
/// block is out of range, or the type/value sub-DAG cannot be reconstructed.
fn copy_constant_into(
    src: &ShardReader,
    idx: u32,
    dst: &mut ShardWriter,
    seen: &mut HashSet<ConstKey>,
) -> Result<bool, StreamError> {
    let header = *src.constants.get(idx as usize).ok_or_else(|| {
        io_err(format!(
            "shard constant index {idx} out of range ({} constants)",
            src.constants.len()
        ))
    })?;
    let name = src
        .strings
        .get(header.name_idx as usize)
        .map(String::as_str)
        .unwrap_or("");
    // Universe params must be CARRIED, not refused and not dropped: the
    // synthesized definitional prelude every range shard now carries contains
    // universe-polymorphic constants (`isabelle.def.HOL.If` has `["u"]`), and a
    // consumer's `Const(isabelle.def.HOL.If, [u])` fails checked registration
    // with `LevelCountMismatch` against a header whose parameter list was
    // dropped — the exact failure the shard-writer level-list fix removed.
    let lp_start = header.level_params_start as usize;
    let lp_end = lp_start + header.level_params_count as usize;
    let level_names: Vec<String> = src
        .strings
        .get(lp_start..lp_end)
        .ok_or_else(|| {
            io_err(format!(
                "universe-parameter block [{lp_start}, {lp_end}) of `{name}` is out of range \
                 ({} strings)",
                src.strings.len()
            ))
        })?
        .to_vec();
    let type_expr = reconstruct_single_subdag(
        &src.exprs,
        &src.levels,
        &src.strings,
        &src.level_lists,
        header.type_idx,
    )
    .map_err(|e| io_err(format!("reconstruct type of `{name}`: {e}")))?;
    let name_idx = dst.add_string(name);
    let type_idx = lower_kernel_expr(&type_expr, dst);
    let value_idx = if header.value_idx == NO_VALUE {
        NO_VALUE
    } else {
        let value_expr = reconstruct_single_subdag(
            &src.exprs,
            &src.levels,
            &src.strings,
            &src.level_lists,
            header.value_idx,
        )
        .map_err(|e| io_err(format!("reconstruct value of `{name}`: {e}")))?;
        lower_kernel_expr(&value_expr, dst)
    };
    let key = ConstKey {
        name: name.to_string(),
        type_idx,
        value_idx,
        level_names: level_names.clone(),
        verdict_bytes: [
            header.source_system,
            header.import_confidence,
            header.content_domain,
            header.decl_kind,
        ],
        axiom_profile: header.axiom_profile,
    };
    if !seen.insert(key) {
        return Ok(false);
    }
    // AFTER the dedup check: `add_string_block` appends unconditionally to
    // guarantee a contiguous window, so running it for a skipped duplicate would
    // bloat the destination string table by one block per skipped copy.
    let level_refs: Vec<&str> = level_names.iter().map(String::as_str).collect();
    let level_params_start = dst.add_string_block(&level_refs);
    dst.add_constant(MathverseConstantHeader {
        name_idx,
        type_idx,
        value_idx,
        level_params_start,
        ..header
    });
    Ok(true)
}

/// Write the `.mathverse` subset carrying exactly the `const_indices` constants of
/// `full_writer` (a whole-replay writer) to `out_path`. Returns the count written
/// (`const_indices.len()` minus any exact-content duplicate).
///
/// The full writer is serialized once and read back so the copy path sees the
/// same public shard arenas the loader does. `const_indices` are the emitting
/// order: the shared definitional prelude first, then this range's own
/// constants in serial/line order.
///
/// # Errors
/// [`StreamError::Io`] on a serialize/parse/write failure or a per-constant copy
/// error (see [`copy_constant_into`]).
fn write_range_shard(
    full_writer: &ShardWriter,
    const_indices: &[u32],
    out_path: &Path,
) -> Result<usize, StreamError> {
    let mut buf = Vec::new();
    full_writer.write(&mut buf).map_err(io_err)?;
    let src = ShardReader::from_bytes(&buf).map_err(io_err)?;
    let mut dst = ShardWriter::new();
    let mut seen = HashSet::new();
    let mut written = 0usize;
    for &idx in const_indices {
        if copy_constant_into(&src, idx, &mut dst, &mut seen)? {
            written += 1;
        }
    }
    dst.write_to_file(out_path).map_err(io_err)?;
    Ok(written)
}

/// [`super::import_proven_theorems_streaming_shard`] plus per-range `.mathverse`
/// emission: run the shard's full deterministic replay, and (when `mathverse_out`
/// is set) write ITS OWN serial range's `KernelVerified` constants — plus the
/// shared synthesized definitional prelude those constants' types and proof
/// values reference, so the artifact is independently loadable — to that path as
/// a genuine `.mathverse` shard. `prepass` optionally loads a leader-exported
/// pre-pass snapshot (see [`super::export_prepass_snapshot`]). With
/// `mathverse_out == None` this is byte-identical to the plain shard verify.
///
/// # Errors
/// [`StreamError`] on file / snapshot errors, or a per-constant emission failure.
pub fn import_proven_theorems_streaming_shard_emit(
    serial_sorted_path: impl AsRef<Path>,
    writer: &mut ShardWriter,
    spec: ShardSpec,
    prepass: Option<&Path>,
    mathverse_out: Option<&Path>,
) -> Result<ShardVerdicts, StreamError> {
    let recorder = stream_shard_recorded(serial_sorted_path.as_ref(), writer, spec, prepass)?;
    if let Some(out) = mathverse_out {
        // `carried_const_indices`, not `emitted_const_indices`: the range's own
        // theorems PLUS the shared definitional prelude their types and proof
        // values reference. A shard carrying only its range declares theorems
        // whose closure no consumer can register (uncitable at TrustGate::Strict).
        write_range_shard(writer, &recorder.carried_const_indices(), out)?;
    }
    Ok(recorder.into_verdicts())
}

/// Merge a group's per-range `.mathverse` artifacts (produced by
/// [`import_proven_theorems_streaming_shard_emit`]) into one `.mathverse` at
/// `out_path`, equivalent to the unsharded run's output.
///
/// `shard_paths` MUST be in serial/line order (shard `1..N`, `lo`-ascending): the
/// merge re-adds every shard's constants in that order into one fresh writer,
/// **collapsing by exact content identity** ([`ConstKey`]) the shared
/// definitional prelude each range shard carries, so the merged declaration set
/// and verdicts match the unsharded stream (the ranges tile `[0, total)` exactly,
/// per [`ShardSpec::range`]). Returns the merged constant count.
///
/// The duplicated prelude bytes across the per-shard files are intentional — a
/// range shard must be independently loadable — and cost `(N - 1) · D` headers
/// in those files only; the merged artifact is unchanged in size and its
/// constant ORDER (prelude, then range `1..N` in serial order) is independent
/// of `N`.
///
/// # Errors
/// [`StreamError::Io`] on a read/parse/write failure or a per-constant copy error.
pub fn merge_shard_mathverse(
    shard_paths: &[PathBuf],
    out_path: impl AsRef<Path>,
) -> Result<usize, StreamError> {
    let mut dst = ShardWriter::new();
    let mut seen = HashSet::new();
    let mut total = 0usize;
    for path in shard_paths {
        let bytes = std::fs::read(path)?;
        let src = ShardReader::from_bytes(&bytes).map_err(io_err)?;
        for idx in 0..src.constants.len() as u32 {
            if copy_constant_into(&src, idx, &mut dst, &mut seen)? {
                total += 1;
            }
        }
    }
    dst.write_to_file(out_path.as_ref()).map_err(io_err)?;
    Ok(total)
}
