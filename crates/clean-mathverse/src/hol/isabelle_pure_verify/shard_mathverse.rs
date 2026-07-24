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
//! Every `KernelVerified` line appends exactly the constants it emits to the
//! writer, in line order (`batch::verify_one`), and rejects touch the writer not
//! at all. So the full-replay writer's constant list is the KV constants in line
//! order, and [`ShardRecorder`](super::shard_verify) records precisely which of
//! them fall in a shard's range. [`copy_constant_into`] re-flattens one
//! constant's type+value through the SAME lowering path the original build used
//! (`reconstruct_single_subdag` → `lower_kernel_expr`), so both the per-range
//! subset and the merge are genuine `.mathverse` shards built by the existing
//! writer — no new format. Re-adding constants in serial order reproduces the
//! unsharded declaration set and verdicts (the equivalence proved at fixture
//! scale by `tests/isabelle_shard_determinism.rs`).

use std::path::{Path, PathBuf};

use crate::hol::opentheory_shard::lower_kernel_expr;
use crate::shard::{ShardReader, ShardWriter};
use crate::shard_reconstruct::reconstruct_single_subdag;
use crate::types::{MathverseConstantHeader, NO_VALUE};

use super::shard_verify::{stream_shard_recorded, ShardSpec, ShardVerdicts};
use super::StreamError;

/// Wrap any error carrying a message as a [`StreamError::Io`] (`std::io::Error::other`).
fn io_err(msg: impl std::fmt::Display) -> StreamError {
    StreamError::Io(std::io::Error::other(msg.to_string()))
}

/// Copy the constant at `idx` in `src` into `dst`, re-flattening its type and
/// value through the same `reconstruct → lower` path the original shard build
/// used, so `dst` accumulates a genuine, self-contained subset (its own arena).
/// Preserves every verdict-bearing header field (name, confidence, domain,
/// decl-kind, axiom profile); re-points the name/type/value indices into `dst`.
///
/// # Errors
/// [`StreamError::Io`] if `idx` is out of range, the constant carries
/// declaration-level universe params (not produced by the Isabelle KV lane — a
/// loud refusal rather than a silently-mis-indexed copy), or its type/value
/// sub-DAG cannot be reconstructed.
fn copy_constant_into(
    src: &ShardReader,
    idx: u32,
    dst: &mut ShardWriter,
) -> Result<(), StreamError> {
    let header = *src.constants.get(idx as usize).ok_or_else(|| {
        io_err(format!(
            "shard constant index {idx} out of range ({} constants)",
            src.constants.len()
        ))
    })?;
    if header.level_params_count != 0 {
        return Err(io_err(
            "per-range .mathverse copy does not carry declaration-level universe params \
             (the Isabelle KernelVerified lane produces none)",
        ));
    }
    let name = src
        .strings
        .get(header.name_idx as usize)
        .map(String::as_str)
        .unwrap_or("");
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
    dst.add_constant(MathverseConstantHeader {
        name_idx,
        type_idx,
        value_idx,
        ..header
    });
    Ok(())
}

/// Write the `.mathverse` subset carrying exactly the `const_indices` constants of
/// `full_writer` (a whole-replay writer) to `out_path`. Returns the count written.
///
/// The full writer is serialized once and read back so the copy path sees the
/// same public shard arenas the loader does. `const_indices` are the emitting
/// order (== serial/line order) recorded for this shard's range.
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
    for &idx in const_indices {
        copy_constant_into(&src, idx, &mut dst)?;
    }
    dst.write_to_file(out_path).map_err(io_err)?;
    Ok(const_indices.len())
}

/// [`super::import_proven_theorems_streaming_shard`] plus per-range `.mathverse`
/// emission: run the shard's full deterministic replay, and (when `mathverse_out`
/// is set) write ITS OWN serial range's `KernelVerified` constants to that path as
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
        write_range_shard(writer, recorder.emitted_const_indices(), out)?;
    }
    Ok(recorder.into_verdicts())
}

/// Merge a group's per-range `.mathverse` artifacts (produced by
/// [`import_proven_theorems_streaming_shard_emit`]) into one `.mathverse` at
/// `out_path`, equivalent to the unsharded run's output.
///
/// `shard_paths` MUST be in serial/line order (shard `1..N`, `lo`-ascending): the
/// merge re-adds every shard's constants in that order into one fresh writer, so
/// the merged declaration set and verdicts match the unsharded stream (the ranges
/// tile `[0, total)` exactly, per [`ShardSpec::range`]). Returns the merged
/// constant count.
///
/// # Errors
/// [`StreamError::Io`] on a read/parse/write failure or a per-constant copy error.
pub fn merge_shard_mathverse(
    shard_paths: &[PathBuf],
    out_path: impl AsRef<Path>,
) -> Result<usize, StreamError> {
    let mut dst = ShardWriter::new();
    let mut total = 0usize;
    for path in shard_paths {
        let bytes = std::fs::read(path)?;
        let src = ShardReader::from_bytes(&bytes).map_err(io_err)?;
        for idx in 0..src.constants.len() as u32 {
            copy_constant_into(&src, idx, &mut dst)?;
            total += 1;
        }
    }
    dst.write_to_file(out_path.as_ref()).map_err(io_err)?;
    Ok(total)
}
