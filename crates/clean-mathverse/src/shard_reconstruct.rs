// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::cell::RefCell;
use std::sync::Arc;

use clean_kernel::expr::{BigNat, BinderInfo, Expr, FVarId};
use clean_kernel::flat::{FlatExpr, FlatFlags, FlatLevel};
use clean_kernel::level::Level;
use clean_kernel::name::Name;

/// Identity of a shard's raw slices, used to memoize whole-table reconstruction
/// across the many per-constant calls the incremental verifier makes against the
/// SAME reader.
#[derive(PartialEq, Eq, Clone, Copy)]
struct ArenaKey {
    exprs: (usize, usize),
    levels: (usize, usize),
    strings: (usize, usize),
    level_lists: (usize, usize),
}

impl ArenaKey {
    fn of(
        exprs: &[FlatExpr],
        levels: &[FlatLevel],
        strings: &[String],
        level_lists: &[u32],
    ) -> Self {
        ArenaKey {
            exprs: (exprs.as_ptr() as usize, exprs.len()),
            levels: (levels.as_ptr() as usize, levels.len()),
            strings: (strings.as_ptr() as usize, strings.len()),
            level_lists: (level_lists.as_ptr() as usize, level_lists.len()),
        }
    }
}

thread_local! {
    /// Size-1 memo of the reconstructed expr table for the most-recently-seen
    /// arena. The incremental verifier reconstructs EVERY constant of one reader
    /// against the same arena; the naive per-constant path rebuilds `0..=idx`
    /// each call — O(N·M) over the merged corpus arena, which made a single
    /// chunk take >17h. Building the full table once and serving indexed clones
    /// is O(M + N). The reconstructed `Expr`s are byte-identical to the
    /// per-constant path (same `reconstruct_single_expr` over the same in-order
    /// `built_exprs`), so verification verdicts are unchanged — this is purely a
    /// speedup. Keyed on the four raw slice (ptr, len) pairs; a key mismatch
    /// rebuilds, so distinct readers stay correct (a collision would require all
    /// four independent slices to alias at identical ptr+len, which cannot happen
    /// for two live readers).
    static RECONSTRUCT_TABLE: RefCell<Option<(ArenaKey, Vec<Expr>)>> = const { RefCell::new(None) };
}

pub fn reconstruct_from_shard(
    exprs: &[FlatExpr],
    levels: &[FlatLevel],
    strings: &[String],
    expr_idx: u32,
) -> Result<Expr, String> {
    reconstruct_from_shard_with_level_lists(exprs, levels, strings, &[], expr_idx)
}

/// Reconstruct an expression from shard data, with support for level lists.
///
/// Memoized per-arena (see [`RECONSTRUCT_TABLE`]): the first call for a given
/// reader builds the whole reconstructable prefix once; subsequent calls index
/// the cached table.
pub fn reconstruct_from_shard_with_level_lists(
    exprs: &[FlatExpr],
    levels: &[FlatLevel],
    strings: &[String],
    level_lists: &[u32],
    expr_idx: u32,
) -> Result<Expr, String> {
    let idx = expr_idx as usize;
    if idx >= exprs.len() {
        return Err(format!(
            "expression index {idx} out of bounds for shard with {} expressions",
            exprs.len()
        ));
    }

    let key = ArenaKey::of(exprs, levels, strings, level_lists);
    RECONSTRUCT_TABLE.with(|cell| {
        let mut slot = cell.borrow_mut();
        if slot.as_ref().map(|(k, _)| *k != key).unwrap_or(true) {
            // `reconstruct_expr_table_prefix` calls `reconstruct_single_expr`
            // directly (not back into this function), so there is no re-entrant
            // borrow of the thread-local while we hold it here.
            let table = reconstruct_expr_table_prefix(exprs, levels, strings, level_lists);
            *slot = Some((key, table));
        }
        let table = &slot.as_ref().expect("table just populated").1;
        table.get(idx).cloned().ok_or_else(|| {
            format!(
                "failed to reconstruct expression {idx} (beyond reconstructable prefix of len {})",
                table.len()
            )
        })
    })
}

/// Reconstruct the longest valid prefix of a shard's expression table in one
/// pass, sharing the work across every constant of the shard.
///
/// Returns the reconstructed expressions for indices `0..prefix_len`; the
/// table is truncated at the first entry that fails to reconstruct (an
/// unsupported-flagged entry, a bad tag, a dangling reference, …). This
/// truncation mirrors [`reconstruct_from_shard_with_level_lists`] exactly:
/// the per-constant path rebuilds `0..=type_idx` in order and errors on the
/// first bad entry, so a constant's type is reconstructible there **iff**
/// `type_idx < prefix_len` here. If the level table itself fails to build,
/// the prefix is empty (every per-constant call would fail too).
///
/// Why this exists: calling the per-constant function for each of a shard's
/// N constants rebuilds the table from scratch every time — O(N·M) for an
/// M-entry table (measured ~10ms/constant on real mathverse shards). One
/// shared pass is O(M) and produces structurally identical expressions: the
/// loop body is the same code, so digests computed over the results are
/// byte-identical to the per-constant path.
pub(crate) fn reconstruct_expr_table_prefix(
    exprs: &[FlatExpr],
    levels: &[FlatLevel],
    strings: &[String],
    level_lists: &[u32],
) -> Vec<Expr> {
    let Ok(built_levels) = build_levels(levels, strings, levels.len()) else {
        return Vec::new();
    };
    // Store each built node as a shared `Arc` so a node referenced by multiple
    // parents is one allocation (F2 — preserves the arena's DAG sharing).
    let mut built_exprs: Vec<Option<Arc<Expr>>> = Vec::with_capacity(exprs.len());
    for (i, flat) in exprs.iter().enumerate() {
        // Truncate at the first UNSUPPORTED-flagged entry (mode-extension /
        // unconvertible exprs encoded as Sort(0)+UNSUPPORTED by the writer, see
        // clean_kernel::flat::convert). NOTE: the flag is bit 4 (0x10); the old
        // `1 << 0` here tested bit 0, which is the unrelated VERIFIED flag —
        // letting UNSUPPORTED exprs through to reconstruct as garbage. Matches
        // the kernel's own `flat::reconstruct` guard.
        if flat.flags().contains(FlatFlags::UNSUPPORTED) {
            break;
        }
        let Ok(expr) =
            reconstruct_single_expr(flat, i, strings, &built_levels, level_lists, &built_exprs)
        else {
            break;
        };
        built_exprs.push(Some(Arc::new(expr)));
    }
    // Deref each prefix root to an owned `Expr` (its children remain the shared
    // `Arc`s built above — the intra-term DAG sharing that F1 accelerates).
    built_exprs
        .into_iter()
        .flatten()
        .map(|a| (*a).clone())
        .collect()
}

/// Reconstruct ONLY the sub-DAG reachable from `root_idx`, materializing each
/// reachable `FlatExpr` once, in ascending-index (== topological) order.
///
/// The writer emits children at strictly lower arena indices than their parents
/// (both the per-constant and prefix paths resolve children through already-built
/// lower indices), so a single ascending pass over the reachable set always has
/// every child ready before its parent. This is the demand-fold backing the
/// lazy/mmap closure loader: it materializes one constant's `Expr` WITHOUT
/// rebuilding the whole shard prefix (the memory win). The result is byte-identical
/// to indexing [`reconstruct_from_shard_with_level_lists`] at `root_idx` (same
/// `reconstruct_single_expr` over the same flats) — pinned by
/// `single_subdag_matches_full_reconstruct`. That identity is the soundness
/// invariant the lazy loader rests on: it must never change a reconstructed `Expr`,
/// hence never a KernelVerified verdict.
// Wired up by the lazy/mmap closure loader (zero-copy MVP, ShardConstantSource)
// and the structural-equivalence search path
// (`MathverseLibrary::structural_rewrite_digest_of`).
pub(crate) fn reconstruct_single_subdag(
    exprs: &[FlatExpr],
    levels: &[FlatLevel],
    strings: &[String],
    level_lists: &[u32],
    root_idx: u32,
) -> Result<Expr, String> {
    let root = root_idx as usize;
    if root >= exprs.len() {
        return Err(format!(
            "expression index {root} out of bounds for shard with {} expressions",
            exprs.len()
        ));
    }

    // Reachable expr indices via DFS over child-index edges.
    let mut reachable: std::collections::BTreeSet<u32> = std::collections::BTreeSet::new();
    let mut stack = vec![root_idx];
    while let Some(i) = stack.pop() {
        if !reachable.insert(i) {
            continue;
        }
        let flat = exprs
            .get(i as usize)
            .ok_or_else(|| format!("dangling expr index {i} in sub-DAG of {root}"))?;
        // Mirror the prefix path's truncation: an UNSUPPORTED node is unreconstructable.
        if flat.flags().contains(FlatFlags::UNSUPPORTED) {
            return Err(format!("unsupported FlatExpr at {i} in sub-DAG of {root}"));
        }
        for child in expr_child_indices(flat)? {
            stack.push(child);
        }
    }

    // Levels are small relative to the expr arena; build the table once (the
    // per-constant path resolves levels by index too).
    let built_levels = build_levels(levels, strings, levels.len())
        .map_err(|e| format!("level table build failed for sub-DAG of {root}: {e}"))?;

    // Build reachable exprs in ascending (topological) order. Only reachable slots
    // are filled; every child of a reachable node is reachable and built earlier.
    // Shared-`Arc` slots so a node referenced by K parents is one allocation
    // (F2 — preserves the sub-DAG's sharing for the kernel's `ptr_eq` fast path).
    let mut built: Vec<Option<Arc<Expr>>> = vec![None; root + 1];
    for &i in &reachable {
        let flat = &exprs[i as usize];
        built[i as usize] = Some(Arc::new(reconstruct_single_expr(
            flat,
            i as usize,
            strings,
            &built_levels,
            level_lists,
            &built,
        )?));
    }

    built[root]
        .clone()
        .map(|a| (*a).clone())
        .ok_or_else(|| format!("failed to reconstruct sub-DAG root {root}"))
}

/// DEMAND-PAGED sub-DAG fold: identical to [`reconstruct_single_subdag`] but pulls
/// each `FlatExpr` through `read_flat` (an index→`FlatExpr` reader) instead of an
/// in-memory `&[FlatExpr]` slice. Backing the mmap closure loader, `read_flat`
/// decodes ONE 16-byte `FlatExpr` straight out of the `mmap`'d arena, so only the
/// bytes of the reachable sub-DAG ever fault in — the untouched bulk of the expr
/// arena (the OOM driver) is never resident.
///
/// SOUNDNESS / parity: this is byte-for-byte the same algorithm as
/// `reconstruct_single_subdag` — same DFS over [`expr_child_indices`], same
/// ascending-order build, same per-node [`reconstruct_single_expr`] over the same
/// `strings`/`built_levels`/`level_lists`. The ONLY change is the source of each
/// `FlatExpr` (a slice index vs. a decode-from-mmap that yields the identical
/// 16 bytes). Pinned equal to the slice path by
/// `mmap_subdag_matches_slice_subdag`. It therefore can NEVER change a
/// reconstructed `Expr`, hence never a KernelVerified verdict.
pub(crate) fn reconstruct_single_subdag_with_reader<F>(
    read_flat: F,
    expr_count: u32,
    levels: &[FlatLevel],
    strings: &[String],
    level_lists: &[u32],
    root_idx: u32,
) -> Result<Expr, String>
where
    F: Fn(u32) -> Result<FlatExpr, String>,
{
    let root = root_idx as usize;
    if root_idx >= expr_count {
        return Err(format!(
            "expression index {root} out of bounds for shard with {expr_count} expressions"
        ));
    }

    // Reachable expr indices via DFS over child-index edges. Each touched node is
    // read once from the mmap (16 bytes faulted), then cached in `flats` so the
    // ascending build pass below reuses it without a second fault.
    let mut reachable: std::collections::BTreeSet<u32> = std::collections::BTreeSet::new();
    let mut flats: std::collections::HashMap<u32, FlatExpr> = std::collections::HashMap::new();
    let mut stack = vec![root_idx];
    while let Some(i) = stack.pop() {
        if !reachable.insert(i) {
            continue;
        }
        let flat = read_flat(i)?;
        // Mirror the prefix path's truncation: an UNSUPPORTED node is unreconstructable.
        if flat.flags().contains(FlatFlags::UNSUPPORTED) {
            return Err(format!("unsupported FlatExpr at {i} in sub-DAG of {root}"));
        }
        for child in expr_child_indices(&flat)? {
            stack.push(child);
        }
        flats.insert(i, flat);
    }

    let built_levels = build_levels(levels, strings, levels.len())
        .map_err(|e| format!("level table build failed for sub-DAG of {root}: {e}"))?;

    // Build reachable exprs in ascending (topological) order. Only reachable slots
    // are filled; every child of a reachable node is reachable and built earlier.
    // Shared-`Arc` slots so a node referenced by K parents is one allocation
    // (F2 — preserves the sub-DAG's sharing for the kernel's `ptr_eq` fast path).
    let mut built: Vec<Option<Arc<Expr>>> = vec![None; root + 1];
    for &i in &reachable {
        let flat = flats
            .get(&i)
            .ok_or_else(|| format!("missing cached FlatExpr {i} in sub-DAG of {root}"))?;
        built[i as usize] = Some(Arc::new(reconstruct_single_expr(
            flat,
            i as usize,
            strings,
            &built_levels,
            level_lists,
            &built,
        )?));
    }

    built[root]
        .clone()
        .map(|a| (*a).clone())
        .ok_or_else(|| format!("failed to reconstruct sub-DAG root {root}"))
}

/// Expr-arena child indices referenced by a `FlatExpr` (mirrors the field offsets
/// read in [`reconstruct_single_expr`]). Level/string/literal operands are not
/// expr children and are excluded.
fn expr_child_indices(flat: &FlatExpr) -> Result<Vec<u32>, String> {
    Ok(match flat.tag {
        // App: fn, arg
        3 => vec![read_expr_u32(flat, 0)?, read_expr_u32(flat, 4)?],
        // Lam / Pi: ty (offset 1, after the binder-info byte), body (offset 5)
        4 | 5 => vec![read_expr_u32(flat, 1)?, read_expr_u32(flat, 5)?],
        // Let: ty, val, body
        6 => vec![
            read_expr_u32(flat, 0)?,
            read_expr_u32(flat, 4)?,
            read_expr_u32(flat, 8)?,
        ],
        // Proj: inner (offset 6, after name_idx + field u16)
        9 => vec![read_expr_u32(flat, 6)?],
        // BVar, Sort, Const, NatLit, StrLit, FVar: no expr children
        _ => Vec::new(),
    })
}

/// Dispatch a single FlatExpr tag to the corresponding kernel Expr constructor.
fn reconstruct_single_expr(
    flat: &FlatExpr,
    idx: usize,
    strings: &[String],
    built_levels: &[Level],
    level_lists: &[u32],
    built_exprs: &[Option<Arc<Expr>>],
) -> Result<Expr, String> {
    match flat.tag {
        0 => {
            let bvar_idx = read_expr_u32(flat, 0)?;
            // The kernel packs `loose_bvar_range` (= bvar_idx + 1) into 20 bits and
            // hard-PANICS above 2^20-1 (clean-kernel `expr/meta.rs`, matching Lean 4's
            // `expr.cpp`). A shard BVar at/above that cap is a corrupt de Bruijn index
            // (no real Lean term nests a million binders deep — it indicates a
            // malformed conversion, e.g. in Mathlib.Tactic.FunProp.RefinedDiscrTree).
            // Because release builds are `panic = "abort"`, letting `Expr::bvar` panic
            // would abort the ENTIRE corpus run; instead fail THIS constant's
            // reconstruction gracefully (it is recorded as reconstruct_failed and the
            // run continues). Soundness-neutral: a corrupt expr is never verified.
            const MAX_BVAR_RANGE: u32 = 1_048_575; // 2^20 - 1; mirrors clean_kernel ExprMeta
            if bvar_idx >= MAX_BVAR_RANGE {
                return Err(format!(
                    "corrupt bvar index {bvar_idx} >= kernel cap {MAX_BVAR_RANGE} (malformed reconstruction)"
                ));
            }
            Ok(Expr::bvar(bvar_idx))
        }
        1 => {
            let level_idx = read_expr_u32(flat, 0)?;
            Ok(Expr::sort(resolve_sort_level(built_levels, level_idx)?))
        }
        2 => {
            let name_idx = read_expr_u32(flat, 0)?;
            let levels_list_idx = read_expr_u32(flat, 4)?;
            let name = Name::from_string(get_string(strings, name_idx)?);
            let levels = reconstruct_level_list(built_levels, level_lists, levels_list_idx)?;
            Ok(Expr::const_(name, levels))
        }
        3 => {
            let fn_idx = read_expr_u32(flat, 0)?;
            let arg_idx = read_expr_u32(flat, 4)?;
            Ok(Expr::app_arc(
                get_expr_ref(built_exprs, fn_idx)?,
                get_expr_ref(built_exprs, arg_idx)?,
            ))
        }
        4 => {
            let binder_info = binder_info_from_u8(flat.data[0])?;
            let ty_idx = read_expr_u32(flat, 1)?;
            let body_idx = read_expr_u32(flat, 5)?;
            Ok(Expr::lam_arc(
                binder_info,
                get_expr_ref(built_exprs, ty_idx)?,
                get_expr_ref(built_exprs, body_idx)?,
            ))
        }
        5 => {
            let binder_info = binder_info_from_u8(flat.data[0])?;
            let ty_idx = read_expr_u32(flat, 1)?;
            let body_idx = read_expr_u32(flat, 5)?;
            Ok(Expr::pi_arc(
                binder_info,
                get_expr_ref(built_exprs, ty_idx)?,
                get_expr_ref(built_exprs, body_idx)?,
            ))
        }
        6 => {
            let ty_idx = read_expr_u32(flat, 0)?;
            let val_idx = read_expr_u32(flat, 4)?;
            let body_idx = read_expr_u32(flat, 8)?;
            Ok(Expr::let_named_arc(
                Name::anon(),
                get_expr_ref(built_exprs, ty_idx)?,
                get_expr_ref(built_exprs, val_idx)?,
                get_expr_ref(built_exprs, body_idx)?,
                false,
            ))
        }
        7 => {
            if flat.flags().contains(FlatFlags::NAT_BIG) {
                // BigNat > u64: data[0..4] is a string index to the comma-joined
                // decimal little-endian u64 limbs (see clean_kernel::flat::convert).
                let str_idx = read_expr_u32(flat, 0)?;
                let s = get_string(strings, str_idx)?;
                Ok(Expr::bignat_lit(parse_bignat_limbs(s)?))
            } else {
                Ok(Expr::nat_lit(read_expr_u64(flat, 0)?))
            }
        }
        8 => {
            let string_idx = read_expr_u32(flat, 0)?;
            Ok(Expr::str_lit(get_string(strings, string_idx)?))
        }
        9 => {
            let name_idx = read_expr_u32(flat, 0)?;
            let field = read_expr_u16(flat, 4)? as u32;
            let inner_idx = read_expr_u32(flat, 6)?;
            Ok(Expr::proj_arc(
                Name::from_string(get_string(strings, name_idx)?),
                field,
                get_expr_ref(built_exprs, inner_idx)?,
            ))
        }
        10 => Ok(Expr::fvar(FVarId::new(read_expr_u64(flat, 0)?))),
        tag => Err(format!("invalid FlatExpr tag {tag} at expression {idx}")),
    }
}

pub(crate) fn reconstruct_level_from_shard(
    levels: &[FlatLevel],
    strings: &[String],
    level_idx: u32,
) -> Result<Level, String> {
    let level_idx = level_idx as usize;
    if level_idx >= levels.len() {
        return Err(format!(
            "level index {level_idx} out of bounds for shard with {} levels",
            levels.len()
        ));
    }

    let built_levels = build_levels(levels, strings, level_idx + 1)?;
    built_levels
        .get(level_idx)
        .cloned()
        .ok_or_else(|| format!("failed to reconstruct level {level_idx}"))
}

fn build_levels(
    levels: &[FlatLevel],
    strings: &[String],
    limit: usize,
) -> Result<Vec<Level>, String> {
    if limit > levels.len() {
        return Err(format!(
            "requested {limit} levels from shard with only {} levels",
            levels.len()
        ));
    }

    let mut built: Vec<Option<Level>> = vec![None; limit];

    for i in 0..limit {
        let flat = &levels[i];
        let level = match flat.tag {
            FlatLevel::TAG_ZERO => Level::zero(),
            FlatLevel::TAG_SUCC => {
                let inner_idx = read_level_u32(flat, 0)?;
                Level::succ(get_built_level(&built, inner_idx)?)
            }
            FlatLevel::TAG_MAX => {
                let left_idx = read_level_u32(flat, 0)?;
                let right_idx = read_level_u32(flat, 4)?;
                Level::max(
                    get_built_level(&built, left_idx)?,
                    get_built_level(&built, right_idx)?,
                )
            }
            FlatLevel::TAG_IMAX => {
                let left_idx = read_level_u32(flat, 0)?;
                let right_idx = read_level_u32(flat, 4)?;
                Level::imax(
                    get_built_level(&built, left_idx)?,
                    get_built_level(&built, right_idx)?,
                )
            }
            FlatLevel::TAG_PARAM => {
                let name_idx = read_level_u32(flat, 0)?;
                Level::param(Name::from_string(get_string(strings, name_idx)?))
            }
            tag => return Err(format!("invalid FlatLevel tag {tag} at level {i}")),
        };

        built[i] = Some(level);
    }

    built
        .into_iter()
        .enumerate()
        .map(|(i, level)| level.ok_or_else(|| format!("failed to reconstruct level {i}")))
        .collect()
}

/// Reconstruct a Vec<Level> from the level_lists table entry at the given offset.
///
/// If `levels_list_idx` is `u32::MAX` (no-levels sentinel) or the level_lists
/// table is empty, returns an empty Vec. Otherwise reads
/// `[count, level_idx_0, ..., level_idx_N]` starting at that offset.
fn reconstruct_level_list(
    built_levels: &[Level],
    level_lists: &[u32],
    levels_list_idx: u32,
) -> Result<Vec<Level>, String> {
    if levels_list_idx == u32::MAX || level_lists.is_empty() {
        return Ok(Vec::new());
    }
    let offset = levels_list_idx as usize;
    if offset >= level_lists.len() {
        return Err(format!(
            "level_list offset {offset} out of bounds for level_lists table of length {}",
            level_lists.len()
        ));
    }
    let count = level_lists[offset] as usize;
    let start = offset + 1;
    if start + count > level_lists.len() {
        return Err(format!(
            "level_list at offset {offset} claims {count} entries but table has only {} remaining",
            level_lists.len() - start
        ));
    }
    let mut result = Vec::with_capacity(count);
    for k in 0..count {
        let level_idx = level_lists[start + k];
        result.push(get_level_ref(built_levels, level_idx)?);
    }
    Ok(result)
}

/// Reconstruct declaration-level universe parameter names from the string table.
///
/// Reads `count` consecutive strings starting at `start` from the string table
/// and converts them to `Name`s.
pub fn reconstruct_level_params(
    strings: &[String],
    start: u32,
    count: u16,
) -> Result<Vec<Name>, String> {
    if count == 0 {
        return Ok(Vec::new());
    }
    let mut params = Vec::with_capacity(count as usize);
    for i in 0..count as u32 {
        let idx = start + i;
        let s = get_string(strings, idx)?;
        params.push(Name::from_string(s));
    }
    Ok(params)
}

/// Parse the NAT_BIG limb string (`"limb0,limb1,..."`, decimal little-endian
/// u64 limbs) written by `clean_kernel::flat::convert` into a `BigNat`. Mirrors
/// the kernel's own `flat::reconstruct::parse_bignat_limbs` so the shard decode
/// reproduces the eager olean import's `Expr` exactly.
fn parse_bignat_limbs(s: &str) -> Result<BigNat, String> {
    let mut limbs = Vec::new();
    for part in s.split(',') {
        let limb = part
            .parse::<u64>()
            .map_err(|_| format!("invalid BigNat limb {part:?} in NAT_BIG literal"))?;
        limbs.push(limb);
    }
    Ok(BigNat::from_limbs(limbs))
}

fn get_string(strings: &[String], idx: u32) -> Result<&str, String> {
    strings
        .get(idx as usize)
        .map(|s| s.as_str())
        .ok_or_else(|| {
            format!(
                "string index {idx} out of bounds for shard with {} strings",
                strings.len()
            )
        })
}

fn get_built_level(levels: &[Option<Level>], idx: u32) -> Result<Level, String> {
    levels
        .get(idx as usize)
        .ok_or_else(|| format!("level index {idx} out of bounds during reconstruction"))?
        .clone()
        .ok_or_else(|| format!("level index {idx} referenced before it was reconstructed"))
}

fn get_level_ref(levels: &[Level], idx: u32) -> Result<Level, String> {
    levels
        .get(idx as usize)
        .cloned()
        .ok_or_else(|| format!("level index {idx} out of bounds during reconstruction"))
}

/// Whether a reconstructed level pool is the bare zero sentinel — the signature
/// of a legacy coq_v/fstar shard whose importer wrote `sort(N)` with `N` as a
/// **raw universe value** instead of a level-pool index (see
/// [`crate::coq::v_type_parser`]: `SORT_PROP=0`, `SORT_TYPE=1`). A well-formed
/// v2 shard that genuinely only uses `Sort 0` also has this pool, but then every
/// sort is `sort(0)` (in-bounds), so this predicate only ever changes behaviour
/// for the OOB `sort(N>=1)` form that the stale importer emitted.
fn is_legacy_raw_universe_pool(levels: &[Level]) -> bool {
    matches!(levels, [only] if *only == Level::zero())
}

/// Resolve the level of a `Sort` expr, tolerating the legacy coq_v/fstar
/// raw-universe-value encoding losslessly.
///
/// Normal path: `idx` is a level-pool index → return `levels[idx]`.
///
/// Legacy path (only when the pool is the bare zero sentinel and `idx` is out of
/// bounds): the importer wrote the raw universe **value** `idx` rather than a
/// pool index, per the documented `v_type_parser` convention. `sort(0)` is
/// `Sort 0` and `sort(N)` is `Sort N` = `succ^N(zero)`. This reads the legacy
/// bytes correctly — it does not invent data: the universe value is exactly what
/// the importer recorded.
fn resolve_sort_level(levels: &[Level], idx: u32) -> Result<Level, String> {
    if (idx as usize) < levels.len() {
        return get_level_ref(levels, idx);
    }
    if is_legacy_raw_universe_pool(levels) {
        let mut level = Level::zero();
        for _ in 0..idx {
            level = Level::succ(level);
        }
        return Ok(level);
    }
    Err(format!(
        "level index {idx} out of bounds during reconstruction"
    ))
}

// Returns the shared `Arc` of an already-built child (a refcount bump, NOT a
// deep copy) so a node referenced by K parents is ONE allocation (F2,
// `designs/2026-07-06-carrier-whnf-perf.md`) — preserving the shard's DAG
// sharing so the kernel's `Arc::ptr_eq` structural-equality fast path (F1) fires
// during verification instead of re-walking each shared subtree K times.
fn get_expr_ref(exprs: &[Option<Arc<Expr>>], idx: u32) -> Result<Arc<Expr>, String> {
    exprs
        .get(idx as usize)
        .ok_or_else(|| format!("expression index {idx} out of bounds during reconstruction"))?
        .clone()
        .ok_or_else(|| format!("expression index {idx} referenced before it was reconstructed"))
}

fn binder_info_from_u8(value: u8) -> Result<BinderInfo, String> {
    match value {
        0 => Ok(BinderInfo::Default),
        1 => Ok(BinderInfo::Implicit),
        2 => Ok(BinderInfo::StrictImplicit),
        3 => Ok(BinderInfo::InstImplicit),
        // Unknown binder kinds from future Lean 4 versions (e.g. 0xA2 in v4.27+).
        // Treat as explicit, matching clean-olean's convert_binder_info behavior.
        _ => Ok(BinderInfo::Default),
    }
}

fn read_expr_u16(expr: &FlatExpr, offset: usize) -> Result<u16, String> {
    let bytes = read_bytes(&expr.data, offset, 2, "FlatExpr")?;
    Ok(u16::from_le_bytes([bytes[0], bytes[1]]))
}

fn read_expr_u32(expr: &FlatExpr, offset: usize) -> Result<u32, String> {
    let bytes = read_bytes(&expr.data, offset, 4, "FlatExpr")?;
    Ok(u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]))
}

fn read_expr_u64(expr: &FlatExpr, offset: usize) -> Result<u64, String> {
    let bytes = read_bytes(&expr.data, offset, 8, "FlatExpr")?;
    Ok(u64::from_le_bytes([
        bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
    ]))
}

fn read_level_u32(level: &FlatLevel, offset: usize) -> Result<u32, String> {
    let bytes = read_bytes(&level.data, offset, 4, "FlatLevel")?;
    Ok(u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]))
}

fn read_bytes<'a>(
    data: &'a [u8],
    offset: usize,
    width: usize,
    kind: &str,
) -> Result<&'a [u8], String> {
    let end = offset
        .checked_add(width)
        .ok_or_else(|| format!("{kind} read overflow at offset {offset}"))?;
    data.get(offset..end)
        .ok_or_else(|| format!("{kind} read out of bounds at offset {offset}"))
}

#[cfg(test)]
mod subdag_tests {
    use super::*;

    /// A topologically-ordered arena (children at lower indices than parents),
    /// using only exprs that need no level/string table: bvars, app, lam, pi.
    fn sample_arena() -> Vec<FlatExpr> {
        vec![
            FlatExpr::bvar(0),      // 0
            FlatExpr::bvar(1),      // 1
            FlatExpr::app(0, 1),    // 2  = (#0 #1)
            FlatExpr::lam(0, 0, 2), // 3  = λ(ty=#0). #2
            FlatExpr::pi(0, 1, 3),  // 4  = Π(ty=#1). #3
        ]
    }

    /// THE soundness invariant for the lazy/mmap loader: the demand sub-DAG fold
    /// must produce an `Expr` identical to indexing the full prefix reconstruct.
    #[test]
    fn single_subdag_matches_full_reconstruct() {
        let exprs = sample_arena();
        let levels: Vec<FlatLevel> = Vec::new();
        let strings: Vec<String> = Vec::new();
        let level_lists: Vec<u32> = Vec::new();
        for root in 0..exprs.len() as u32 {
            let full = reconstruct_from_shard_with_level_lists(
                &exprs,
                &levels,
                &strings,
                &level_lists,
                root,
            )
            .expect("full reconstruct should succeed");
            let sub = reconstruct_single_subdag(&exprs, &levels, &strings, &level_lists, root)
                .expect("sub-DAG reconstruct should succeed");
            assert_eq!(
                full, sub,
                "sub-DAG fold diverged from full reconstruct at root {root}"
            );
        }
    }

    /// THE soundness invariant for the DEMAND-PAGED mmap loader: the reader-backed
    /// fold (`reconstruct_single_subdag_with_reader`, which the mmap source uses to
    /// touch only reachable expr bytes) must produce an `Expr` byte-identical to the
    /// in-memory slice fold for every root. The reader here just indexes the same
    /// slice, isolating the "source of each FlatExpr" as the only variable.
    #[test]
    fn mmap_subdag_matches_slice_subdag() {
        let exprs = sample_arena();
        let levels: Vec<FlatLevel> = Vec::new();
        let strings: Vec<String> = Vec::new();
        let level_lists: Vec<u32> = Vec::new();
        let read_flat = |i: u32| -> Result<FlatExpr, String> {
            exprs
                .get(i as usize)
                .copied()
                .ok_or_else(|| format!("oob {i}"))
        };
        for root in 0..exprs.len() as u32 {
            let slice = reconstruct_single_subdag(&exprs, &levels, &strings, &level_lists, root)
                .expect("slice sub-DAG reconstruct should succeed");
            let reader = reconstruct_single_subdag_with_reader(
                read_flat,
                exprs.len() as u32,
                &levels,
                &strings,
                &level_lists,
                root,
            )
            .expect("reader sub-DAG reconstruct should succeed");
            assert_eq!(
                slice, reader,
                "reader-backed sub-DAG diverged from slice sub-DAG at root {root}"
            );
        }
    }

    /// Real-data soundness validation: on an actual `.mathverse` shard, the demand
    /// fold must be byte-identical to the full reconstruct wherever BOTH succeed.
    /// Opt-in (set `CLEAN_TEST_SHARD` to a real shard path); skips otherwise so CI
    /// without the corpus stays green. (Err,Ok) is allowed and counted: the full
    /// path truncates its whole prefix at the first bad node, so the demand fold can
    /// legitimately reconstruct a later root whose own sub-DAG is clean — that is
    /// MORE complete, never a divergence. (Ok,Err) would be a regression and panics.
    #[test]
    fn real_shard_subdag_matches_full_reconstruct() {
        let Ok(path) = std::env::var("CLEAN_TEST_SHARD") else {
            eprintln!("skip: set CLEAN_TEST_SHARD to a real .mathverse file to run");
            return;
        };
        let reader = crate::shard::ShardReader::from_file(&path).expect("load real shard");
        let (exprs, levels, strings, ll) = (
            &reader.exprs,
            &reader.levels,
            &reader.strings,
            &reader.level_lists,
        );
        // Collect each constant's type/value expr roots (value-less = out-of-bounds
        // sentinel, skipped by the bounds guard). Spread-sample to ~4000 for speed.
        let mut roots: Vec<u32> = Vec::new();
        for c in &reader.constants {
            roots.push(c.type_idx);
            roots.push(c.value_idx);
        }
        roots.sort_unstable();
        roots.dedup();
        let stride = (roots.len() / 4000).max(1);
        let (mut byte_identical, mut sub_more_complete, mut both_err) = (0u64, 0u64, 0u64);
        for &idx in roots.iter().step_by(stride) {
            if (idx as usize) >= exprs.len() {
                continue;
            }
            let full = reconstruct_from_shard_with_level_lists(exprs, levels, strings, ll, idx);
            let sub = reconstruct_single_subdag(exprs, levels, strings, ll, idx);
            match (full, sub) {
                (Ok(a), Ok(b)) => {
                    assert_eq!(a, b, "REAL-DATA DIVERGENCE: demand fold != full reconstruct at expr {idx} of {path}");
                    byte_identical += 1;
                }
                (Ok(_), Err(e)) => {
                    panic!("REGRESSION: demand fold failed where full reconstruct succeeded at {idx}: {e}")
                }
                (Err(_), Ok(_)) => sub_more_complete += 1,
                (Err(_), Err(_)) => both_err += 1,
            }
        }
        eprintln!(
            "REAL SHARD {path}: {} constants; byte_identical={byte_identical} \
             sub_more_complete={sub_more_complete} both_err={both_err}",
            reader.constants.len()
        );
        assert!(
            byte_identical > 0,
            "validated nothing — empty/garbled shard?"
        );
    }

    /// A broken node the root never references must not affect the sub-DAG —
    /// demonstrating the fold only touches reachable indices (the memory win) while
    /// staying verdict-identical to the full path for the requested root.
    #[test]
    fn subdag_ignores_unreachable_bad_node() {
        let mut exprs = sample_arena(); // root 3 reaches {0,1,2,3}, never 5
                                        // A dangling reference (out-of-bounds children) is unreconstructable, like
                                        // an UNSUPPORTED node, without needing clean-kernel's private flag bits.
        exprs.push(FlatExpr::app(999, 999)); // index 5, unreachable from root 3
        let levels: Vec<FlatLevel> = Vec::new();
        let strings: Vec<String> = Vec::new();
        let level_lists: Vec<u32> = Vec::new();
        let sub = reconstruct_single_subdag(&exprs, &levels, &strings, &level_lists, 3)
            .expect("sub-DAG of 3 must succeed despite an unrelated unsupported node");
        let full =
            reconstruct_from_shard_with_level_lists(&exprs, &levels, &strings, &level_lists, 3)
                .expect("full reconstruct of root 3");
        assert_eq!(full, sub);
    }
}
