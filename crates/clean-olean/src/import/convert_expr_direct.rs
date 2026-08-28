// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Direct binary-to-kernel expression conversion (#2428).
//!
//! Merges the two-phase pipeline (binary → ParsedExpr → Expr) into a single
//! pass (binary → Expr with hash-consing), roughly halving heap allocations
//! during olean import.
//!
//! Used by the production load path (Phase 2, #2428) and by tests.

use super::convert_expr::{convert_binder_info, convert_level, hash_str, intern_expr};
use super::{ExprInternCache, ExprSharingStats, ImportError};
use crate::error::OleanError;
use crate::expr::expr_tags;
use crate::expr::{ParsedBinderInfo, ParsedLiteral, EXPR_DATA_SCALAR_BYTES};
use crate::region::{is_ptr, is_scalar, unbox_scalar, CompactedRegion};
use clean_kernel::expr::{BigNat, BinderInfo, Expr, ExprKind, FVarId, LevelVec, Literal, MDataMap};
use clean_kernel::name::Name;
use hashbrown::HashMap;
use smallvec::SmallVec;
use std::sync::Arc;

/// Memo of already-converted expression nodes, keyed by their pointer INSIDE
/// ONE compacted region (#import-dag-memo).
///
/// A `.olean` compacted region stores `Expr` as a shared DAG: Lean hash-conses
/// every subterm, so a single node is typically referenced from many parents.
/// [`read_and_convert_expr`] walks that DAG as a TREE — it re-reads, re-decodes
/// and re-interns a shared subterm once per PATH that reaches it — so its work
/// is proportional to the number of root-to-node paths, not to the number of
/// nodes. Measured on Lean v4.30.0-rc2 `Init` (64-module sample): 978_138
/// distinct nodes but 48_876_364 memo-less node visits (~50x); the `.olean.private`
/// proof-body regions alone amplify 56.7x on average and
/// `Init/Data/BitVec/Lemmas.olean.private` amplifies 165x (373_990 nodes ->
/// 61_758_674 visits). This memo collapses that back to one visit per node.
///
/// SOUNDNESS: conversion is a PURE function of `(region, ptr)` — `name` is used
/// only to label error messages, and nothing else in [`parse_ptr`] reads mutable
/// state that could make the same pointer decode differently. Reusing the first
/// result for a repeated pointer therefore yields the byte-identical `Expr` the
/// unmemoized walk would have built, so the kernel sees exactly the same
/// constants. Failures are NOT memoized: a pointer that errors is re-walked and
/// re-reported under the next constant's name, preserving today's diagnostics.
///
/// REGION SCOPING (the one way this could go wrong): keys are region-relative
/// pointers, so a cache MUST NOT outlive the `CompactedRegion` it was filled
/// from — two different regions can hand out the same pointer value for
/// different nodes. The type therefore carries no `Default`: a cache is built by
/// [`RegionPtrCache::for_region`] next to the region it belongs to, or by
/// [`RegionPtrCache::disabled`] for callers that keep the historical
/// unmemoized behavior.
pub(crate) struct RegionPtrCache {
    map: HashMap<u64, Arc<Expr>>,
    enabled: bool,
}

impl RegionPtrCache {
    /// A live memo for exactly one [`CompactedRegion`]. The caller must drop it
    /// before the region it was filled from goes away or is replaced.
    pub(crate) fn for_region() -> Self {
        Self {
            map: HashMap::new(),
            enabled: true,
        }
    }

    /// A memo that never stores or serves anything, so the conversion walk is
    /// bit-for-bit the historical one (same visit order, same intern-call and
    /// cache-hit statistics).
    ///
    /// This is the DIFFERENTIAL ORACLE for the memo, not a production mode: no
    /// shipping caller wants the 49.97x-amplified walk back. Its whole job is to
    /// let a test convert the same region twice — once disabled, once enabled —
    /// and assert the two `Expr`s are identical, which is the evidence that
    /// memoizing changed only the cost and not the output. Test-only so the
    /// slow path cannot be reached by accident from a shipping code path.
    #[cfg(test)]
    pub(crate) fn disabled() -> Self {
        Self {
            map: HashMap::new(),
            enabled: false,
        }
    }

    fn is_enabled(&self) -> bool {
        self.enabled
    }

    fn get(&self, ptr: u64) -> Option<Arc<Expr>> {
        if self.enabled {
            self.map.get(&ptr).map(Arc::clone)
        } else {
            None
        }
    }

    fn insert(&mut self, ptr: u64, expr: &Arc<Expr>) {
        if self.enabled {
            self.map.insert(ptr, Arc::clone(expr));
        }
    }
}

/// Work item for direct binary-to-kernel expression conversion.
enum DirectConvertWork {
    /// Read binary data at this pointer and produce kernel Expr
    Parse(u64),
    /// Record the just-built result on top of `results` as the conversion of
    /// this region pointer. Pushed BEFORE the matching `Build*` item so it pops
    /// AFTER it, when the parent node exists.
    Memo(u64),
    /// Build App from top 2 results
    BuildApp,
    /// Build Lam from top 2 results
    BuildLam(BinderInfo),
    /// Build Pi from top 2 results
    BuildPi(BinderInfo),
    /// Build Let from top 3 results
    BuildLet(Name, bool),
    /// Build MData from top result
    BuildMData,
    /// Build Proj from top result
    BuildProj(Name, u32),
}

/// Read .olean binary data and produce interned kernel `Expr` in a single pass.
///
/// The `intern` cache is shared across all constants in a module for
/// cross-constant expression deduplication (#2383).
///
/// Test-only, and paired with [`RegionPtrCache::disabled`]: every shipping
/// caller now goes through [`read_and_convert_expr_with_memo`] with a live
/// region-scoped memo. This 4-argument form is retained purely as the
/// unmemoized reference walk that the memo is differentially checked against.
#[cfg(test)]
pub(crate) fn read_and_convert_expr(
    region: &CompactedRegion<'_>,
    initial_ptr: u64,
    name: &str,
    intern: &mut ExprInternCache,
) -> Result<(Expr, ExprSharingStats), ImportError> {
    read_and_convert_expr_with_memo(
        region,
        initial_ptr,
        name,
        intern,
        &mut RegionPtrCache::disabled(),
    )
}

/// [`read_and_convert_expr`] with a caller-owned region-pointer memo, so a
/// shared subterm is decoded ONCE per region instead of once per path that
/// reaches it (#import-dag-memo).
///
/// # REQUIRES
/// - `memo` was filled only from THIS `region` (see [`RegionPtrCache`]).
///
/// # ENSURES
/// - Returns the same `Expr` the unmemoized walk returns, for every input.
/// - `ExprSharingStats` counts only the intern calls actually performed, so a
///   memo hit is not double-counted as a hash-cons hit.
pub(crate) fn read_and_convert_expr_with_memo(
    region: &CompactedRegion<'_>,
    initial_ptr: u64,
    name: &str,
    intern: &mut ExprInternCache,
    memo: &mut RegionPtrCache,
) -> Result<(Expr, ExprSharingStats), ImportError> {
    let mut work: Vec<DirectConvertWork> = vec![DirectConvertWork::Parse(initial_ptr)];
    let mut results: SmallVec<[Arc<Expr>; 32]> = SmallVec::new();
    let cache_size_before: u64 = intern.total_entries;
    let mut cache_hits: u64 = 0;
    let mut total_intern_calls: u64 = 0;

    macro_rules! do_intern {
        ($cache:expr, $e:expr) => {{
            let (arc, was_hit) = intern_expr($cache, $e);
            total_intern_calls += 1;
            if was_hit {
                cache_hits += 1;
            }
            arc
        }};
    }

    let mut iterations = 0usize;
    const MAX_ITERATIONS: usize = 100_000_000;

    while let Some(item) = work.pop() {
        iterations += 1;
        if iterations > MAX_ITERATIONS {
            return Err(ImportError::ExprConversion {
                name: name.to_string(),
                message: "Expression too complex (direct converter)".to_string(),
            });
        }

        match item {
            DirectConvertWork::Parse(ptr) => {
                // Already decoded under this region: reuse it instead of
                // re-walking the whole subtree hanging off `ptr`.
                if let Some(hit) = memo.get(ptr) {
                    results.push(hit);
                    continue;
                }
                parse_ptr(
                    region,
                    ptr,
                    name,
                    intern,
                    memo,
                    &mut work,
                    &mut results,
                    &mut total_intern_calls,
                    &mut cache_hits,
                )?;
            }
            DirectConvertWork::Memo(ptr) => {
                // The matching `Build*` item ran immediately before this one, so
                // the node for `ptr` is on top of `results`.
                if let Some(top) = results.last() {
                    memo.insert(ptr, top);
                }
            }
            DirectConvertWork::BuildApp => {
                let arg = results.pop().expect("stack balance invariant");
                let func = results.pop().expect("stack balance invariant");
                results.push(do_intern!(
                    intern,
                    Expr::from_kind(ExprKind::App(func, arg))
                ));
            }
            DirectConvertWork::BuildLam(info) => {
                let body = results.pop().expect("stack balance invariant");
                let ty = results.pop().expect("stack balance invariant");
                results.push(do_intern!(
                    intern,
                    Expr::from_kind(ExprKind::Lam(info.into(), ty, body))
                ));
            }
            DirectConvertWork::BuildPi(info) => {
                let body = results.pop().expect("stack balance invariant");
                let ty = results.pop().expect("stack balance invariant");
                results.push(do_intern!(
                    intern,
                    Expr::from_kind(ExprKind::Pi(info.into(), ty, body))
                ));
            }
            DirectConvertWork::BuildLet(let_name, nondep) => {
                let body = results.pop().expect("stack balance invariant");
                let val = results.pop().expect("stack balance invariant");
                let ty = results.pop().expect("stack balance invariant");
                let kind = ExprKind::Let(let_name, ty, val, body, nondep);
                results.push(do_intern!(intern, Expr::from_kind(kind)));
            }
            DirectConvertWork::BuildMData => {
                let inner = results.pop().expect("stack balance invariant");
                results.push(do_intern!(
                    intern,
                    Expr::from_kind(ExprKind::MData(MDataMap::new(), inner))
                ));
            }
            DirectConvertWork::BuildProj(struct_name, idx) => {
                let inner = results.pop().expect("stack balance invariant");
                results.push(do_intern!(
                    intern,
                    Expr::from_kind(ExprKind::Proj(struct_name, idx, inner))
                ));
            }
        }
    }

    debug_assert_eq!(results.len(), 1);
    let stats = ExprSharingStats {
        total_intern_calls,
        cache_hits,
        unique_exprs: intern.total_entries - cache_size_before,
    };
    let result_arc = results.pop().expect("stack balance invariant");
    Ok((
        Arc::try_unwrap(result_arc).unwrap_or_else(|arc| (*arc).clone()),
        stats,
    ))
}

/// Parse a single pointer from the binary region and push work items + results.
fn parse_ptr(
    region: &CompactedRegion<'_>,
    ptr: u64,
    name: &str,
    intern: &mut ExprInternCache,
    memo: &mut RegionPtrCache,
    work: &mut Vec<DirectConvertWork>,
    results: &mut SmallVec<[Arc<Expr>; 32]>,
    total_intern_calls: &mut u64,
    cache_hits: &mut u64,
) -> Result<(), ImportError> {
    macro_rules! do_intern {
        ($cache:expr, $e:expr) => {{
            let (arc, was_hit) = intern_expr($cache, $e);
            *total_intern_calls += 1;
            if was_hit {
                *cache_hits += 1;
            }
            arc
        }};
    }

    if is_scalar(ptr) {
        let idx = unbox_scalar(ptr);
        if idx > u64::from(Expr::MAX_BVAR_INDEX) {
            return Err(ImportError::ExprConversion {
                name: name.to_string(),
                message: format!("bvar index too large: {idx}"),
            });
        }
        results.push(do_intern!(intern, Expr::bvar(idx as u32)));
        return Ok(());
    }
    if !is_ptr(ptr) {
        return Err(ImportError::Parse(OleanError::Region(
            "Null expression pointer".into(),
        )));
    }

    let offset = region.ptr_to_offset(ptr)?;
    let header = region.read_header_at(offset)?;
    CompactedRegion::require_expr_fields(&header, offset)?;
    let field_base = offset + 8;
    let scalar_base = field_base + header.other as usize * 8;

    // Nodes whose whole result is pushed to `results` by this call (no `Build*`
    // step follows) are memoized here; interior nodes push a `Memo(ptr)` item
    // that fires once their `Build*` step has produced them.
    let is_leaf = matches!(
        header.tag,
        expr_tags::BVAR | expr_tags::FVAR | expr_tags::SORT | expr_tags::CONST | expr_tags::LIT
    );

    let parsed = match header.tag {
        expr_tags::BVAR => parse_bvar(
            region,
            field_base,
            name,
            intern,
            results,
            total_intern_calls,
            cache_hits,
        ),
        expr_tags::FVAR => {
            let id_ptr = region.read_u64_at(field_base)?;
            let id_str = region.resolve_name_ptr(id_ptr)?;
            results.push(do_intern!(
                intern,
                Expr::fvar(FVarId::new(hash_str(&id_str)))
            ));
            Ok(())
        }
        expr_tags::MVAR => Err(ImportError::UnsupportedMVar(name.to_string())),
        expr_tags::SORT => {
            let level_ptr = region.read_u64_at(field_base)?;
            let parsed_level = region.resolve_level_ptr(level_ptr, 0)?;
            let level = convert_level(name, &parsed_level)?;
            results.push(do_intern!(intern, Expr::sort(level)));
            Ok(())
        }
        expr_tags::CONST => parse_const(
            region,
            field_base,
            name,
            intern,
            results,
            total_intern_calls,
            cache_hits,
        ),
        expr_tags::LIT => parse_lit(
            region,
            field_base,
            intern,
            results,
            total_intern_calls,
            cache_hits,
        ),
        expr_tags::APP => {
            let fn_ptr = region.read_u64_at(field_base)?;
            let arg_ptr = region.read_u64_at(field_base + 8)?;
            if memo.is_enabled() {
                work.push(DirectConvertWork::Memo(ptr));
            }
            work.push(DirectConvertWork::BuildApp);
            work.push(DirectConvertWork::Parse(arg_ptr));
            work.push(DirectConvertWork::Parse(fn_ptr));
            Ok(())
        }
        expr_tags::LAM => {
            let type_ptr = region.read_u64_at(field_base + 8)?;
            let body_ptr = region.read_u64_at(field_base + 16)?;
            // binderInfo is a SEPARATE scalar field that follows the cached
            // 8-byte `Expr.Data` (hash/flags/looseBVarRange — it does NOT contain
            // binderInfo; see Lean `Expr.lean`). Reading `scalar_base` grabbed the
            // Data's first byte (hash low byte) → almost always 0 = `Default`,
            // silently dropping `Implicit`/`InstImplicit` on EVERY imported binder
            // (masked only for the ~handful of List ops clean hand-registers as
            // builtins, e.g. `List.map`). Read after the 8-byte Data scalar.
            let bi = convert_binder_info(ParsedBinderInfo::from_u8(
                region.bytes_at(scalar_base + EXPR_DATA_SCALAR_BYTES, 1)?[0],
            ));
            if memo.is_enabled() {
                work.push(DirectConvertWork::Memo(ptr));
            }
            work.push(DirectConvertWork::BuildLam(bi));
            work.push(DirectConvertWork::Parse(body_ptr));
            work.push(DirectConvertWork::Parse(type_ptr));
            Ok(())
        }
        expr_tags::FORALL_E => {
            let type_ptr = region.read_u64_at(field_base + 8)?;
            let body_ptr = region.read_u64_at(field_base + 16)?;
            // See LAM above: binderInfo follows the 8-byte cached `Expr.Data`.
            let bi = convert_binder_info(ParsedBinderInfo::from_u8(
                region.bytes_at(scalar_base + EXPR_DATA_SCALAR_BYTES, 1)?[0],
            ));
            if memo.is_enabled() {
                work.push(DirectConvertWork::Memo(ptr));
            }
            work.push(DirectConvertWork::BuildPi(bi));
            work.push(DirectConvertWork::Parse(body_ptr));
            work.push(DirectConvertWork::Parse(type_ptr));
            Ok(())
        }
        expr_tags::LET_E => {
            let name_ptr = region.read_u64_at(field_base)?;
            let type_ptr = region.read_u64_at(field_base + 8)?;
            let value_ptr = region.read_u64_at(field_base + 16)?;
            let body_ptr = region.read_u64_at(field_base + 24)?;
            let decl_name_str = region.resolve_name_ptr(name_ptr)?;
            // Like binderInfo above, `nondep` follows the cached Expr.Data
            // word. Reading the hash byte made nearly every let look nondep.
            let nondep = region.bytes_at(scalar_base + EXPR_DATA_SCALAR_BYTES, 1)?[0] != 0;
            if memo.is_enabled() {
                work.push(DirectConvertWork::Memo(ptr));
            }
            work.push(DirectConvertWork::BuildLet(
                Name::from_string(&decl_name_str),
                nondep,
            ));
            work.push(DirectConvertWork::Parse(body_ptr));
            work.push(DirectConvertWork::Parse(value_ptr));
            work.push(DirectConvertWork::Parse(type_ptr));
            Ok(())
        }
        expr_tags::MDATA => {
            let expr_ptr = region.read_u64_at(field_base + 8)?;
            if memo.is_enabled() {
                work.push(DirectConvertWork::Memo(ptr));
            }
            work.push(DirectConvertWork::BuildMData);
            work.push(DirectConvertWork::Parse(expr_ptr));
            Ok(())
        }
        expr_tags::PROJ => {
            if memo.is_enabled() {
                work.push(DirectConvertWork::Memo(ptr));
            }
            parse_proj(region, field_base, name, work)
        }
        _ => Err(ImportError::Parse(OleanError::InvalidObjectTag {
            tag: header.tag,
            offset,
        })),
    };

    // Leaves are complete the moment their branch returns, so memoize them here.
    // Errors are deliberately NOT memoized (see `RegionPtrCache`).
    if parsed.is_ok() && is_leaf {
        if let Some(top) = results.last() {
            memo.insert(ptr, top);
        }
    }
    parsed
}

fn parse_bvar(
    region: &CompactedRegion<'_>,
    field_base: usize,
    name: &str,
    intern: &mut ExprInternCache,
    results: &mut SmallVec<[Arc<Expr>; 32]>,
    total_intern_calls: &mut u64,
    cache_hits: &mut u64,
) -> Result<(), ImportError> {
    let idx_ptr = region.read_u64_at(field_base)?;
    let idx = if is_scalar(idx_ptr) {
        unbox_scalar(idx_ptr)
    } else if is_ptr(idx_ptr) {
        region.read_nat_value(idx_ptr)?
    } else {
        0
    };
    if idx > u64::from(Expr::MAX_BVAR_INDEX) {
        return Err(ImportError::ExprConversion {
            name: name.to_string(),
            message: format!("bvar index too large: {idx}"),
        });
    }
    let (arc, was_hit) = intern_expr(intern, Expr::bvar(idx as u32));
    *total_intern_calls += 1;
    if was_hit {
        *cache_hits += 1;
    }
    results.push(arc);
    Ok(())
}

fn parse_const(
    region: &CompactedRegion<'_>,
    field_base: usize,
    name: &str,
    intern: &mut ExprInternCache,
    results: &mut SmallVec<[Arc<Expr>; 32]>,
    total_intern_calls: &mut u64,
    cache_hits: &mut u64,
) -> Result<(), ImportError> {
    let name_ptr = region.read_u64_at(field_base)?;
    let levels_ptr = region.read_u64_at(field_base + 8)?;
    let const_name_str = region.resolve_name_ptr(name_ptr)?;
    let parsed_levels = region.read_level_list(levels_ptr)?;
    let levels: LevelVec = parsed_levels
        .iter()
        .map(|l| convert_level(name, l))
        .collect::<Result<_, _>>()?;
    let (arc, was_hit) = intern_expr(
        intern,
        Expr::const_(Name::interned(&const_name_str), levels),
    );
    *total_intern_calls += 1;
    if was_hit {
        *cache_hits += 1;
    }
    results.push(arc);
    Ok(())
}

fn parse_lit(
    region: &CompactedRegion<'_>,
    field_base: usize,
    intern: &mut ExprInternCache,
    results: &mut SmallVec<[Arc<Expr>; 32]>,
    total_intern_calls: &mut u64,
    cache_hits: &mut u64,
) -> Result<(), ImportError> {
    let lit_ptr = region.read_u64_at(field_base)?;
    let parsed_lit = region.read_literal(lit_ptr)?;
    let expr = match &parsed_lit {
        ParsedLiteral::Nat(n) => {
            let kernel_bignat = match n {
                crate::expr::BigNat::Small(v) => BigNat::Small(*v),
                crate::expr::BigNat::Big(limbs) => BigNat::from_limbs(limbs.clone()),
            };
            Expr::from_kind(ExprKind::Lit(Literal::Nat(kernel_bignat)))
        }
        ParsedLiteral::String(s) => {
            Expr::from_kind(ExprKind::Lit(Literal::String(s.clone().into())))
        }
    };
    let (arc, was_hit) = intern_expr(intern, expr);
    *total_intern_calls += 1;
    if was_hit {
        *cache_hits += 1;
    }
    results.push(arc);
    Ok(())
}

fn parse_proj(
    region: &CompactedRegion<'_>,
    field_base: usize,
    name: &str,
    work: &mut Vec<DirectConvertWork>,
) -> Result<(), ImportError> {
    let type_name_ptr = region.read_u64_at(field_base)?;
    let idx_ptr = region.read_u64_at(field_base + 8)?;
    let struct_ptr = region.read_u64_at(field_base + 16)?;
    let type_name_str = region.resolve_name_ptr(type_name_ptr)?;
    let idx = if is_scalar(idx_ptr) {
        unbox_scalar(idx_ptr)
    } else if is_ptr(idx_ptr) {
        region.read_nat_value(idx_ptr).unwrap_or(0)
    } else {
        0
    };
    if idx > u64::from(u32::MAX) {
        return Err(ImportError::ExprConversion {
            name: name.to_string(),
            message: format!("projection index too large: {idx}"),
        });
    }
    work.push(DirectConvertWork::BuildProj(
        Name::interned(&type_name_str),
        idx as u32,
    ));
    work.push(DirectConvertWork::Parse(struct_ptr));
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    const TEST_BASE_ADDR: u64 = 0x0010_0000;

    fn boxed_scalar(value: u64) -> u64 {
        (value << 1) | 1
    }

    fn write_header(data: &mut [u8], offset: usize, other: u8, tag: u8) {
        data[offset..offset + 4].copy_from_slice(&0i32.to_le_bytes());
        data[offset + 4..offset + 6].copy_from_slice(&0u16.to_le_bytes());
        data[offset + 6] = other;
        data[offset + 7] = tag;
    }

    #[test]
    fn underdeclared_app_fails_before_direct_conversion_reads_adjacent_data() {
        let mut data = vec![0u8; 128];
        let app_offset = 64;
        write_header(&mut data, app_offset, 1, expr_tags::APP);
        data[app_offset + 8..app_offset + 16].copy_from_slice(&boxed_scalar(0).to_le_bytes());
        // This plausible adjacent word must never be accepted as the missing
        // second App field.
        data[app_offset + 16..app_offset + 24].copy_from_slice(&boxed_scalar(1).to_le_bytes());

        let region = CompactedRegion::new(&data, TEST_BASE_ADDR);
        let mut intern = ExprInternCache::default();
        let error = read_and_convert_expr(
            &region,
            region.offset_to_ptr(app_offset),
            "malformed_app",
            &mut intern,
        )
        .expect_err("the production direct path must share the field-count gate");
        assert!(
            matches!(
                error,
                ImportError::Parse(OleanError::Region(ref message))
                    if message.contains("malformed Expr")
            ),
            "unexpected error: {error:?}"
        );
    }

    #[test]
    fn direct_let_reads_nondep_after_cached_expr_data() {
        let mut data = vec![0u8; 192];
        let let_offset = 64;
        write_header(&mut data, let_offset, 4, expr_tags::LET_E);
        for field in 0..4 {
            let start = let_offset + 8 + field * 8;
            data[start..start + 8].copy_from_slice(&boxed_scalar(0).to_le_bytes());
        }
        data[let_offset + 40] = 0xff; // cached Expr.Data hash byte
        data[let_offset + 48] = 0; // nondep = false

        let region = CompactedRegion::new(&data, TEST_BASE_ADDR);
        let mut intern = ExprInternCache::default();
        let (expr, _) = read_and_convert_expr(
            &region,
            region.offset_to_ptr(let_offset),
            "dependent_let",
            &mut intern,
        )
        .expect("well-formed dependent let must convert");
        assert!(
            matches!(expr.kind(), ExprKind::Let(_, _, _, _, false)),
            "cached Expr.Data must not be decoded as nondep: {expr:?}"
        );
    }

    /// Build `App(App(s, s), App(s, s))` where every inner `App` is the SAME
    /// region object, so the node is reachable by four distinct paths. This is
    /// the shape the memo exists for (#import-dag-memo).
    fn shared_dag_region() -> (Vec<u8>, usize) {
        let mut data = vec![0u8; 256];
        let leaf = 64; // Expr.bvar 0
        write_header(&mut data, leaf, 1, expr_tags::BVAR);
        data[leaf + 8..leaf + 16].copy_from_slice(&boxed_scalar(0).to_le_bytes());

        let shared = 96; // App(leaf, leaf) — referenced twice by `root`
        write_header(&mut data, shared, 2, expr_tags::APP);
        let leaf_ptr = TEST_BASE_ADDR + leaf as u64;
        data[shared + 8..shared + 16].copy_from_slice(&leaf_ptr.to_le_bytes());
        data[shared + 16..shared + 24].copy_from_slice(&leaf_ptr.to_le_bytes());

        let root = 128; // App(shared, shared)
        write_header(&mut data, root, 2, expr_tags::APP);
        let shared_ptr = TEST_BASE_ADDR + shared as u64;
        data[root + 8..root + 16].copy_from_slice(&shared_ptr.to_le_bytes());
        data[root + 16..root + 24].copy_from_slice(&shared_ptr.to_le_bytes());
        (data, root)
    }

    #[test]
    fn test_ptr_memo_shared_dag_matches_unmemoized_conversion() {
        let (data, root) = shared_dag_region();
        let region = CompactedRegion::new(&data, TEST_BASE_ADDR);
        let ptr = region.offset_to_ptr(root);

        let mut plain_cache = ExprInternCache::default();
        let (plain, _) = read_and_convert_expr(&region, ptr, "dag", &mut plain_cache)
            .expect("unmemoized conversion must succeed");

        let mut memo_cache = ExprInternCache::default();
        let mut memo = RegionPtrCache::for_region();
        let (memoized, _) =
            read_and_convert_expr_with_memo(&region, ptr, "dag", &mut memo_cache, &mut memo)
                .expect("memoized conversion must succeed");

        assert_eq!(
            plain, memoized,
            "the region-pointer memo must not change the converted Expr"
        );
    }

    #[test]
    fn test_ptr_memo_visits_each_shared_node_once() {
        let (data, root) = shared_dag_region();
        let region = CompactedRegion::new(&data, TEST_BASE_ADDR);
        let ptr = region.offset_to_ptr(root);

        // Without the memo the shared `App` (and both its leaves) are rebuilt
        // once per path, so more intern calls are made than there are nodes.
        let mut plain_cache = ExprInternCache::default();
        let (_, plain_stats) = read_and_convert_expr(&region, ptr, "dag", &mut plain_cache)
            .expect("unmemoized conversion must succeed");

        let mut memo_cache = ExprInternCache::default();
        let mut memo = RegionPtrCache::for_region();
        let (_, memo_stats) =
            read_and_convert_expr_with_memo(&region, ptr, "dag", &mut memo_cache, &mut memo)
                .expect("memoized conversion must succeed");

        assert!(
            memo_stats.total_intern_calls < plain_stats.total_intern_calls,
            "memo must remove repeated visits: {} vs {}",
            memo_stats.total_intern_calls,
            plain_stats.total_intern_calls
        );
        // 3 distinct nodes: bvar leaf, shared App, root App.
        assert_eq!(
            memo_stats.total_intern_calls, 3,
            "each distinct region node must be converted exactly once"
        );
    }
}
