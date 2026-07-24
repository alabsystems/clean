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
use crate::expr::{ParsedBinderInfo, ParsedLiteral};
use crate::region::{is_ptr, is_scalar, unbox_scalar, CompactedRegion};
use clean_kernel::expr::{BigNat, BinderInfo, Expr, ExprKind, FVarId, LevelVec, Literal, MDataMap};
use clean_kernel::name::Name;
use smallvec::SmallVec;
use std::sync::Arc;

/// Work item for direct binary-to-kernel expression conversion.
enum DirectConvertWork {
    /// Read binary data at this pointer and produce kernel Expr
    Parse(u64),
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
pub(crate) fn read_and_convert_expr(
    region: &CompactedRegion,
    initial_ptr: u64,
    name: &str,
    intern: &mut ExprInternCache,
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
                parse_ptr(
                    region,
                    ptr,
                    name,
                    intern,
                    &mut work,
                    &mut results,
                    &mut total_intern_calls,
                    &mut cache_hits,
                )?;
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
    region: &CompactedRegion,
    ptr: u64,
    name: &str,
    intern: &mut ExprInternCache,
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
    let field_base = offset + 8;
    let scalar_base = field_base + header.other as usize * 8;

    match header.tag {
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
                region.bytes_at(scalar_base + 8, 1)?[0],
            ));
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
                region.bytes_at(scalar_base + 8, 1)?[0],
            ));
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
            let nondep = region.bytes_at(scalar_base, 1)?[0] != 0;
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
            work.push(DirectConvertWork::BuildMData);
            work.push(DirectConvertWork::Parse(expr_ptr));
            Ok(())
        }
        expr_tags::PROJ => parse_proj(region, field_base, name, work),
        _ => Err(ImportError::Parse(OleanError::InvalidObjectTag {
            tag: header.tag,
            offset,
        })),
    }
}

fn parse_bvar(
    region: &CompactedRegion,
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
    region: &CompactedRegion,
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
    region: &CompactedRegion,
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
    region: &CompactedRegion,
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
