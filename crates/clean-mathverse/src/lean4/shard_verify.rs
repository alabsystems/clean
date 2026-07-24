// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Reconstruct kernel `Expr`/`Level` values from mathverse shard data and verify
//! shard constants by feeding them through `Environment::add_decl()`.

use clean_kernel::env::{Declaration, EnvError, Environment};
use clean_kernel::expr::{BinderInfo, Expr, FVarId};
use clean_kernel::flat::{FlatError, FlatExpr, FlatFlags, FlatLevel};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use thiserror::Error;

use crate::error::{MathverseError, MathverseResult};
use crate::shard::ShardReader;
use crate::shard_reconstruct::reconstruct_level_params;
use crate::types::{ImportConfidence, NO_VALUE};

/// Results from verifying shard constants.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ShardVerifyResult {
    /// Total constants encountered in the shard.
    pub total: usize,
    /// Constants accepted as theorem/definition-style declarations.
    pub kernel_verified: usize,
    /// Constants accepted as axioms or trust-gated opaque declarations.
    pub axiom_accepted: usize,
    /// Constants that failed reconstruction or kernel verification.
    pub failed: usize,
    /// `(constant name, error)` pairs for failures.
    pub failures: Vec<(String, String)>,
}

#[derive(Clone, Debug, Error)]
enum ShardReconstructError {
    #[error("flat reconstruction error: {0}")]
    Flat(#[from] FlatError),
    #[error("string index {idx} out of range (count: {count})")]
    StringOutOfRange { idx: u32, count: usize },
    #[error("level index {idx} out of range (count: {count})")]
    LevelOutOfRange { idx: u32, count: usize },
    #[error("expression index {idx} out of range (count: {count})")]
    ExprOutOfRange { idx: u32, count: usize },
    #[error("forward level reference {idx} before entry {current}")]
    ForwardLevelRef { idx: u32, current: usize },
    #[error("forward expression reference {idx} before entry {current}")]
    ForwardExprRef { idx: u32, current: usize },
    #[error("invalid flat level tag: {0}")]
    InvalidLevelTag(u8),
    #[error("invalid binder info: {0}")]
    InvalidBinderInfo(u8),
    #[error("unsupported expression (UNSUPPORTED flag set)")]
    UnsupportedExpression,
}

impl From<ShardReconstructError> for MathverseError {
    fn from(value: ShardReconstructError) -> Self {
        match value {
            ShardReconstructError::StringOutOfRange { idx, count } => {
                MathverseError::StringOutOfRange {
                    idx,
                    count: saturating_usize_to_u32(count),
                }
            }
            ShardReconstructError::ExprOutOfRange { idx, count } => {
                MathverseError::ExprOutOfRange {
                    idx,
                    count: saturating_usize_to_u32(count),
                }
            }
            other => MathverseError::Kernel(other.to_string()),
        }
    }
}

type LevelBuild = Result<Level, ShardReconstructError>;
type ExprBuild = Result<Expr, ShardReconstructError>;

/// Reconstruct all shard levels into kernel `Level`s.
pub fn reconstruct_shard_levels(reader: &ShardReader) -> MathverseResult<Vec<Level>> {
    build_level_results(reader)
        .into_iter()
        .collect::<Result<Vec<_>, _>>()
        .map_err(Into::into)
}

/// Reconstruct a single shard expression into a kernel `Expr`.
pub fn reconstruct_shard_expr(reader: &ShardReader, idx: u32) -> MathverseResult<Expr> {
    let level_results = build_level_results(reader);
    let expr_results = build_expr_results(reader, &level_results);
    get_expr_result(&expr_results, idx, reader.exprs.len()).map_err(Into::into)
}

/// Verify all constants in a shard through the kernel type-checker.
pub fn verify_shard(reader: &ShardReader) -> MathverseResult<ShardVerifyResult> {
    let mut env = Environment::new();
    verify_shard_into_env(reader, &mut env)
}

/// Verify shard constants and add them to an existing `Environment`.
///
/// This allows verifying multiple shards with shared declarations already
/// present in `env`.
pub fn verify_shard_into_env(
    reader: &ShardReader,
    env: &mut Environment,
) -> MathverseResult<ShardVerifyResult> {
    let mut result = ShardVerifyResult {
        total: reader.constants.len(),
        ..ShardVerifyResult::default()
    };

    let level_results = build_level_results(reader);
    let expr_results = build_expr_results(reader, &level_results);

    for header in &reader.constants {
        let const_name = constant_name(reader, header.name_idx);
        let type_ = match get_expr_result(&expr_results, header.type_idx, reader.exprs.len()) {
            Ok(type_) => type_,
            Err(err) => {
                push_failure(&mut result, const_name, err.to_string());
                continue;
            }
        };

        let confidence = match ImportConfidence::try_from(header.import_confidence) {
            Ok(confidence) => confidence,
            Err(raw) => {
                push_failure(
                    &mut result,
                    const_name,
                    format!("invalid import confidence: {raw}"),
                );
                continue;
            }
        };

        // Reconstruct declaration-level universe parameter names.
        let level_params = reconstruct_level_params(
            &reader.strings,
            header.level_params_start,
            header.level_params_count,
        )
        .unwrap_or_default();

        let name = Name::from_string(&const_name);

        if header.value_idx == NO_VALUE {
            let decl = Declaration::Axiom {
                name,
                level_params,
                type_,
            };
            match env.add_decl(decl) {
                Ok(()) => result.axiom_accepted += 1,
                Err(err) => push_failure(&mut result, const_name, err.to_string()),
            }
            continue;
        }

        let value = match get_expr_result(&expr_results, header.value_idx, reader.exprs.len()) {
            Ok(value) => value,
            Err(err) => {
                push_failure(&mut result, const_name, err.to_string());
                continue;
            }
        };

        if matches!(confidence, ImportConfidence::Axiomatized) {
            let decl = Declaration::Opaque {
                name,
                level_params,
                type_,
                value,
            };
            match env.add_decl(decl) {
                Ok(()) => result.axiom_accepted += 1,
                Err(err) => push_failure(&mut result, const_name, err.to_string()),
            }
            continue;
        }

        let theorem_decl = Declaration::Theorem {
            name: name.clone(),
            level_params: level_params.clone(),
            type_: type_.clone(),
            value: value.clone(),
        };
        match env.add_decl(theorem_decl) {
            Ok(()) => result.kernel_verified += 1,
            Err(EnvError::TheoremTypeNotProp { .. }) => {
                let definition_decl = Declaration::Definition {
                    name,
                    level_params,
                    type_,
                    value,
                    is_reducible: false,
                };
                match env.add_decl(definition_decl) {
                    Ok(()) => result.kernel_verified += 1,
                    Err(err) => push_failure(&mut result, const_name, err.to_string()),
                }
            }
            Err(err) => push_failure(&mut result, const_name, err.to_string()),
        }
    }

    Ok(result)
}

fn build_level_results(reader: &ShardReader) -> Vec<LevelBuild> {
    let mut built = Vec::with_capacity(reader.levels.len());

    for flat in &reader.levels {
        let level = match flat.tag {
            FlatLevel::TAG_ZERO => Ok(Level::zero()),
            FlatLevel::TAG_SUCC => {
                let inner_idx = read_level_u32(flat, 0);
                get_level_result(&built, inner_idx, reader.levels.len()).map(Level::succ)
            }
            FlatLevel::TAG_MAX => {
                let left_idx = read_level_u32(flat, 0);
                let right_idx = read_level_u32(flat, 4);
                match (
                    get_level_result(&built, left_idx, reader.levels.len()),
                    get_level_result(&built, right_idx, reader.levels.len()),
                ) {
                    (Ok(left), Ok(right)) => Ok(Level::max(left, right)),
                    (Err(err), _) | (_, Err(err)) => Err(err),
                }
            }
            FlatLevel::TAG_IMAX => {
                let left_idx = read_level_u32(flat, 0);
                let right_idx = read_level_u32(flat, 4);
                match (
                    get_level_result(&built, left_idx, reader.levels.len()),
                    get_level_result(&built, right_idx, reader.levels.len()),
                ) {
                    (Ok(left), Ok(right)) => Ok(Level::imax(left, right)),
                    (Err(err), _) | (_, Err(err)) => Err(err),
                }
            }
            FlatLevel::TAG_PARAM => {
                let name_idx = read_level_u32(flat, 0);
                read_string(reader, name_idx).map(|name| Level::param(Name::from_string(name)))
            }
            other => Err(ShardReconstructError::InvalidLevelTag(other)),
        };
        built.push(level);
    }

    built
}

fn build_expr_results(reader: &ShardReader, level_results: &[LevelBuild]) -> Vec<ExprBuild> {
    let mut built = Vec::with_capacity(reader.exprs.len());

    for flat in &reader.exprs {
        let expr = reconstruct_single_expr(reader, flat, level_results, &built);
        built.push(expr);
    }

    built
}

fn reconstruct_single_expr(
    reader: &ShardReader,
    flat: &FlatExpr,
    level_results: &[LevelBuild],
    expr_results: &[ExprBuild],
) -> ExprBuild {
    if flat.flags().contains(FlatFlags::UNSUPPORTED) {
        return Err(ShardReconstructError::UnsupportedExpression);
    }

    match flat.tag()? {
        clean_kernel::flat::FlatTag::BVar => {
            let idx = flat.read_u32(0)?;
            Ok(Expr::bvar(idx))
        }
        clean_kernel::flat::FlatTag::Sort => {
            let level_idx = flat.read_u32(0)?;
            get_level_value(level_results, level_idx).map(Expr::sort)
        }
        clean_kernel::flat::FlatTag::Const => {
            let name_idx = flat.read_u32(0)?;
            let levels_list_idx = flat.read_u32(4)?;
            let name = Name::from_string(read_string(reader, name_idx)?);
            let levels = resolve_level_list(reader, level_results, levels_list_idx)?;
            Ok(Expr::const_(name, levels))
        }
        clean_kernel::flat::FlatTag::App => {
            let fn_idx = flat.read_u32(0)?;
            let arg_idx = flat.read_u32(4)?;
            match (
                get_expr_result(expr_results, fn_idx, reader.exprs.len()),
                get_expr_result(expr_results, arg_idx, reader.exprs.len()),
            ) {
                (Ok(func), Ok(arg)) => Ok(Expr::app(func, arg)),
                (Err(err), _) | (_, Err(err)) => Err(err),
            }
        }
        clean_kernel::flat::FlatTag::Lam => {
            let binder_info = decode_binder_info(flat.data[0])?;
            let ty_idx = flat.read_u32(1)?;
            let body_idx = flat.read_u32(5)?;
            match (
                get_expr_result(expr_results, ty_idx, reader.exprs.len()),
                get_expr_result(expr_results, body_idx, reader.exprs.len()),
            ) {
                (Ok(ty), Ok(body)) => Ok(Expr::lam(binder_info, ty, body)),
                (Err(err), _) | (_, Err(err)) => Err(err),
            }
        }
        clean_kernel::flat::FlatTag::Pi => {
            let binder_info = decode_binder_info(flat.data[0])?;
            let ty_idx = flat.read_u32(1)?;
            let body_idx = flat.read_u32(5)?;
            match (
                get_expr_result(expr_results, ty_idx, reader.exprs.len()),
                get_expr_result(expr_results, body_idx, reader.exprs.len()),
            ) {
                (Ok(ty), Ok(body)) => Ok(Expr::pi(binder_info, ty, body)),
                (Err(err), _) | (_, Err(err)) => Err(err),
            }
        }
        clean_kernel::flat::FlatTag::Let => {
            let ty_idx = flat.read_u32(0)?;
            let val_idx = flat.read_u32(4)?;
            let body_idx = flat.read_u32(8)?;
            match (
                get_expr_result(expr_results, ty_idx, reader.exprs.len()),
                get_expr_result(expr_results, val_idx, reader.exprs.len()),
                get_expr_result(expr_results, body_idx, reader.exprs.len()),
            ) {
                (Ok(ty), Ok(val), Ok(body)) => {
                    Ok(Expr::let_named(Name::anon(), ty, val, body, false))
                }
                (Err(err), _, _) | (_, Err(err), _) | (_, _, Err(err)) => Err(err),
            }
        }
        clean_kernel::flat::FlatTag::LitNat => {
            let value = flat.read_u64(0)?;
            Ok(Expr::nat_lit(value))
        }
        clean_kernel::flat::FlatTag::LitStr => {
            let str_idx = flat.read_u32(0)?;
            read_string(reader, str_idx).map(Expr::str_lit)
        }
        clean_kernel::flat::FlatTag::Proj => {
            let name_idx = flat.read_u32(0)?;
            let field = flat.read_u16(4)?;
            let expr_idx = flat.read_u32(6)?;
            let name = Name::from_string(read_string(reader, name_idx)?);
            get_expr_result(expr_results, expr_idx, reader.exprs.len())
                .map(|inner| Expr::proj(name, u32::from(field), inner))
        }
        clean_kernel::flat::FlatTag::FVar => {
            let id = flat.read_u64(0)?;
            Ok(Expr::fvar(FVarId::new(id)))
        }
    }
}

fn decode_binder_info(raw: u8) -> Result<BinderInfo, ShardReconstructError> {
    match raw {
        0 => Ok(BinderInfo::Default),
        1 => Ok(BinderInfo::Implicit),
        2 => Ok(BinderInfo::StrictImplicit),
        3 => Ok(BinderInfo::InstImplicit),
        other => Err(ShardReconstructError::InvalidBinderInfo(other)),
    }
}

fn read_string(reader: &ShardReader, idx: u32) -> Result<&str, ShardReconstructError> {
    reader.strings.get(idx as usize).map(String::as_str).ok_or(
        ShardReconstructError::StringOutOfRange {
            idx,
            count: reader.strings.len(),
        },
    )
}

fn get_level_result(
    built: &[LevelBuild],
    idx: u32,
    total_count: usize,
) -> Result<Level, ShardReconstructError> {
    let idx_usize = idx as usize;
    if idx_usize >= total_count {
        return Err(ShardReconstructError::LevelOutOfRange {
            idx,
            count: total_count,
        });
    }
    if idx_usize >= built.len() {
        return Err(ShardReconstructError::ForwardLevelRef {
            idx,
            current: built.len(),
        });
    }
    built[idx_usize].clone()
}

fn get_level_value(built: &[LevelBuild], idx: u32) -> Result<Level, ShardReconstructError> {
    built
        .get(idx as usize)
        .cloned()
        .ok_or(ShardReconstructError::LevelOutOfRange {
            idx,
            count: built.len(),
        })?
}

fn get_expr_result(
    built: &[ExprBuild],
    idx: u32,
    total_count: usize,
) -> Result<Expr, ShardReconstructError> {
    let idx_usize = idx as usize;
    if idx_usize >= total_count {
        return Err(ShardReconstructError::ExprOutOfRange {
            idx,
            count: total_count,
        });
    }
    if idx_usize >= built.len() {
        return Err(ShardReconstructError::ForwardExprRef {
            idx,
            current: built.len(),
        });
    }
    built[idx_usize].clone()
}

fn read_level_u32(flat: &FlatLevel, offset: usize) -> u32 {
    u32::from_le_bytes([
        flat.data[offset],
        flat.data[offset + 1],
        flat.data[offset + 2],
        flat.data[offset + 3],
    ])
}

/// Reconstruct a `Vec<Level>` from the shard's `level_lists` table at a given
/// offset. Returns an empty vec for the `u32::MAX` sentinel or when the shard
/// has no level_lists table (v1 format).
fn resolve_level_list(
    reader: &ShardReader,
    level_results: &[LevelBuild],
    levels_list_idx: u32,
) -> Result<Vec<Level>, ShardReconstructError> {
    if levels_list_idx == u32::MAX || reader.level_lists.is_empty() {
        return Ok(Vec::new());
    }
    let offset = levels_list_idx as usize;
    if offset >= reader.level_lists.len() {
        return Ok(Vec::new());
    }
    let count = reader.level_lists[offset] as usize;
    let start = offset + 1;
    if start + count > reader.level_lists.len() {
        return Ok(Vec::new());
    }
    let mut result = Vec::with_capacity(count);
    for k in 0..count {
        let level_idx = reader.level_lists[start + k];
        result.push(get_level_value(level_results, level_idx)?);
    }
    Ok(result)
}

fn constant_name(reader: &ShardReader, name_idx: u32) -> String {
    match reader.strings.get(name_idx as usize) {
        Some(name) => name.clone(),
        None => format!("<invalid-name-idx:{name_idx}>"),
    }
}

fn push_failure(result: &mut ShardVerifyResult, name: String, error: String) {
    result.failed += 1;
    result.failures.push((name, error));
}

fn saturating_usize_to_u32(value: usize) -> u32 {
    u32::try_from(value).unwrap_or(u32::MAX)
}

#[cfg(test)]
mod tests;
