// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Per-shard and per-constant verification logic.

use std::collections::HashMap;
use std::path::Path;
use std::time::Instant;

use clean_kernel::{Declaration, Environment, Name};

use super::{ShardResult, SystemStats, VerifyStats};
use crate::shard::ShardReader;
use crate::shard_reconstruct::{reconstruct_from_shard_with_level_lists, reconstruct_level_params};
use crate::types::NO_VALUE;

pub(super) struct ShardVerification {
    pub(super) stats: VerifyStats,
    pub(super) per_system: HashMap<u8, SystemStats>,
    pub(super) result: ShardResult,
}

enum ConstResult {
    KernelVerified,
    Translated,
    ReconstructFailed,
    TypeCheckFailed,
}

pub(super) fn verify_shard_file(path: &Path) -> ShardVerification {
    let start = Instant::now();

    let reader = match ShardReader::from_file(path) {
        Ok(reader) => reader,
        Err(error) => {
            return ShardVerification {
                stats: VerifyStats {
                    shards_skipped: 1,
                    ..VerifyStats::default()
                },
                per_system: HashMap::new(),
                result: ShardResult {
                    path: path.to_path_buf(),
                    num_constants: 0,
                    verified: 0,
                    translated: 0,
                    failed: 0,
                    elapsed_secs: start.elapsed().as_secs_f64(),
                    error: Some(error.to_string()),
                },
            };
        }
    };

    let shard_name = path
        .file_name()
        .unwrap_or_default()
        .to_string_lossy()
        .into_owned();

    let mut stats = VerifyStats::default();
    let mut per_system = HashMap::new();

    let (verified, translated, failed) =
        verify_shard_constants(&reader, &shard_name, &mut stats, &mut per_system);

    stats.shards_processed = 1;

    ShardVerification {
        stats,
        per_system,
        result: ShardResult {
            path: path.to_path_buf(),
            num_constants: reader.constants.len(),
            verified,
            translated,
            failed,
            elapsed_secs: start.elapsed().as_secs_f64(),
            error: None,
        },
    }
}

/// Verify all constants in a single shard. Returns (verified, translated, failed).
fn verify_shard_constants(
    reader: &ShardReader,
    shard_name: &str,
    stats: &mut VerifyStats,
    per_system: &mut HashMap<u8, SystemStats>,
) -> (u64, u64, u64) {
    let mut shard_verified = 0u64;
    let mut shard_translated = 0u64;
    let mut shard_failed = 0u64;

    for (ci, constant) in reader.constants.iter().enumerate() {
        let name_str = reader
            .strings
            .get(constant.name_idx as usize)
            .map(|s| s.as_str())
            .unwrap_or("<unknown>");

        let sys = per_system
            .entry(constant.source_system)
            .or_insert_with(|| SystemStats {
                source_system: constant.source_system,
                total: 0,
                kernel_verified: 0,
                translated: 0,
                failed: 0,
            });
        sys.total += 1;
        stats.total_constants += 1;

        let result = verify_single_constant(reader, shard_name, ci, name_str, constant);
        match result {
            ConstResult::KernelVerified => {
                shard_verified += 1;
                sys.kernel_verified += 1;
                stats.kernel_verified += 1;
            }
            ConstResult::Translated => {
                shard_translated += 1;
                sys.translated += 1;
                stats.translated += 1;
            }
            ConstResult::ReconstructFailed => {
                shard_failed += 1;
                sys.failed += 1;
                stats.reconstruct_failed += 1;
            }
            ConstResult::TypeCheckFailed => {
                shard_failed += 1;
                sys.failed += 1;
                stats.type_check_failed += 1;
            }
        }
    }

    (shard_verified, shard_translated, shard_failed)
}

/// Verify a single constant: reconstruct type/value, try theorem then axiom.
fn verify_single_constant(
    reader: &ShardReader,
    shard_name: &str,
    ci: usize,
    name_str: &str,
    constant: &crate::types::MathverseConstantHeader,
) -> ConstResult {
    let type_expr = match reconstruct_from_shard_with_level_lists(
        &reader.exprs,
        &reader.levels,
        &reader.strings,
        &reader.level_lists,
        constant.type_idx,
    ) {
        Ok(e) => e,
        Err(_) => return ConstResult::ReconstructFailed,
    };

    let value_expr = if constant.value_idx != NO_VALUE {
        reconstruct_from_shard_with_level_lists(
            &reader.exprs,
            &reader.levels,
            &reader.strings,
            &reader.level_lists,
            constant.value_idx,
        )
        .ok()
    } else {
        None
    };

    // Reconstruct declaration-level universe parameter names.
    let level_params = reconstruct_level_params(
        &reader.strings,
        constant.level_params_start,
        constant.level_params_count,
    )
    .unwrap_or_default();

    let decl_name = Name::from_string(&format!("mathverse.{shard_name}.{ci}.{name_str}"));

    if let Some(ref value) = value_expr {
        let decl = Declaration::Theorem {
            name: decl_name.clone(),
            level_params: level_params.clone(),
            type_: type_expr.clone(),
            value: value.clone(),
        };
        let mut env = Environment::new();
        if env.add_decl(decl).is_ok() {
            return ConstResult::KernelVerified;
        }
    }

    let axiom_name = Name::from_string(&format!("mathverse.{shard_name}.{ci}.{name_str}.axiom"));
    let axiom_decl = Declaration::Axiom {
        name: axiom_name,
        level_params,
        type_: type_expr,
    };
    let mut env = Environment::new();
    if env.add_decl(axiom_decl).is_ok() {
        ConstResult::Translated
    } else {
        ConstResult::TypeCheckFailed
    }
}
