// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Direct constant conversion from load-ready representation (#2428).
//!
//! Converts `LoadConstant` entries to kernel types using `read_and_convert_expr`
//! instead of the two-phase `ParsedExpr` -> `convert_expr` pipeline.

use super::convert::{
    elides_value, infer_recursor_arg_order, proof_value_or_placeholder, ConvertedConstant,
};
use super::convert_expr::convert_level_params;
use super::convert_expr_direct::read_and_convert_expr;
use super::load_parse::LoadConstant;
use super::{ExprInternCache, ExprSharingStats, ImportError};
use crate::module::{ConstantKind, ReducibilityHintsData};
use crate::region::CompactedRegion;
use clean_kernel::env::{Declaration, ProofValueElision};
use clean_kernel::expr::Expr;
use clean_kernel::inductive::{ConstructorVal, InductiveVal, RecursorRule, RecursorVal};
use clean_kernel::name::Name;

/// Convert a load-ready constant directly from binary, bypassing ParsedExpr.
pub(super) fn convert_load_constant(
    constant: &LoadConstant,
    region: &CompactedRegion<'_>,
    intern: &mut ExprInternCache,
    elide: ProofValueElision,
) -> ConvertedConstant {
    let name = constant.name.clone();
    match constant.kind {
        ConstantKind::Inductive => {
            let (result, stats) = convert_load_inductive(constant, region, intern);
            ConvertedConstant::Inductive(name, result, stats)
        }
        ConstantKind::Constructor => {
            let (result, stats) = convert_load_constructor(constant, region, intern);
            ConvertedConstant::Constructor(name, result, stats)
        }
        ConstantKind::Recursor => {
            let (result, stats) = convert_load_recursor(constant, region, intern);
            ConvertedConstant::Recursor(name, result, stats)
        }
        _ => {
            let hints = constant.hints;
            let (result, stats) = convert_load_other(constant, region, intern, elide);
            ConvertedConstant::Other(name, result.map(|d| (d, hints)), stats)
        }
    }
}

/// Convert type expression from raw pointer via the direct converter.
fn convert_type_expr(
    constant: &LoadConstant,
    region: &CompactedRegion<'_>,
    intern: &mut ExprInternCache,
    stats: &mut ExprSharingStats,
) -> Result<Expr, ImportError> {
    if constant.type_ptr == 0 {
        return Err(ImportError::MissingType(constant.name.clone()));
    }
    let (expr, s) = read_and_convert_expr(region, constant.type_ptr, &constant.name, intern)?;
    stats.merge(&s);
    Ok(expr)
}

/// Convert value expression from raw pointer via the direct converter.
fn convert_value_expr(
    constant: &LoadConstant,
    region: &CompactedRegion<'_>,
    intern: &mut ExprInternCache,
    stats: &mut ExprSharingStats,
) -> Result<Option<Expr>, ImportError> {
    if constant.value_ptr == 0 {
        return Ok(None);
    }
    let (expr, s) = read_and_convert_expr(region, constant.value_ptr, &constant.name, intern)?;
    stats.merge(&s);
    Ok(Some(expr))
}

fn convert_load_inductive(
    constant: &LoadConstant,
    region: &CompactedRegion<'_>,
    intern: &mut ExprInternCache,
) -> (Result<InductiveVal, ImportError>, ExprSharingStats) {
    let mut stats = ExprSharingStats::default();
    let result = (|| {
        let type_ = convert_type_expr(constant, region, intern, &mut stats)?;
        let level_params: Vec<Name> = constant
            .level_params
            .iter()
            .map(|s| Name::interned(s))
            .collect();
        let name = Name::interned(&constant.name);
        let ind_data = constant.inductive_val.as_ref();

        Ok(InductiveVal {
            name: name.clone(),
            level_params,
            type_,
            num_params: ind_data.map_or(0, |d| d.num_params),
            num_indices: ind_data.map_or(0, |d| d.num_indices),
            all_names: ind_data.map_or_else(
                || vec![name.clone()],
                |d| d.all.iter().map(|s| Name::interned(s)).collect(),
            ),
            constructor_names: ind_data
                .map(|d| d.ctors.iter().map(|s| Name::interned(s)).collect())
                .unwrap_or_default(),
            is_recursive: ind_data.is_some_and(|d| d.is_rec),
            is_reflexive: ind_data.is_some_and(|d| d.is_reflexive),
            is_large_elim: true, // placeholder, recomputed in fixup pass
            is_nested: ind_data.is_some_and(|d| d.is_nested),
        })
    })();
    (result, stats)
}

fn convert_load_constructor(
    constant: &LoadConstant,
    region: &CompactedRegion<'_>,
    intern: &mut ExprInternCache,
) -> (Result<ConstructorVal, ImportError>, ExprSharingStats) {
    let mut stats = ExprSharingStats::default();
    let result = (|| {
        let type_ = convert_type_expr(constant, region, intern, &mut stats)?;
        let level_params: Vec<Name> = constant
            .level_params
            .iter()
            .map(|s| Name::interned(s))
            .collect();
        let name = Name::interned(&constant.name);
        let ctor_data = constant.constructor_val.as_ref();

        Ok(ConstructorVal {
            name: name.clone(),
            inductive_name: ctor_data.map_or_else(
                || {
                    Name::interned(
                        constant
                            .name
                            .rsplit_once('.')
                            .map_or(constant.name.as_str(), |(p, _)| p),
                    )
                },
                |d| Name::interned(&d.induct),
            ),
            level_params,
            type_,
            num_params: ctor_data.map_or(0, |d| d.num_params),
            num_fields: ctor_data.map_or(0, |d| d.num_fields),
            constructor_idx: ctor_data.map_or(0, |d| d.cidx),
        })
    })();
    (result, stats)
}

fn convert_load_recursor(
    constant: &LoadConstant,
    region: &CompactedRegion<'_>,
    intern: &mut ExprInternCache,
) -> (
    Result<(RecursorVal, Vec<Name>, u32), ImportError>,
    ExprSharingStats,
) {
    let mut stats = ExprSharingStats::default();
    let result = (|| {
        let type_ = convert_type_expr(constant, region, intern, &mut stats)?;
        let level_params: Vec<Name> = constant
            .level_params
            .iter()
            .map(|s| Name::interned(s))
            .collect();
        let name = Name::interned(&constant.name);

        let inductive_name = Name::interned(
            constant
                .name
                .strip_suffix(".rec")
                .or_else(|| constant.name.strip_suffix(".recOn"))
                .or_else(|| constant.name.strip_suffix(".casesOn"))
                .or_else(|| constant.name.strip_suffix(".brecOn"))
                .unwrap_or(&constant.name),
        );

        let rec_data = constant.recursor_val.as_ref();

        let mutual_inductives: Vec<Name> = rec_data.map_or_else(
            || vec![inductive_name.clone()],
            |d| d.all.iter().map(|s| Name::interned(s)).collect(),
        );

        let param_count = rec_data.map_or(0, |d| d.num_params);

        // Convert rules with direct expression reading
        let rules: Vec<RecursorRule> = rec_data
            .map(|d| {
                d.rules
                    .iter()
                    .map(|r| {
                        let rhs = if r.rhs_ptr != 0 {
                            let (rhs, s) =
                                read_and_convert_expr(region, r.rhs_ptr, &constant.name, intern)?;
                            stats.merge(&s);
                            rhs
                        } else {
                            return Err(ImportError::ExprConversion {
                                name: constant.name.clone(),
                                message: format!(
                                    "recursor rule for {} has no RHS expression",
                                    r.ctor
                                ),
                            });
                        };

                        Ok(RecursorRule {
                            constructor_name: Name::interned(&r.ctor),
                            num_fields: r.num_fields,
                            recursive_fields: vec![], // Placeholder, filled in later
                            rhs,
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()
            })
            .transpose()?
            .unwrap_or_default();

        let arg_order = infer_recursor_arg_order(&constant.name);

        let rec_val = RecursorVal {
            name: name.clone(),
            arg_order,
            level_params,
            type_,
            inductive_name,
            num_params: param_count,
            num_indices: rec_data.map_or(0, |d| d.num_indices),
            num_motives: rec_data.map_or(1, |d| d.num_motives),
            num_minors: rec_data.map_or(0, |d| d.num_minors),
            rules,
            is_k: rec_data.is_some_and(|d| d.k),
        };

        Ok((rec_val, mutual_inductives, param_count))
    })();
    (result, stats)
}

fn convert_load_other(
    constant: &LoadConstant,
    region: &CompactedRegion<'_>,
    intern: &mut ExprInternCache,
    elide: ProofValueElision,
) -> (Result<Declaration, ImportError>, ExprSharingStats) {
    let mut stats = ExprSharingStats::default();
    let result = (|| {
        let type_ = convert_type_expr(constant, region, intern, &mut stats)?;
        // Conversion-time proof-value elision (#6 memory lever): for elided proof
        // kinds that actually HAVE a value (value_ptr != 0), skip building/interning
        // the value DAG (removing the peak); the placeholder + post-hoc null yield
        // value=None for exactly those kinds. Gating on value_ptr != 0 keeps the
        // registered-constant set identical to the post-hoc baseline (value-less
        // proofs still hit MissingValue). Shared helpers/predicate with super::convert.
        let should_elide = constant.value_ptr != 0 && elides_value(elide, &constant.kind);
        let value = if should_elide {
            None
        } else {
            convert_value_expr(constant, region, intern, &mut stats)?
        };
        let level_params = convert_level_params(&constant.level_params);
        let name = Name::interned(&constant.name);

        match constant.kind {
            ConstantKind::Axiom | ConstantKind::Quot => Ok(Declaration::Axiom {
                name,
                level_params,
                type_,
            }),
            ConstantKind::Definition => {
                let value =
                    value.ok_or_else(|| ImportError::MissingValue(constant.name.clone()))?;
                let is_reducible = matches!(constant.hints, Some(ReducibilityHintsData::Abbrev));
                Ok(Declaration::Definition {
                    name,
                    level_params,
                    type_,
                    value,
                    is_reducible,
                })
            }
            ConstantKind::Theorem => {
                let value = proof_value_or_placeholder(value, should_elide, &constant.name)?;
                Ok(Declaration::Theorem {
                    name,
                    level_params,
                    type_,
                    value,
                })
            }
            ConstantKind::Opaque => {
                let value = proof_value_or_placeholder(value, should_elide, &constant.name)?;
                Ok(Declaration::Opaque {
                    name,
                    level_params,
                    type_,
                    value,
                })
            }
            ConstantKind::Inductive | ConstantKind::Constructor | ConstantKind::Recursor => {
                Ok(Declaration::Axiom {
                    name,
                    level_params,
                    type_,
                })
            }
        }
    })();
    (result, stats)
}
