// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A cone's units as export declarations, read off the kernel's own records.
//!
//! The source is an [`Environment`]: the kernel's `ConstantInfo`,
//! `InductiveVal`, `ConstructorVal`, `RecursorVal` and `QuotVal`, nothing
//! parsed from a file. What Lean's records state and the kernel does not hold
//! is derived or refused, never guessed:
//!
//! - `hints`: the kernel keeps an unfolding priority (`Reducibility`), not
//!   Lean's hint. `Reducible` is written `abbrev`, `Regular(h)` as
//!   `{"regular": h}`, and `Opaque` or `Irreducible` as `opaque`. Lean's kernel
//!   reads a hint only to choose which side of a definitional-equality
//!   problem to unfold first (`lazy_delta_reduction_step`); whether a
//!   definition unfolds is decided by its having a value. A hint the `.olean`
//!   loader adjusted (an attribute, a projection function) is therefore
//!   written as the kernel holds it, not as Lean stored it.
//! - `numNested`: the number of the block's auxiliary recursors
//!   (`<first type>.rec_<i>`), which is how Lean numbers them; it must agree
//!   with the kernel's `is_nested`.
//! - a block's recursors: `<type>.rec` for each type in the block's order,
//!   then `<first type>.rec_1 ..`. Any other recursor (the `casesOn`/`recOn`
//!   of a Clean-built family) has no record in Lean's format and is refused.
//! - `unsafe` and `partial` declarations are refused: the writer exports the
//!   fragment Lean's replay checks.

use clean_kernel::env::{ConstantKind, Environment, Reducibility};
use clean_kernel::name::Name;
use clean_kernel::quot::QuotKind;

use super::error::ExportWriteError;
use crate::module::{DefinitionSafety, ParsedQuotKind, ReducibilityHintsData};
use crate::ndjson::decl::{
    ExportConstructor, ExportDeclaration, ExportHeader, ExportInductiveBlock, ExportInductiveType,
    ExportRecursor, ExportRecursorRule,
};
use crate::recheck_closed::PlannedUnit;

fn safe(env: &Environment, name: &Name) -> Result<(), ExportWriteError> {
    let marker = if env.is_unsafe(name) {
        "unsafe"
    } else if env.is_partial(name) {
        "partial"
    } else {
        return Ok(());
    };
    Err(ExportWriteError::OutsideSafeFragment {
        name: name.to_unambiguous_string(),
        marker,
    })
}

fn shape(block: &Name, problem: String) -> ExportWriteError {
    ExportWriteError::BlockShape {
        block: block.to_unambiguous_string(),
        problem,
    }
}

/// The declaration `unit` is, as the export states it.
pub(super) fn unit_declaration(
    env: &Environment,
    unit: &PlannedUnit,
) -> Result<ExportDeclaration, ExportWriteError> {
    match unit {
        PlannedUnit::Constant(name) => constant(env, name),
        PlannedUnit::Family { head, members } => {
            family(env, head, members).map(ExportDeclaration::Inductive)
        }
    }
}

fn constant(env: &Environment, name: &Name) -> Result<ExportDeclaration, ExportWriteError> {
    safe(env, name)?;
    if let Some(quot) = env.get_quot(name) {
        let header = ExportHeader {
            name: name.clone(),
            level_params: quot.level_params.clone(),
            type_: quot.type_.clone(),
        };
        let kind = match quot.kind {
            QuotKind::Type => ParsedQuotKind::Type,
            QuotKind::Mk => ParsedQuotKind::Mk,
            QuotKind::Lift => ParsedQuotKind::Lift,
            QuotKind::Ind => ParsedQuotKind::Ind,
            // Lean declares `Quot.sound` as an axiom of `Init.Core`.
            QuotKind::Sound => {
                return Ok(ExportDeclaration::Axiom {
                    header,
                    is_unsafe: false,
                })
            }
        };
        return Ok(ExportDeclaration::Quot { header, kind });
    }
    let Some(info) = env.get_const(name) else {
        return Err(ExportWriteError::AbsentConstant {
            name: name.to_unambiguous_string(),
        });
    };
    let header = ExportHeader {
        name: name.clone(),
        level_params: info.level_params.clone(),
        type_: info.type_.clone(),
    };
    let value = |kind: &'static str| {
        info.value
            .clone()
            .ok_or_else(|| ExportWriteError::MissingValue {
                name: name.to_unambiguous_string(),
                kind,
            })
    };
    Ok(match info.kind {
        ConstantKind::Axiom => ExportDeclaration::Axiom {
            header,
            is_unsafe: false,
        },
        ConstantKind::Definition => ExportDeclaration::Definition {
            header,
            value: value("def")?,
            hints: match info.reducibility {
                Reducibility::Reducible => ReducibilityHintsData::Abbrev,
                Reducibility::Regular(height) => ReducibilityHintsData::Regular(height),
                Reducibility::Opaque | Reducibility::Irreducible => ReducibilityHintsData::Opaque,
            },
            safety: DefinitionSafety::Safe,
        },
        ConstantKind::Theorem => ExportDeclaration::Theorem {
            header,
            value: value("thm")?,
        },
        ConstantKind::Opaque => ExportDeclaration::Opaque {
            header,
            value: value("opaque")?,
            is_unsafe: false,
        },
    })
}

/// The auxiliary recursor index of `name`, if it is `<first>.rec_<i>`.
fn aux_index(first: &Name, name: &Name, limit: usize) -> Option<usize> {
    (1..=limit).find(|i| *name == first.clone().str(format!("rec_{i}")))
}

fn family(
    env: &Environment,
    head: &Name,
    members: &[Name],
) -> Result<ExportInductiveBlock, ExportWriteError> {
    let Some(head_val) = env.get_inductive(head) else {
        return Err(shape(head, "its head is not an inductive type".to_owned()));
    };
    let all: Vec<Name> = if head_val.all_names.is_empty() {
        vec![head_val.name.clone()]
    } else {
        head_val.all_names.clone()
    };
    let first = &all[0];
    let mut block = ExportInductiveBlock::default();
    for type_name in &all {
        safe(env, type_name)?;
        let Some(ind) = env.get_inductive(type_name) else {
            return Err(shape(
                first,
                format!(
                    "its member {} is not an inductive type",
                    type_name.to_unambiguous_string()
                ),
            ));
        };
        if !ind.all_names.is_empty() && ind.all_names != all {
            return Err(shape(
                first,
                format!(
                    "its member {} names a different block",
                    type_name.to_unambiguous_string()
                ),
            ));
        }
        block.types.push(ExportInductiveType {
            header: ExportHeader {
                name: ind.name.clone(),
                level_params: ind.level_params.clone(),
                type_: ind.type_.clone(),
            },
            num_params: ind.num_params,
            num_indices: ind.num_indices,
            all: all.clone(),
            ctors: ind.constructor_names.clone(),
            num_nested: 0,
            is_rec: ind.is_recursive,
            is_unsafe: false,
            is_reflexive: ind.is_reflexive,
        });
        for ctor_name in &ind.constructor_names {
            safe(env, ctor_name)?;
            let Some(ctor) = env.get_constructor(ctor_name) else {
                return Err(shape(
                    first,
                    format!(
                        "its constructor {} is not in the environment",
                        ctor_name.to_unambiguous_string()
                    ),
                ));
            };
            block.ctors.push(ExportConstructor {
                header: ExportHeader {
                    name: ctor.name.clone(),
                    level_params: ctor.level_params.clone(),
                    type_: ctor.type_.clone(),
                },
                induct: ctor.inductive_name.clone(),
                cidx: ctor.constructor_idx,
                num_params: ctor.num_params,
                num_fields: ctor.num_fields,
                is_unsafe: false,
            });
        }
    }

    // The recursors, in Lean's order: `<type>.rec` per type, then the
    // auxiliary ones of a nested block by their number.
    let recursors: Vec<&Name> = members
        .iter()
        .filter(|member| env.get_recursor(member).is_some())
        .collect();
    let mut ordered: Vec<Option<&Name>> = vec![None; recursors.len()];
    for name in &recursors {
        let slot = all
            .iter()
            .position(|t| **name == t.clone().str("rec"))
            .or_else(|| aux_index(first, name, recursors.len()).map(|i| all.len() + i - 1))
            .filter(|slot| *slot < ordered.len() && ordered[*slot].is_none());
        let Some(slot) = slot else {
            return Err(shape(
                first,
                format!(
                    "it carries the recursor {}, which is neither `<type>.rec` nor the next \
                     `<first type>.rec_<n>`: Lean's `inductive` record has no place for it",
                    name.to_unambiguous_string()
                ),
            ));
        };
        ordered[slot] = Some(name);
    }
    if recursors.len() < all.len() {
        return Err(shape(
            first,
            format!(
                "it has {} type(s) and {} recursor(s) in the environment",
                all.len(),
                recursors.len()
            ),
        ));
    }
    let nested = recursors.len() - all.len();
    if head_val.is_nested != (nested > 0) {
        return Err(shape(
            first,
            format!(
                "the kernel records is_nested = {} and the environment holds {nested} auxiliary \
                 recursor(s)",
                head_val.is_nested
            ),
        ));
    }
    let nested = u32::try_from(nested)
        .map_err(|_| shape(first, "too many auxiliary recursors".to_owned()))?;
    for t in &mut block.types {
        t.num_nested = nested;
    }
    for name in ordered.into_iter().flatten() {
        safe(env, name)?;
        let Some(rec) = env.get_recursor(name) else {
            continue;
        };
        block.recs.push(ExportRecursor {
            header: ExportHeader {
                name: rec.name.clone(),
                level_params: rec.level_params.clone(),
                type_: rec.type_.clone(),
            },
            all: all.clone(),
            num_params: rec.num_params,
            num_indices: rec.num_indices,
            num_motives: rec.num_motives,
            num_minors: rec.num_minors,
            rules: rec
                .rules
                .iter()
                .map(|rule| ExportRecursorRule {
                    ctor: rule.constructor_name.clone(),
                    nfields: rule.num_fields,
                    rhs: rule.rhs.clone(),
                })
                .collect(),
            k: rec.is_k,
            is_unsafe: false,
        });
    }
    Ok(block)
}
