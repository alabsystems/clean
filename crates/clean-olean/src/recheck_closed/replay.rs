// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The two admission paths of the dependency-closed replay: an ordinary
//! constant through `add_decl`, an inductive family through
//! `add_inductive_core` with its recursors regenerated and the imported ones
//! only compared.

use clean_kernel::env::{ConstantInfo, ConstantKind, Declaration, Environment};
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType, RecursorRule};
use clean_kernel::name::Name;
use clean_kernel::tc::TypeChecker;
use std::collections::BTreeMap;

use super::drive::ReplayTarget;
use super::{ClosedRecheckRefusal, FamilyIndex, ReplayStats, Unit};

/// Re-admit one ordinary constant through `add_decl`.
pub(super) fn replay_constant(
    env: &Environment,
    replay: &mut dyn ReplayTarget,
    name: &Name,
    stats: &mut ReplayStats,
    refusals: &mut Vec<ClosedRecheckRefusal>,
) {
    let Some(info) = env.get_const(name) else {
        refusals.push(ClosedRecheckRefusal::AbsentFromEnvironment {
            name: name.to_string(),
        });
        return;
    };
    if env.is_unsafe(name) {
        refusals.push(ClosedRecheckRefusal::OutsideTrustedFragment {
            name: name.to_string(),
            marker: "unsafe",
        });
        return;
    }
    if env.is_partial(name) {
        refusals.push(ClosedRecheckRefusal::OutsideTrustedFragment {
            name: name.to_string(),
            marker: "partial",
        });
        return;
    }
    // A name the kernel already regenerated as part of an inductive family
    // certificate is never overwritten by the imported copy: compare instead.
    if replay.env().get_const(name).is_some() {
        compare_member(replay.env(), info, name, stats, refusals);
        // `Quot.sound` is installed by the kernel (`init_quot`), not admitted
        // through `add_decl`, but it is an AXIOM all the same — Lean's
        // `#print axioms` lists it. A cone that reaches it rests on it, so the
        // report must say so; the other quotient primitives are type
        // formers and eliminators with computation rules, not assumptions.
        if replay
            .env()
            .get_quot(name)
            .is_some_and(|q| q.kind == clean_kernel::quot::QuotKind::Sound)
        {
            stats.axioms_admitted.insert(name.clone());
        }
        return;
    }
    let Some(decl) = declaration_from_info(info) else {
        refusals.push(ClosedRecheckRefusal::DeclarationRefused {
            name: name.to_string(),
            error: "declaration has no value and is not a kernel-generated family member \
                    (nothing to re-derive)"
                .to_string(),
        });
        return;
    };
    match replay.admit_decl(decl) {
        Ok(()) => {
            stats.constants_admitted += 1;
            stats.admitted_names.insert(name.clone());
            if info.kind == ConstantKind::Axiom {
                stats.axioms_admitted.insert(name.clone());
            }
        }
        Err(error) => refusals.push(ClosedRecheckRefusal::DeclarationRefused {
            name: name.to_string(),
            error,
        }),
    }
}

/// Re-admit one inductive family block through `add_inductive_core`, then
/// compare every imported member against what the kernel regenerated.
///
/// With `clean_families`, a family whose recursor table carries `casesOn` /
/// `recOn` as RECURSORS — which only Clean's own `add_inductive` produces;
/// Lean carries them as ordinary definitions — is re-admitted through
/// `add_inductive` instead, so those recursors are regenerated and compared
/// like `rec` rather than reported as never regenerated. The generated
/// convenience definitions that come with it (`noConfusion`, `below`, …)
/// enter the replay environment as kernel output; a cone member of the same
/// name is then compared against them, never installed over them.
#[allow(clippy::too_many_arguments)]
pub(super) fn replay_family(
    env: &Environment,
    index: &FamilyIndex,
    replay: &mut dyn ReplayTarget,
    head: &Name,
    unit: &Unit,
    clean_families: bool,
    stats: &mut ReplayStats,
    refusals: &mut Vec<ClosedRecheckRefusal>,
) {
    let Some(head_val) = env.get_inductive(head) else {
        refusals.push(ClosedRecheckRefusal::FamilyIncomplete {
            family: head.to_string(),
            detail: "family head is not registered as an inductive".to_string(),
        });
        return;
    };
    let families: Vec<Name> = if head_val.all_names.is_empty() {
        vec![head_val.name.clone()]
    } else {
        head_val.all_names.clone()
    };

    let mut types = Vec::with_capacity(families.len());
    for family in &families {
        let Some(ind) = env.get_inductive(family) else {
            refusals.push(ClosedRecheckRefusal::FamilyIncomplete {
                family: head.to_string(),
                detail: format!("mutual member {family} is not registered as an inductive"),
            });
            return;
        };
        let mut constructors = Vec::with_capacity(ind.constructor_names.len());
        for ctor_name in &ind.constructor_names {
            let Some(ctor) = env.get_constructor(ctor_name) else {
                refusals.push(ClosedRecheckRefusal::FamilyIncomplete {
                    family: head.to_string(),
                    detail: format!("constructor {ctor_name} is not registered"),
                });
                return;
            };
            constructors.push(Constructor {
                name: ctor.name.clone(),
                type_: ctor.type_.clone(),
            });
        }
        types.push(InductiveType {
            name: ind.name.clone(),
            type_: ind.type_.clone(),
            constructors,
        });
    }

    let decl = InductiveDecl {
        level_params: head_val.level_params.clone(),
        num_params: head_val.num_params,
        types,
    };
    let clean_built = clean_families
        && unit.members.iter().any(|m| {
            env.get_recursor(m).is_some() && {
                let s = m.to_string();
                s.ends_with(".casesOn") || s.ends_with(".recOn")
            }
        });
    if let Err(error) = replay.admit_family(decl, clean_built) {
        refusals.push(ClosedRecheckRefusal::FamilyRefused {
            family: head.to_string(),
            error,
        });
        return;
    }
    let replay: &Environment = replay.env();
    stats.families_replayed += 1;
    for member in &unit.members {
        if replay.get_const(member).is_some() {
            stats.admitted_names.insert(member.clone());
        }
    }

    // Compare every imported member of the block against the regenerated one.
    for member in &unit.members {
        if let Some(rec) = env.get_recursor(member) {
            let Some(regenerated) = replay.get_recursor(member) else {
                refusals.push(ClosedRecheckRefusal::MemberNotRegenerated {
                    name: member.to_string(),
                    family: head.to_string(),
                });
                continue;
            };
            stats.family_members_compared += 1;
            let imported_type = rec.type_.clone();
            let imported_rules = rec.rules.clone();
            let imported_levels = rec.level_params.clone();
            let regenerated_type = regenerated.type_.clone();
            let regenerated_rules = regenerated.rules.clone();
            let regenerated_levels = regenerated.level_params.clone();
            if imported_levels != regenerated_levels {
                refusals.push(ClosedRecheckRefusal::MemberMismatch {
                    name: member.to_string(),
                    detail: format!(
                        "level params: imported {imported_levels:?}, \
                         regenerated {regenerated_levels:?}"
                    ),
                });
            }
            if !same_term(replay, &imported_type, &regenerated_type) {
                refusals.push(ClosedRecheckRefusal::MemberMismatch {
                    name: member.to_string(),
                    detail: "the imported recursor type is not definitionally equal to the one \
                             the kernel regenerates from the family"
                        .to_string(),
                });
            }
            compare_rules(
                replay,
                member,
                &imported_rules,
                &regenerated_rules,
                stats,
                refusals,
            );
            continue;
        }
        if env.get_inductive(member).is_some() || env.get_constructor(member).is_some() {
            let imported = env.get_const(member);
            let regenerated_present =
                replay.get_inductive(member).is_some() || replay.get_constructor(member).is_some();
            if !regenerated_present {
                refusals.push(ClosedRecheckRefusal::MemberNotRegenerated {
                    name: member.to_string(),
                    family: head.to_string(),
                });
                continue;
            }
            stats.family_members_compared += 1;
            if let Some(info) = imported {
                compare_member(replay, info, member, stats, refusals);
            }
        }
    }
    let _ = index;
}

/// Compare an imported family member's stored `ConstantInfo` against the
/// regenerated one already in the replay environment.
fn compare_member(
    replay: &Environment,
    imported: &ConstantInfo,
    name: &Name,
    stats: &mut ReplayStats,
    refusals: &mut Vec<ClosedRecheckRefusal>,
) {
    let Some(regenerated) = replay.get_const(name) else {
        return;
    };
    stats.family_members_compared += 1;
    if imported.level_params != regenerated.level_params {
        refusals.push(ClosedRecheckRefusal::MemberMismatch {
            name: name.to_string(),
            detail: format!(
                "level params: imported {:?}, regenerated {:?}",
                imported.level_params, regenerated.level_params
            ),
        });
        return;
    }
    let imported_type = imported.type_.clone();
    let regenerated_type = regenerated.type_.clone();
    if same_term(replay, &imported_type, &regenerated_type) {
        return;
    }
    refusals.push(ClosedRecheckRefusal::MemberMismatch {
        name: name.to_string(),
        detail: "imported type is not definitionally equal to the regenerated one".to_string(),
    });
}

/// Compare imported ι-rules against regenerated ones.
///
/// This is the comparison no weaker level performs. The replay environment
/// keeps the REGENERATED rules either way, so a mismatch is a finding about
/// the import, never a change to what the replay reduces with.
/// Syntactic equality first, then definitional equality in the replay
/// environment. Definitional equality is the semantic criterion — two ι-rules
/// that reduce to the same thing compute the same thing — so a mere spelling
/// difference between Lean's generated term and Clean's is not reported as a
/// finding, while a difference in what they COMPUTE is.
fn same_term(
    replay: &Environment,
    a: &clean_kernel::expr::Expr,
    b: &clean_kernel::expr::Expr,
) -> bool {
    if a == b {
        return true;
    }
    let tc = TypeChecker::new(replay);
    tc.is_def_eq(a, b)
}

fn compare_rules(
    replay: &Environment,
    recursor: &Name,
    imported: &[RecursorRule],
    regenerated: &[RecursorRule],
    stats: &mut ReplayStats,
    refusals: &mut Vec<ClosedRecheckRefusal>,
) {
    let by_ctor: BTreeMap<&Name, &RecursorRule> = regenerated
        .iter()
        .map(|r| (&r.constructor_name, r))
        .collect();
    for rule in imported {
        stats.recursor_rules_compared += 1;
        let Some(theirs) = by_ctor.get(&rule.constructor_name) else {
            refusals.push(ClosedRecheckRefusal::RecursorRuleMismatch {
                recursor: recursor.to_string(),
                constructor: rule.constructor_name.to_string(),
                detail: "the kernel regenerated no rule for this constructor".to_string(),
            });
            continue;
        };
        if rule.num_fields != theirs.num_fields {
            refusals.push(ClosedRecheckRefusal::RecursorRuleMismatch {
                recursor: recursor.to_string(),
                constructor: rule.constructor_name.to_string(),
                detail: format!(
                    "num_fields: imported {}, regenerated {}",
                    rule.num_fields, theirs.num_fields
                ),
            });
            continue;
        }
        if !same_term(replay, &rule.rhs, &theirs.rhs) {
            refusals.push(ClosedRecheckRefusal::RecursorRuleMismatch {
                recursor: recursor.to_string(),
                constructor: rule.constructor_name.to_string(),
                detail: "the imported ι-rule right-hand side differs from the one the kernel \
                         regenerates from the constructor"
                    .to_string(),
            });
        }
    }
    for rule in regenerated {
        if !imported
            .iter()
            .any(|r| r.constructor_name == rule.constructor_name)
        {
            refusals.push(ClosedRecheckRefusal::RecursorRuleMismatch {
                recursor: recursor.to_string(),
                constructor: rule.constructor_name.to_string(),
                detail: "the import carries no rule for a constructor the kernel regenerates"
                    .to_string(),
            });
        }
    }
}

fn declaration_from_info(info: &ConstantInfo) -> Option<Declaration> {
    match info.kind {
        ConstantKind::Definition => Some(Declaration::Definition {
            name: info.name.clone(),
            level_params: info.level_params.clone(),
            type_: info.type_.clone(),
            value: info.value.clone()?,
            is_reducible: info.is_reducible,
        }),
        ConstantKind::Theorem => Some(Declaration::Theorem {
            name: info.name.clone(),
            level_params: info.level_params.clone(),
            type_: info.type_.clone(),
            value: info.value.clone()?,
        }),
        ConstantKind::Opaque => Some(Declaration::Opaque {
            name: info.name.clone(),
            level_params: info.level_params.clone(),
            type_: info.type_.clone(),
            value: info.value.clone()?,
        }),
        ConstantKind::Axiom => Some(Declaration::Axiom {
            name: info.name.clone(),
            level_params: info.level_params.clone(),
            type_: info.type_.clone(),
        }),
    }
}
