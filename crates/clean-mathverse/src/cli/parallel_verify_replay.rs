// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! PARAGON's per-module verdicts in Lean's replay order.
//!
//! The shared base holds every target module's OWN declarations (types, and
//! definition values), so `check_decl_readonly` alone let a value lean on
//! itself: measured 2026-09-23, `stamp-verified --parallel` stored
//! `KernelVerified` for `forged3_self : False := forged3_self` and for the
//! two-cycle `forged3_cycA/B`, which `leanchecker` rejects with `(kernel)
//! unknown constant`. Here a module's constants are scheduled the way
//! `Lean.Environment.Replay.replayConstant` (`src/lean/Lean/Replay.lean`) adds
//! them — every module-local dependency first, an inductive block as one unit,
//! unsafe and partial declarations never — through
//! [`clean_olean::replay_order`], and a constant earns `KernelVerified` only
//! when its own check passed AND every module-local constant it uses was
//! admitted first. A value that mentions itself or sits on a cycle is refused
//! before the kernel runs. Imports (the dependency closure) stay the trusted
//! starting environment, as in Lean's `replayFromImports`; the base carries
//! [`clean_kernel::env::KernelTheory::Lean`], so every check runs in Lean's
//! reducer theory and Lean's safe context.

use std::collections::{BTreeMap, BTreeSet};

use clean_kernel::env::Declaration;
use clean_kernel::{EnvError, Environment, KernelTypeError, Name};
use clean_olean::replay_families::inductive_block_refusals;
use clean_olean::replay_order::{
    expr_refs, resident_refs, ReplayGraph, ReplayRefusal, ReplayVerdicts,
};
use clean_olean::DefinitionSafety;

use super::{purge_freed_arena, ModuleVerdicts};
use crate::inductive_replay::reconstruct_constant;
use crate::shard::ShardReader;
use crate::types::DeclKind;

/// Declarations of each loaded module (by module name) that the loader
/// dropped because a constant of the same name was already resident and is not
/// that module's own (`clean_olean::LoadSummary::shadowed_declarations`), each
/// with who holds the name. The per-module replay refuses them as already
/// declared ([`verify_module_constants`]).
pub(super) type ShadowedByModule = std::collections::HashMap<String, BTreeMap<Name, String>>;

/// Every kernel name each loaded module's parts (its `.olean`, `.olean.server`
/// and `.olean.private`) declared, by module name — the companions' names
/// folded onto the base module, as [`record_shadowed`] keys them. A module's
/// shard rows come from its `.olean` plus its `.olean.private` root only
/// (`parse_target_module_with_proofs`), so a name a part declared that is not a
/// row — a `.olean.server`-only family, or a `.olean.private` family the bridge
/// could not merge — is resident in the base but never replayed; without this
/// the replay trusts it as an import (finding B1). The `.olean` loader's
/// [`clean_olean::ImportError::MisplacedDeclaration`] refuses the server-only
/// case outright (R113); this is the per-module defence behind it.
pub(super) type ModuleDeclaredNames = std::collections::HashMap<String, BTreeSet<Name>>;

pub(super) fn record_declared(
    declared: &mut ModuleDeclaredNames,
    summary: &clean_olean::LoadSummary,
) {
    if summary.added_names.is_empty() {
        return;
    }
    let module = summary.module_name.clone().unwrap_or_default();
    let module = module
        .strip_suffix("._server")
        .or_else(|| module.strip_suffix("._private"))
        .unwrap_or(&module)
        .to_owned();
    declared
        .entry(module)
        .or_default()
        .extend(summary.added_names.iter().cloned());
}

pub(super) fn record_shadowed(shadowed: &mut ShadowedByModule, summary: &clean_olean::LoadSummary) {
    if summary.shadowed_declarations.is_empty() {
        return;
    }
    let module = summary.module_name.clone().unwrap_or_default();
    let module = module
        .strip_suffix("._server")
        .or_else(|| module.strip_suffix("._private"))
        .unwrap_or(&module)
        .to_owned();
    let slot = shadowed.entry(module).or_default();
    for (name, held_by) in &summary.shadowed_declarations {
        slot.entry(name.clone()).or_insert_with(|| held_by.clone());
    }
}

/// The first name two closure shards declare that Lean's import refuses:
/// `(name, served module, other module)`. PARAGON's demand-paged base serves
/// one declaration per name (first shard wins, which is not Lean's import
/// order) and its lazily served constants never pass the loader's dedup, so a
/// module's redeclaration of a name another module holds would be served or
/// stamped there. Lean's own exception is kept: a theorem or axiom restated
/// with the same universe parameters and type (`finalizeImport`'s
/// `subsumesInfo`). A copy that does not materialize counts as a collision.
pub(super) fn first_refused_collision(
    source: &crate::closure_source::ShardConstantSource,
) -> Option<(Name, String, String)> {
    use clean_kernel::ConstantKind;
    let load = |(shard, idx): (u32, u32)| {
        source
            .reader(shard as usize)
            .and_then(|reader| crate::closure_source::materialize_constant_from_reader(reader, idx))
    };
    let module = |shard: u32| {
        source
            .shard_module(shard as usize)
            .unwrap_or("?")
            .to_owned()
    };
    source
        .collisions()
        .iter()
        .find_map(|(name, served, other)| {
            let restated = match (load(*served), load(*other)) {
                (Some(a), Some(b)) => {
                    [a.kind, b.kind]
                        .iter()
                        .all(|k| matches!(k, ConstantKind::Theorem | ConstantKind::Axiom))
                        && a.level_params == b.level_params
                        && clean_kernel::env::lean_expr_eqv(&a.type_, &b.type_)
                }
                _ => false,
            };
            (!restated).then(|| (name.clone(), module(served.0), module(other.0)))
        })
}

/// What pass 1 learned about one value-bearing constant.
enum ValueRow {
    /// Ready for the kernel.
    Checkable(Declaration),
    /// The shard carries no value for this row (an elided opaque/meta value).
    NoValue,
    /// The flat arena could not be rebuilt.
    ReconstructFailed(String),
}

/// One named constant of the module.
struct Row {
    name: String,
    kind: DeclKind,
    value: Option<ValueRow>,
}

/// Re-check every constant of `reader` against `base` in replay order,
/// accumulating into `v` exactly the counters the unordered loop kept, plus
/// `failed` rows for the constants the replay refuses.
pub(super) fn verify_module_constants(
    reader: &ShardReader,
    base: &Environment,
    already_declared: Option<&BTreeMap<Name, String>>,
    module_declared: Option<&BTreeSet<Name>>,
    heartbeat_escalate: Option<u32>,
    v: &mut ModuleVerdicts,
) {
    let mut rows: BTreeMap<Name, Row> = BTreeMap::new();
    let mut graph = ReplayGraph::new();
    for constant in &reader.constants {
        v.total += 1;
        let Some(name) = reader.strings.get(constant.name_idx as usize) else {
            v.reconstruct_failed += 1;
            v.failures.push((
                "<unnamed>".to_string(),
                "constant name index out of bounds".to_string(),
            ));
            continue;
        };
        let kind = DeclKind::try_from(constant.decl_kind).unwrap_or(DeclKind::Theorem);
        let key = Name::from_string(name);
        if rows.contains_key(&key) {
            // Two rows under one name cannot both be the declaration Lean added.
            v.failed += 1;
            v.failures
                .push((name.clone(), "duplicate constant name in shard".to_string()));
            continue;
        }
        // The reconstructed value's references for a checkable row; every other
        // row takes its edges from the base, which holds the type (and every
        // inductive block) of each module constant — a row that fails in pass 1
        // still needs its edges, so that its dependents are refused rather
        // than scheduled ahead of it.
        let mut own_refs = None;
        let value = match kind {
            DeclKind::Theorem | DeclKind::Definition | DeclKind::Opaque => {
                Some(match reconstruct_constant(name, reader, constant) {
                    Err(msg) => ValueRow::ReconstructFailed(msg),
                    Ok(rc) => match rc.value_expr {
                        None => ValueRow::NoValue,
                        Some(value_expr) => {
                            own_refs = Some(expr_refs(&rc.type_expr, Some(&value_expr)));
                            ValueRow::Checkable(build_decl(
                                name,
                                kind,
                                rc.level_params,
                                rc.type_expr,
                                value_expr,
                            ))
                        }
                    },
                })
            }
            _ => None,
        };
        let refs = own_refs.unwrap_or_else(|| resident_refs(base, &key));
        graph.insert(key.clone(), refs);
        let safety = match constant.definition_safety() {
            Some(DefinitionSafety::Safe) | None if base.is_unsafe(&key) => Some("unsafe"),
            Some(DefinitionSafety::Safe) | None if base.is_partial(&key) => Some("partial"),
            Some(DefinitionSafety::Safe) | None => None,
            Some(DefinitionSafety::Partial) => Some("partial"),
            // `unsafe`, or a safety this build does not know: fail closed.
            Some(_) => Some("unsafe"),
        };
        if let Some(safety) = safety {
            graph.refuse(
                key.clone(),
                ReplayRefusal::NotReplayable {
                    name: key.clone(),
                    safety,
                },
            );
        }
        // The loader dropped this module's declaration of the name in favour
        // of another module's (or a kernel seed): what the base holds under it
        // is not this declaration, and Lean's `addDecl` refuses it.
        if let Some(held_by) = already_declared.and_then(|m| m.get(&key)) {
            graph.refuse(
                key.clone(),
                ReplayRefusal::AlreadyDeclared {
                    name: key.clone(),
                    reason: held_by.clone(),
                },
            );
        }
        rows.insert(
            key,
            Row {
                name: name.clone(),
                kind,
                value,
            },
        );
    }

    // A name THIS module's parts declared that is not a shard row: a
    // `.olean.server`-only family, or a `.olean.private` family the bridge
    // could not merge, is resident in the base but never replayed here. Mark
    // it unreplayed so any row that mentions it is refused
    // `DependsOnUnreplayed`, as Lean's replay refuses a reference to a constant
    // its environment does not hold (finding B1). The `.olean` loader already
    // refuses the server-only case as a whole (`MisplacedDeclaration`); this is
    // the per-module defence behind it.
    if let Some(declared) = module_declared {
        for name in declared {
            if !rows.contains_key(name) {
                graph.mark_unreplayed(name.clone());
            }
        }
    }

    let schedule = graph.schedule();
    // Lean's replay of the module's inductive blocks (`clean_olean::replay_families`):
    // every stored constructor and recursor must be what the kernel generates
    // from the stored types. The base holds each block as the `.olean` stores it.
    let local: BTreeSet<Name> = rows.keys().cloned().collect();
    let families = inductive_block_refusals(base, &local, &local);
    let mut verdicts = ReplayVerdicts::new();
    for key in schedule.order() {
        let Some(row) = rows.remove(key) else {
            continue;
        };
        let admitted = schedule
            .admission_gate(key, &verdicts)
            .and_then(|()| families.get(key).cloned().map_or(Ok(()), Err));
        let verdict = match (admitted, row.value) {
            // The constant is itself unsafe/partial: never admitted, never a
            // failure (Lean's replay does not replay it at all). A value-bearing
            // one is the sequential lane's `UnsafeAccepted`; an inductive-family
            // member stays trusted context, as before.
            (Err(refusal @ ReplayRefusal::NotReplayable { .. }), value) => {
                if value.is_some() {
                    v.unsafe_accepted += 1;
                } else {
                    v.axiom_accepted += 1;
                }
                Err(refusal)
            }
            (Err(refusal), _) => {
                v.failed += 1;
                v.failures.push((row.name, refusal.to_string()));
                Err(refusal)
            }
            // Inductive families, quotients and axioms carry no proof term:
            // trusted members of the base, never KernelVerified (as before), and
            // admitted for their dependents once their own references are.
            (Ok(()), None) => {
                v.axiom_accepted += 1;
                Ok(())
            }
            (Ok(()), Some(ValueRow::ReconstructFailed(msg))) => {
                v.reconstruct_failed += 1;
                v.failures.push((row.name, format!("reconstruct: {msg}")));
                Err(not_admitted(key, "its value could not be reconstructed"))
            }
            (Ok(()), Some(ValueRow::NoValue)) => {
                v.axiom_fallback += 1;
                v.axiom_fallback_names.push((
                    row.name,
                    format!(
                        "no value in shard for {:?} row (opaque/meta value elided at \
                         olean->shard conversion; stamped Axiomatized)",
                        row.kind
                    ),
                ));
                Err(not_admitted(
                    key,
                    "no value in shard, so it was never checked",
                ))
            }
            (Ok(()), Some(ValueRow::Checkable(decl))) => {
                check_value_bearing(base, &decl, &row.name, heartbeat_escalate, v).map_err(
                    |message| ReplayRefusal::KernelRejected {
                        name: key.clone(),
                        message,
                    },
                )
            }
        };
        verdicts.insert(key.clone(), verdict);
        const PURGE_EVERY: usize = 64;
        if verdicts.len().is_multiple_of(PURGE_EVERY) {
            purge_freed_arena();
        }
    }
}

fn not_admitted(name: &Name, why: &str) -> ReplayRefusal {
    ReplayRefusal::KernelRejected {
        name: name.clone(),
        message: format!("not admitted: {why}"),
    }
}

fn build_decl(
    name: &str,
    kind: DeclKind,
    level_params: Vec<Name>,
    type_: clean_kernel::expr::Expr,
    value: clean_kernel::expr::Expr,
) -> Declaration {
    let name = Name::from_string(name);
    match kind {
        DeclKind::Theorem => Declaration::Theorem {
            name,
            level_params,
            type_,
            value,
        },
        DeclKind::Opaque => Declaration::Opaque {
            name,
            level_params,
            type_,
            value,
        },
        // Match the sequential path: projection bodies are reducible so
        // is_def_eq can unfold them. Soundness-neutral (unfold_definition gates
        // only on Opaque, never on Reducibility — see `try_add_decl`).
        _ => {
            let is_reducible = clean_olean::import::is_projection_fn_body(&value);
            Declaration::Definition {
                name,
                level_params,
                type_,
                value,
                is_reducible,
            }
        }
    }
}

/// The unchanged per-constant kernel gauntlet: Tier-1 check, Tier-2 retry on a
/// `HeartbeatExceeded` only, `KernelVerified` iff the kernel accepted. `Err`
/// carries the message recorded as the constant's axiom fallback.
fn check_value_bearing(
    base: &Environment,
    decl: &Declaration,
    name: &str,
    heartbeat_escalate: Option<u32>,
    v: &mut ModuleVerdicts,
) -> Result<(), String> {
    match base.check_decl_readonly_with_heartbeat(decl, None) {
        Ok(()) => {
            v.kernel_verified += 1;
            v.kernel_verified_names.push(name.to_string());
            Ok(())
        }
        Err(EnvError::TypeCheckFailed {
            source: KernelTypeError::HeartbeatExceeded { .. },
            ..
        }) if heartbeat_escalate.is_some() => {
            match base.check_decl_readonly_with_heartbeat(decl, heartbeat_escalate) {
                Ok(()) => {
                    v.kernel_verified += 1;
                    v.kernel_verified_names.push(name.to_string());
                    v.heartbeat_escalated_recovered += 1;
                    Ok(())
                }
                Err(e) => {
                    v.axiom_fallback += 1;
                    v.axiom_fallback_names
                        .push((name.to_string(), e.to_string()));
                    Err(e.to_string())
                }
            }
        }
        Err(e) => {
            v.axiom_fallback += 1;
            if let EnvError::TypeCheckFailed {
                source:
                    KernelTypeError::HeartbeatExceeded {
                        profile: Some(p), ..
                    },
                ..
            } = &e
            {
                eprintln!("=== HEARTBEAT PROFILE: {name} ===\n{p}");
            }
            v.axiom_fallback_names
                .push((name.to_string(), e.to_string()));
            Err(e.to_string())
        }
    }
}
