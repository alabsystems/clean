// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Checked merge of a deserialized [`Environment`] into the live server
//! environment — the `loadEnvironment` merge mode (R1-SRV, census row
//! `srv-register-meta` in `data/env_bypass_census.json`).
//!
//! Every declaration in the loaded environment is RE-EARNED through the
//! kernel's checked admission paths before it becomes visible:
//!
//! - **Inductive families** are reassembled from the loaded side tables with
//!   [`Environment::inductive_decl_of`] — the same reconstruction the
//!   graduation lane's `carry_inductive_family`
//!   (`crates/clean-mathverse/src/graduate/intake_family.rs`) uses — and
//!   replayed through the full checked [`Environment::add_inductive`] path
//!   (the validate + rollback transaction in
//!   `crates/clean-kernel/src/env/inductive_builder.rs`: positivity, universe
//!   constraints, recursor generation). The full `add_inductive` (not
//!   `add_inductive_core`) is used because `loadEnvironment` round-trips
//!   Clean-native saved environments, whose `casesOn`/`recOn` recursor-table
//!   entries only the full path regenerates; a Lean-shaped environment whose
//!   recursor metadata the replay cannot regenerate fails closed with a named
//!   error pointing at `importModule` (the lane built for `.olean` merging).
//! - **Plain constants** are reconstructed as [`Declaration`]s and re-admitted
//!   through the checked [`Environment::add_decl`] (full type/value check),
//!   exactly as the merge-mode constants leg always did.
//!
//! Nothing is ever registered through the unchecked entry-API hooks
//! (`register_inductive` / `register_constructor` / `register_recursor`);
//! those `loadEnvironment` sites were closed by R1-SRV. Fail-closed: a family
//! or constant that cannot be replayed checked REFUSES the whole merge with a
//! named error, and the live environment is left untouched — the merge is
//! computed on a clone and committed by the handler only on success.

use std::collections::HashSet;

use clean_kernel::{ConstantInfo, ConstantKind, Declaration, Environment, InductiveDecl, Name};

/// One loaded inductive family awaiting its checked `add_inductive` replay.
struct PendingFamily {
    root: Name,
    decl: InductiveDecl,
    last_error: String,
}

/// One loaded plain constant awaiting its checked `add_decl` re-admission.
struct PendingConstant {
    name: Name,
    decl: Declaration,
    last_error: String,
}

/// Reconstruct the [`Declaration`] for a loaded serialized constant so it can
/// be re-admitted through the checked `add_decl` path.
///
/// A value-less `Definition` is unloadable (its error string is part of the
/// handler contract — tests assert it). A value-less `Theorem`/`Opaque` keeps
/// the historical fallback of substituting its type as the value, which the
/// kernel re-check then rejects unless the type genuinely inhabits itself —
/// fail-closed either way.
fn declaration_of(ci: &ConstantInfo) -> Result<Declaration, String> {
    Ok(match ci.kind {
        ConstantKind::Theorem => Declaration::Theorem {
            name: ci.name.clone(),
            level_params: ci.level_params.clone(),
            type_: ci.type_.clone(),
            value: ci.value.clone().unwrap_or_else(|| ci.type_.clone()),
        },
        ConstantKind::Opaque => Declaration::Opaque {
            name: ci.name.clone(),
            level_params: ci.level_params.clone(),
            type_: ci.type_.clone(),
            value: ci.value.clone().unwrap_or_else(|| ci.type_.clone()),
        },
        ConstantKind::Axiom => Declaration::Axiom {
            name: ci.name.clone(),
            level_params: ci.level_params.clone(),
            type_: ci.type_.clone(),
        },
        ConstantKind::Definition => {
            let Some(value) = ci.value.clone() else {
                return Err(format!("Cannot load value-less definition {}", ci.name));
            };
            Declaration::Definition {
                name: ci.name.clone(),
                level_params: ci.level_params.clone(),
                type_: ci.type_.clone(),
                value,
                is_reducible: ci.is_reducible,
            }
        }
    })
}

/// Merge `loaded` into `target` (the caller's copy of the live environment),
/// re-earning every declaration through the checked kernel paths. Returns the
/// merged environment on success; the caller commits it. On `Err`, nothing was
/// committed anywhere. The kernel's checks read the ambient deadline, so a
/// merge run under one (`loadEnvironment` runs it on the work pool) stops there.
///
/// Admission order is data-dependent (a constructor type may reference a
/// loaded definition and vice versa) and the loaded maps iterate unordered, so
/// admission runs as a worklist fixpoint: each pass retries every remaining
/// family and constant, and the merge is refused only when a full pass admits
/// nothing — with each stuck item's own kernel error named.
pub(super) fn checked_merge_loaded_env(
    target: Environment,
    loaded: &Environment,
) -> Result<Environment, String> {
    let mut merged = target;

    // ---- Families: reassemble each loaded family once (mutual blocks dedupe
    // via `all_names`), in sorted order for deterministic errors. ----
    let mut family_roots: Vec<&Name> = loaded.inductives().map(|ind| &ind.name).collect();
    family_roots.sort_by_key(|name| name.to_string());

    let mut covered: HashSet<Name> = HashSet::new();
    let mut families: Vec<PendingFamily> = Vec::new();
    for root in family_roots {
        if covered.contains(root) {
            continue;
        }
        let Some(decl) = loaded.inductive_decl_of(root) else {
            return Err(format!(
                "Checked inductive replay refused for family {root}: the loaded \
                 environment's side tables do not reassemble into a complete \
                 inductive declaration (missing mutual sibling or constructor \
                 metadata)"
            ));
        };
        covered.extend(decl.types.iter().map(|t| t.name.clone()));
        let present = decl
            .types
            .iter()
            .filter(|t| merged.get_const(&t.name).is_some())
            .count();
        if present == decl.types.len() {
            continue; // family names already present; the orphan audit below still runs
        }
        if present != 0 {
            return Err(format!(
                "Checked inductive replay refused for family {root}: {present} of {} \
                 mutual types already exist in the target environment — a \
                 partially-present family cannot be replayed checked",
                decl.types.len()
            ));
        }
        families.push(PendingFamily {
            root: root.clone(),
            decl,
            last_error: String::new(),
        });
    }

    // Names owned by the loaded inductive side tables. Their constants entries
    // are regenerated by the checked family replay (or already present in the
    // target), never admitted as bare constants — a value-less type-former or
    // constructor constant must not sneak in as a checked axiom.
    let mut family_owned: HashSet<&Name> = HashSet::new();
    for ind in loaded.inductives() {
        family_owned.insert(&ind.name);
        family_owned.extend(ind.constructor_names.iter());
    }
    family_owned.extend(loaded.constructors().map(|ctor| &ctor.name));
    family_owned.extend(loaded.recursors().map(|rec| &rec.name));

    // ---- Plain constants (definitions, axioms, theorems, opaques). ----
    let mut loaded_constants: Vec<&ConstantInfo> = loaded
        .constants()
        .filter(|ci| !family_owned.contains(&ci.name) && merged.get_const(&ci.name).is_none())
        .collect();
    loaded_constants.sort_by_key(|ci| ci.name.to_string());
    let mut constants: Vec<PendingConstant> = Vec::with_capacity(loaded_constants.len());
    for ci in loaded_constants {
        constants.push(PendingConstant {
            name: ci.name.clone(),
            decl: declaration_of(ci)?,
            last_error: String::new(),
        });
    }

    // ---- Worklist fixpoint. Both admission paths are transactional on
    // failure (`add_inductive` restores its snapshot; `add_decl` validates
    // before inserting), so retrying is safe. ----
    loop {
        let mut progressed = false;
        families.retain_mut(|family| match merged.add_inductive(family.decl.clone()) {
            Ok(()) => {
                progressed = true;
                false
            }
            Err(error) => {
                family.last_error = format!(
                    "Checked inductive replay refused for family {}: {error}",
                    family.root
                );
                true
            }
        });
        constants.retain_mut(|constant| {
            if merged.get_const(&constant.name).is_some() {
                // Generated meanwhile by a checked family replay
                // (`casesOn` / `noConfusion` / `below` / ...): the regenerated,
                // kernel-checked spelling wins, exactly as in the graduation lane.
                progressed = true;
                return false;
            }
            match merged.add_decl(constant.decl.clone()) {
                Ok(()) => {
                    progressed = true;
                    false
                }
                Err(error) => {
                    constant.last_error =
                        format!("Kernel validation failed for {}: {error}", constant.name);
                    true
                }
            }
        });
        if families.is_empty() && constants.is_empty() {
            break;
        }
        if !progressed {
            let reasons: Vec<&str> = families
                .iter()
                .map(|family| family.last_error.as_str())
                .chain(
                    constants
                        .iter()
                        .map(|constant| constant.last_error.as_str()),
                )
                .collect();
            return Err(reasons.join("; "));
        }
    }

    // ---- Orphan audit: nothing in the loaded inductive side tables may be
    // silently dropped OR silently substituted by a plain constant. Every
    // loaded family member must exist in the merged env's own checked side
    // tables (either replayed above or already present in the target). ----
    for ind in loaded.inductives() {
        if merged.get_inductive(&ind.name).is_none() {
            return Err(format!(
                "Checked inductive replay refused for family {}: the loaded inductive \
                 was not admitted by the checked replay (its name is occupied by a \
                 non-inductive constant in the target environment)",
                ind.name
            ));
        }
    }
    for ctor in loaded.constructors() {
        if merged.get_constructor(&ctor.name).is_none() {
            return Err(format!(
                "Checked inductive replay refused for constructor {}: it is not a \
                 member of any checked-replayed family (orphaned constructor metadata \
                 is never registered unchecked)",
                ctor.name
            ));
        }
    }
    for rec in loaded.recursors() {
        if merged.get_recursor(&rec.name).is_none() {
            return Err(format!(
                "Checked inductive replay refused for recursor {}: the checked replay \
                 did not regenerate it (orphaned or non-Clean-shaped recursor metadata \
                 is never registered unchecked; use importModule for .olean-based \
                 merging)",
                rec.name
            ));
        }
    }

    Ok(merged)
}
