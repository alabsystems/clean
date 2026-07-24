// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Witness sourcing** for the cross-lane `KernelBridged` discharge.
//!
//! The bridge discharge ([`super::batch::try_bridge_discharge`]) needs the named
//! Mathlib-KV witness constant **resident in the replay environment with its
//! value** — the discharge builds `@Iff.mpr isa witness_type bridge witness`, and
//! for that minted proof to (a) kernel-check and (b) carry a foundational-only
//! axiom closure, the witness must be present as a value-bearing constant whose
//! own transitive closure the kernel can walk.
//!
//! Until now nothing PUT the Mathlib-KV constants into that env; the fixture tests
//! seeded a hand-built witness. This module closes that gap: it reads a directory
//! of `.mathverse` shards (the Mathlib import lane's `KernelVerified` output —
//! exactly what `clean mathverse stamp-verified` writes, values included) and
//! loads the manifest-named witnesses (type **and** value) into the replay env
//! through the kernel's own [`Environment::add_decl`], re-checking each value.
//!
//! ## Soundness
//!
//! A witness is admitted only if:
//! 1. it is stamped `KernelVerified` in the shard (`shard_dir_facts` reads the
//!    header verdict) — the Mathlib lane already re-checked its value;
//! 2. it is **level-monomorphic** (the connective composer works over ground
//!    `Prop`s, and the discharge references the witness level-free);
//! 3. it is value-bearing and definitional (`Theorem`/`Definition`);
//! 4. Clean's kernel **re-accepts** its value via `add_decl` against the current
//!    replay env (so a witness whose dependency closure is not resident is
//!    declined, never trusted blindly); and
//! 5. the re-added constant's transitive axiom closure is
//!    `⊆ FOUNDATIONAL_AXIOMS`.
//!
//! Every gate is the kernel's, never a manifest assertion — a shard cannot mint a
//! usable witness by fiat. A witness that fails any gate is simply skipped (the
//! bridge then declines that line), so this is **inert** unless it strengthens the
//! env with genuinely re-checked foundational constants.

use std::collections::BTreeSet;
use std::path::Path;

use clean_kernel::env::is_foundational_axiom;
use clean_kernel::{Declaration, Environment};

use crate::closure_source::shard_dir_facts;
use crate::types::DeclKind;

/// Per-run accounting for [`load_bridge_witnesses`] — the witness-sourcing
/// **funnel**, so a driver can report how much of the manifest actually
/// resolved to a resident foundational witness.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub(crate) struct WitnessLoadStats {
    /// Distinct witness names the manifest asks for.
    pub(crate) requested: usize,
    /// Requested names found present in the shard directory.
    pub(crate) present: usize,
    /// Present names that are KV + value-bearing + level-monomorphic +
    /// definitional (the pre-kernel candidate set).
    pub(crate) candidates: usize,
    /// Witnesses now resident in the env with a foundational-only closure — the
    /// set the discharge can actually compose against (includes names already
    /// resident, e.g. via the prelude).
    pub(crate) loaded: usize,
    /// Present but not stamped `KernelVerified` in the shard.
    pub(crate) skipped_not_kv: usize,
    /// Present + KV but value-less / non-definitional (axiom / opaque / inductive
    /// family) — no usable proof value to compose against.
    pub(crate) skipped_no_value: usize,
    /// Present + KV + value but level-polymorphic (out of composer scope).
    pub(crate) skipped_polymorphic: usize,
    /// Candidate whose value the kernel REJECTED on `add_decl` (typically its
    /// dependency closure was not resident in the replay env).
    pub(crate) skipped_kernel_reject: usize,
    /// Candidate the kernel accepted but whose closure was NOT foundational —
    /// never a usable bridged witness (the discharge would smuggle a domain
    /// axiom); declined.
    pub(crate) skipped_non_foundational: usize,
}

/// Load the manifest-named Mathlib-KV witnesses (type **and** value) from the
/// `.mathverse` shards under `shard_dir` into `env`, gated entirely by the
/// kernel (see the module soundness note). Returns the load funnel.
///
/// Non-fatal throughout: an unreadable directory, a missing witness, or a
/// rejected value each just decline that witness — the bridge then falls through
/// to the unchanged ledger/reject path for the affected line. The caller is
/// expected to have already registered any base inductives the witnesses need
/// (`init_iff` / `init_or` / `init_exists` / `init_classical`).
pub(crate) fn load_bridge_witnesses(
    env: &mut Environment,
    shard_dir: &Path,
    wanted: &BTreeSet<String>,
) -> WitnessLoadStats {
    let mut stats = WitnessLoadStats {
        requested: wanted.len(),
        ..Default::default()
    };
    // Reading the shard dir is a pure READ — no verify job, no build.
    let facts = match shard_dir_facts(shard_dir) {
        Ok(f) => f,
        Err(_) => return stats, // unreadable/empty dir ⇒ inert
    };
    for fact in facts {
        if !wanted.contains(&fact.name.to_string()) {
            continue;
        }
        stats.present += 1;

        // Already resident (prelude / an earlier witness) — usable as-is iff its
        // closure is foundational. Do not re-add (the kernel would reject a
        // duplicate); just gate on the closure.
        if env.get_const(&fact.name).is_some() {
            if witness_closure_foundational(env, &fact.name) {
                stats.loaded += 1;
            } else {
                stats.skipped_non_foundational += 1;
            }
            continue;
        }

        if !fact.kernel_verified {
            stats.skipped_not_kv += 1;
            continue;
        }
        let Some(value) = fact.value.clone() else {
            stats.skipped_no_value += 1;
            continue;
        };
        if !fact.level_params.is_empty() {
            stats.skipped_polymorphic += 1;
            continue;
        }
        let decl = match DeclKind::try_from(fact.decl_kind) {
            Ok(DeclKind::Theorem) => Declaration::Theorem {
                name: fact.name.clone(),
                level_params: Vec::new(),
                type_: fact.type_.clone(),
                value,
            },
            Ok(DeclKind::Definition) => Declaration::Definition {
                name: fact.name.clone(),
                level_params: Vec::new(),
                type_: fact.type_.clone(),
                value,
                is_reducible: false,
            },
            // Opaque/Axiom/inductive-family: no composable value.
            _ => {
                stats.skipped_no_value += 1;
                continue;
            }
        };
        stats.candidates += 1;

        // The kernel re-checks the witness value here — a witness whose closure
        // is not resident is REJECTED, never trusted on the shard's word.
        if env.add_decl(decl).is_err() {
            stats.skipped_kernel_reject += 1;
            continue;
        }
        // Minting floor: the re-added witness must itself be foundational, else it
        // is not a Mathlib-KV-grade witness. (The discharge re-checks this too;
        // gating here keeps a non-foundational constant from lingering as a
        // tempting-but-unusable witness.)
        if witness_closure_foundational(env, &fact.name) {
            stats.loaded += 1;
        } else {
            stats.skipped_non_foundational += 1;
        }
    }
    stats
}

/// Whether `name`'s transitive axiom closure in `env` is `⊆ FOUNDATIONAL_AXIOMS`.
fn witness_closure_foundational(env: &Environment, name: &clean_kernel::Name) -> bool {
    match env.axiom_deps(name) {
        Some(deps) => deps.iter().all(is_foundational_axiom),
        None => false,
    }
}

#[cfg(test)]
mod tests;
