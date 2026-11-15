// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean olean replay <Module>...`: the pinned toolchain's `leanchecker`,
//! with Clean's kernel as the checker.
//!
//! `leanchecker` (`src/lean/LeanChecker.lean`, v4.30.0-rc2) has two modes, and
//! so does this verb ([`ReplayMode`]):
//!
//! - `replayFromImports` (the default): load the module's IMPORTS as the
//!   trusted starting environment, then replay the module's own declarations
//!   — every constant of its most private `.olean` part — with
//!   `Lean.Environment.replay` (`src/lean/Lean/Replay.lean`);
//! - `replayFromFresh` (`--fresh`, one module only): import the module, then
//!   replay EVERY constant of the closure, the imports' and the module's, into
//!   an empty environment.
//!
//! Every piece is the Phase 0 replay machinery, assembled, not a second path:
//! the starting environment is `Environment::for_lean_replay` (no declaration,
//! Lean's canonical quotient, nothing else) in `KernelTheory::Lean`; the
//! module's declarations reach the environment only through the `.olean`
//! loader; `verify_batch_full` replays them in Lean's order
//! (`crate::replay_order`, a port of `replayConstant`), rebuilds every stored
//! inductive block through the kernel's own admission and compares its
//! constructors and recursors with the stored ones (`crate::replay_families`),
//! refuses a name the environment already held, and checks each constant
//! before it is admitted. The replay stops nothing early — every declaration
//! gets a verdict — and reports the first refusal in replay order with its
//! reason, which is what `leanchecker` prints before it exits 1.
//!
//! Two of `Lean.Environment.replay`'s rules are applied here, before the
//! replay, because only this caller knows which constants are the module's:
//!
//! - `unsafe` and `partial` constants are left out (`!ci.isUnsafe &&
//!   !ci.isPartial`): neither verified nor refused, counted as
//!   `not_replayable`. A safe declaration that uses one is still refused, by
//!   the kernel's safe context;
//! - a declaration of the module that the loader could not register AS
//!   STORED (`LoadSummary::skipped_constants`: a structural refusal — a
//!   duplicate or undeclared universe parameter, a free variable — a
//!   private-part value the load-time check refused, or a compiler artifact)
//!   is refused by name, fail-closed, and so is every declaration that uses
//!   it. Lean's replay would send each to the kernel; nothing here may let one
//!   pass unchecked. The one exception is a skipped compiler artifact the
//!   `.olean` marks `unsafe` or `partial` (`skipped_not_replayable`): Lean's
//!   replay leaves it out, so this one does too.
//!
//! What the loader reports is cross-checked against the name table each
//! replayed module's `.olean` stores (`accounting`): a declaration the loader
//! dropped without reporting it is refused by name, never skipped.
//!
//! The load is kernel-only (`OleanImportPolicy::with_kernel_only`): none of
//! the elaborator tables the loader otherwise derives from extension entries,
//! which Lean's kernel never reads.
//!
//! And it leaves to this replay the refusals `leanchecker` makes per
//! declaration (`OleanImportPolicy::with_replay_refusals`): the loader
//! otherwise refuses the WHOLE import for a name two artifacts declare and for
//! a declaration that depends on itself, which reported a forged module as an
//! unnamed load error and refused a module whose IMPORT is forged, which
//! `leanchecker` trusts. Here a redeclaration is `already declared` (the
//! replay, or with `--fresh` the import, `load_refusals`), a self-reference or
//! cycle is refused by the replay order, and an import is trusted. A load
//! that still fails is reported with a refusal naming what it was about.
//!
//! The `.olean` loader's `noConfusion` regeneration is NOT run: it would
//! replace the module's stored `noConfusionType`/`noConfusion` with Clean's
//! own before the check, and the stored ones are what `leanchecker` checks.

mod accounting;
mod load_refusals;
mod targets;

use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;
use std::time::Instant;

use clean_kernel::env::{ConstantKind, Environment, KernelTheory};
use clean_kernel::name::Name;
use serde::Serialize;

use crate::verify_batch_full::{typecheck_constants_full_ordered, ReplayScope};
use crate::{load_module_with_deps_shared_with_policy, LoadSummary, OleanImportPolicy};

use load_refusals::{import_merge_refusals, load_error_refusals};
pub(crate) use targets::{replay_search_path, select_modules, ReplayTargetError};

/// The policy the replay loads a closure with: the kernel's declarations only,
/// and the refusals `leanchecker` makes per declaration left to the replay.
fn replay_load_policy() -> OleanImportPolicy {
    OleanImportPolicy::default()
        .with_kernel_only()
        .with_replay_refusals()
}

/// Which environment a module's declarations are replayed into.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum ReplayMode {
    /// `leanchecker <Module>` (`replayFromImports`): the imports are trusted,
    /// the module's own declarations are replayed.
    ImportsTrusted,
    /// `leanchecker --fresh <Module>` (`replayFromFresh`): every declaration of
    /// the closure is replayed.
    Fresh,
}

/// What kind of refusal a [`RefusalRecord`] is. Neither kind is admitted.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum RefusalOutcome {
    /// Refused on a finding: the kernel, the replay order, the loader, the
    /// import merge or the accounting ruled against the declaration.
    Refused,
    /// Not decided: every failed kernel check of the declaration had spent its
    /// `--max-heartbeats` budget (`ReplayRefusal::BudgetExhausted`), or every
    /// dependency refusing it was not decided for that reason
    /// (`ReplayRefusal::undecided`). Not admitted (fail-closed), and no
    /// verdict that it is ill-typed.
    BudgetExhausted,
}

/// One refused declaration: its name, why, and what kind of refusal it is.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(crate) struct RefusalRecord {
    /// The refused constant.
    pub(crate) constant: String,
    /// The refusal, as the replay or the kernel states it.
    pub(crate) reason: String,
    /// A finding, or the heartbeat budget running out.
    pub(crate) outcome: RefusalOutcome,
}

impl RefusalRecord {
    /// A refusal on a finding ([`RefusalOutcome::Refused`]).
    pub(crate) fn refused(constant: String, reason: String) -> Self {
        Self {
            constant,
            reason,
            outcome: RefusalOutcome::Refused,
        }
    }
}

/// The verdict on one module: the `--json` record.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct ModuleReplayRecord {
    /// The replayed module.
    pub(crate) module: String,
    /// Which environment it was replayed into.
    pub(crate) mode: ReplayMode,
    /// Loaded, and every replayed declaration admitted.
    pub(crate) ok: bool,
    /// Declarations the replay covered: every `.olean` constant of the replayed
    /// part(s) except the `unsafe`/`partial` ones.
    pub(crate) constants_checked: usize,
    /// Declarations the kernel admitted.
    pub(crate) admitted: usize,
    /// Refusals that are the heartbeat budget running out, not a finding
    /// ([`RefusalOutcome::BudgetExhausted`]); included in `refusals`.
    pub(crate) budget_exhausted: usize,
    /// `unsafe`/`partial` constants left out, as `Lean.Environment.replay` does.
    pub(crate) not_replayable: usize,
    /// Theorems restating an identical imported theorem, which Lean's replay
    /// skips.
    pub(crate) restated: usize,
    /// The first refusal in replay order (`leanchecker` stops there).
    pub(crate) first_refusal: Option<RefusalRecord>,
    /// Every refusal: the ones found before the replay (load, import merge,
    /// accounting) first, then the replay's own in replay order.
    pub(crate) refusals: Vec<RefusalRecord>,
    /// The `.olean` closure could not be loaded at all.
    pub(crate) load_error: Option<String>,
    /// Milliseconds spent loading the closure.
    pub(crate) load_ms: u64,
    /// Milliseconds spent replaying.
    pub(crate) replay_ms: u64,
    /// Peak resident set size of this process so far, in bytes.
    pub(crate) peak_rss_bytes: Option<u64>,
}

/// The loader labels of the parts of `module` (`load_companions_direct`).
fn part_labels(module: &str) -> [String; 3] {
    [
        module.to_owned(),
        format!("{module}._server"),
        format!("{module}._private"),
    ]
}

/// What the replayed part(s) declare, split the way the replay needs it.
#[derive(Default)]
struct Declared {
    /// Display names to replay.
    targets: BTreeSet<String>,
    /// Declarations whose name the environment already held (display name to
    /// who holds it); replayed, and refused as already declared.
    already_declared: BTreeMap<String, String>,
    /// Declarations the loader could not register as stored, with why.
    not_loaded: BTreeMap<String, String>,
    /// `unsafe`/`partial` declarations, left out.
    not_replayable: BTreeSet<String>,
    /// Theorems restating an identical resident theorem, which Lean's replay
    /// skips (`replayConstant`'s duplicate-theorem check), left out.
    restated: BTreeSet<String>,
}

fn declared(
    env: &Environment,
    summaries: &[LoadSummary],
    replayed: &dyn Fn(&str) -> bool,
    seeded: &BTreeSet<Name>,
) -> Declared {
    let mut out = Declared::default();
    let mut resident: BTreeSet<Name> = BTreeSet::new();
    // Seeded names an import (a module NOT replayed) already declared: Lean's
    // starting environment holds those, so the module's own declaration of one
    // is already declared (see `restatement`).
    let seeded_by_import: BTreeSet<Name> = summaries
        .iter()
        .filter(|s| !s.module_name.as_deref().is_some_and(replayed))
        .flat_map(|s| s.restated_declarations.iter().map(|(name, _, _)| name))
        .filter(|name| seeded.contains(*name))
        .cloned()
        .collect();
    // A skipped declaration's status comes from the LAST part that stores it:
    // parts load base, then `.olean.server`, then `.olean.private`, and
    // `leanchecker` replays the most private part's `ConstantInfo`. Measured
    // 2026-09-25: `Lean.Name.beq._unsafe_rec` (a `partial` definition in
    // Lean) was skipped by the base part without a safety mark and by the
    // private part as `partial`.
    let mut skipped: BTreeMap<String, Option<String>> = BTreeMap::new();
    // A restatement's kind likewise: under the module system the exported part
    // stores a theorem as a value-less AXIOM and the private part the theorem
    // (measured 2026-09-26, `String.pos.congr_simp` in
    // `Init.Data.String.Search`, restating `Init.Data.String.Lemmas.Basic`'s),
    // and Lean's replay reads the private one: a restated theorem, skipped.
    let mut restated: BTreeMap<Name, (String, bool)> = BTreeMap::new();
    for summary in summaries {
        if !summary.module_name.as_deref().is_some_and(replayed) {
            continue;
        }
        resident.extend(summary.added_names.iter().cloned());
        for (name, held_by) in &summary.shadowed_declarations {
            out.already_declared
                .entry(name.to_string())
                .or_insert_with(|| held_by.clone());
        }
        for (name, held_by, incoming_theorem) in &summary.restated_declarations {
            restated.insert(name.clone(), (held_by.clone(), *incoming_theorem));
        }
        for constant in &summary.skipped_constants {
            let status = if summary.skipped_not_replayable.contains(&constant.name) {
                None
            } else {
                Some(constant.reason.clone())
            };
            skipped.insert(constant.name.clone(), status);
        }
    }
    for (name, (held_by, incoming_theorem)) in &restated {
        let seed = Seed {
            seeded: seeded.contains(name),
            by_import: seeded_by_import.contains(name),
        };
        restatement(env, &mut out, name, held_by, *incoming_theorem, seed);
    }
    for (name, status) in skipped {
        match status {
            None => {
                out.not_replayable.insert(name);
            }
            Some(reason) => {
                out.not_loaded.insert(name, reason);
            }
        }
    }
    for name in resident {
        let label = name.to_string();
        if out.not_loaded.contains_key(&label)
            || out.not_replayable.contains(&label)
            || out.restated.contains(&label)
        {
            continue;
        }
        if env.is_unsafe(&name) || env.is_partial(&name) {
            out.not_replayable.insert(label);
        } else {
            out.targets.insert(label);
        }
    }
    out.targets.extend(out.already_declared.keys().cloned());
    out
}

/// Whether a restated name is one `Environment::for_lean_replay` seeds, and
/// whether an import (a module not replayed) already restated it.
#[derive(Clone, Copy)]
struct Seed {
    seeded: bool,
    by_import: bool,
}

/// Decide a declaration the loader dropped as a restatement of the resident
/// one, by Lean's rules. Lean's replay (`replayConstant`) skips a theorem whose
/// resident namesake is a theorem of the same type and universe parameters, and
/// sends everything else to `addDecl`, which refuses a name the environment
/// holds.
///
/// A name the replay environment seeds itself (`Environment::for_lean_replay`,
/// read before the load) needs care, because Lean's starting environment holds
/// it only if an import declared it, and the seeded constant carries no
/// provenance tag to say so:
///
/// - `Quot.sound`: Clean's canonical quotient includes it, Lean's `quotDecl`
///   does not, and `Init.Core` declares it as an axiom (measured 2026-09-26:
///   the replay of `Init.Core` refused it as already declared). An AXIOM
///   restating it with the seeded type is the module's own declaration, and is
///   replayed as the (identical) resident one, UNLESS an import already
///   restated it: then Lean's environment holds it and `addDecl` refuses
///   (measured 2026-09-26, pinned `leanchecker`: a module importing `Init.Core`
///   and declaring `axiom Quot.sound` is refused `constant has already been
///   declared 'Quot.sound'`; this function used to replay it as the module's
///   own and admit it);
/// - `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`: Lean holds these only through
///   `quotDecl` (a stored `quotInfo`, which the loader keeps as the seed and
///   never lists here); a restatement of one is an axiom or theorem of that
///   name, which `addDecl` refuses once `Init.Prelude`'s `init_quot` has run
///   (measured the same day: `axiom Quot.ind` over `Init.Prelude`, refused by
///   `leanchecker` in both modes, was admitted here). Refused here
///   unconditionally, the fail-closed side of a module with no quotient import;
/// - a THEOREM restating a seeded name: its value is what Lean's replay would
///   check, and the loader did not register it, so it is refused unchecked.
fn restatement(
    env: &Environment,
    out: &mut Declared,
    name: &Name,
    held_by: &str,
    incoming_theorem: bool,
    seed: Seed,
) {
    let label = name.to_string();
    let resident = env.get_const(name);
    if seed.seeded {
        if incoming_theorem {
            out.not_loaded.insert(
                label,
                "a theorem restating a constant the replay environment seeds: Lean's \
                 replay checks its value, which was not registered"
                    .to_owned(),
            );
        } else if accounting::QUOT_PRIMITIVES.contains(&label.as_str()) {
            out.already_declared
                .entry(label)
                .or_insert_with(|| "Lean's quotient (`quotDecl`)".to_owned());
        } else if seed.by_import {
            out.already_declared
                .entry(label)
                .or_insert_with(|| "an import".to_owned());
        } else {
            out.targets.insert(label);
        }
    } else if incoming_theorem && resident.is_some_and(|c| c.kind == ConstantKind::Theorem) {
        out.restated.insert(label);
    } else {
        out.already_declared
            .entry(label)
            .or_insert_with(|| held_by.to_owned());
    }
}

/// The replayed modules' `.olean` declarations nothing in `own` accounts for,
/// as refusals (`accounting`): the named module, or under `--fresh` every
/// module of the closure.
fn unaccounted(
    module: &str,
    mode: ReplayMode,
    summaries: &[LoadSummary],
    search_path: &[PathBuf],
    own: &Declared,
) -> Vec<RefusalRecord> {
    let modules: BTreeSet<&str> = match mode {
        ReplayMode::ImportsTrusted => std::iter::once(module).collect(),
        ReplayMode::Fresh => summaries
            .iter()
            .filter_map(|s| s.module_name.as_deref())
            .filter(|label| !label.ends_with("._server") && !label.ends_with("._private"))
            .collect(),
    };
    let covered = |name: &str| {
        own.targets.contains(name)
            || own.not_loaded.contains_key(name)
            || own.not_replayable.contains(name)
            || own.restated.contains(name)
    };
    let mut refusals = Vec::new();
    for replayed in modules {
        match accounting::unaccounted_declarations(replayed, search_path, &covered) {
            Ok(names) => refusals.extend(names.into_iter().map(|constant| {
                RefusalRecord::refused(
                    constant,
                    format!(
                        "declared by `{replayed}`'s .olean, but the loader neither registered \
                         nor refused it, so nothing here checked it (Lean's replay would)"
                    ),
                )
            })),
            Err(error) => refusals.push(RefusalRecord::refused(
                replayed.to_owned(),
                format!("cannot account for the module's declarations: {error}"),
            )),
        }
    }
    refusals
}

/// Peak resident set size of this process, in bytes (`getrusage`).
fn peak_rss_bytes() -> Option<u64> {
    // SAFETY: an all-zero `rusage` is a valid value of this plain C struct, and
    // `getrusage` only writes into the struct it is handed.
    let mut usage: libc::rusage = unsafe { std::mem::zeroed() };
    // SAFETY: `usage` is a live, exclusively borrowed `rusage`.
    if unsafe { libc::getrusage(libc::RUSAGE_SELF, &mut usage) } != 0 {
        return None;
    }
    let raw = u64::try_from(usage.ru_maxrss).ok()?;
    // `ru_maxrss` is bytes on macOS and kilobytes on Linux.
    Some(if cfg!(target_os = "macos") {
        raw
    } else {
        raw.saturating_mul(1024)
    })
}

fn millis(since: Instant) -> u64 {
    u64::try_from(since.elapsed().as_millis()).unwrap_or(u64::MAX)
}

/// Replay one module as `leanchecker` does, with Clean's kernel.
///
/// `max_heartbeats` is the kernel budget of each check of a declaration (its
/// stored types, its header, its value; the inductive-block rebuild and the
/// loader's `.olean.private` value check run under the kernel's default limit
/// instead); `0` is unlimited, which is what `Lean.Environment.replay` runs
/// with (`addDeclCore 0`).
pub(crate) fn replay_module(
    module: &str,
    mode: ReplayMode,
    search_path: &[PathBuf],
    max_heartbeats: u32,
) -> ModuleReplayRecord {
    let start = Instant::now();
    let mut record = ModuleReplayRecord {
        module: module.to_owned(),
        mode,
        ok: false,
        constants_checked: 0,
        admitted: 0,
        budget_exhausted: 0,
        not_replayable: 0,
        restated: 0,
        first_refusal: None,
        refusals: Vec::new(),
        load_error: None,
        load_ms: 0,
        replay_ms: 0,
        peak_rss_bytes: None,
    };
    let mut env = Environment::for_lean_replay();
    // What the replay environment holds before any `.olean` is loaded.
    let seeded: BTreeSet<Name> = env.constants().map(|c| c.name.clone()).collect();
    // The loader kernel-checks each `.olean.private` value before installing
    // it over its stub; that check runs in Lean's kernel theory too, so a value
    // is never refused, or admitted, by a reducer Lean's kernel does not have.
    // An `unsafe` value it refuses in Lean's safe context is left out, as
    // Lean's replay leaves it out (`LoadSummary::skipped_not_replayable`).
    env.set_kernel_theory(KernelTheory::Lean);
    let mut visited = hashbrown::HashSet::new();
    let loaded = load_module_with_deps_shared_with_policy(
        &mut env,
        module,
        search_path,
        &mut visited,
        replay_load_policy(),
    );
    record.load_ms = millis(start);
    let summaries = match loaded {
        Ok(summaries) => summaries,
        Err(error) => {
            record.refusals = load_error_refusals(module, &error);
            record.first_refusal = record.refusals.first().cloned();
            record.load_error = Some(error.to_string());
            record.peak_rss_bytes = peak_rss_bytes();
            return record;
        }
    };
    let labels = part_labels(module);
    let replayed = |label: &str| mode == ReplayMode::Fresh || labels.iter().any(|l| l == label);
    let own = declared(&env, &summaries, &replayed, &seeded);
    let unaccounted = unaccounted(module, mode, &summaries, search_path, &own);
    let import_merge = import_merge_refusals(mode, &summaries, &replayed);
    record.not_replayable = own.not_replayable.len();
    record.restated = own.restated.len();
    record.constants_checked = own.targets.len() + own.not_loaded.len() + unaccounted.len();

    let replay_start = Instant::now();
    let none = BTreeSet::new();
    let not_loaded: BTreeSet<String> = own.not_loaded.keys().cloned().collect();
    let scope = ReplayScope {
        prerequisites: &none,
        not_admitted: &not_loaded,
        already_declared: &own.already_declared,
    };
    let replay = typecheck_constants_full_ordered(&env, &own.targets, &scope, max_heartbeats);
    record.replay_ms = millis(replay_start);
    record.admitted = replay.pass;

    // A name Lean's import refuses never reaches its replay: that refusal is
    // the name's record, and the replay's own verdict on it is not repeated.
    let refused_at_import: BTreeSet<String> =
        import_merge.iter().map(|r| r.constant.clone()).collect();
    record.refusals.extend(import_merge);
    record.refusals.extend(unaccounted);
    for (constant, reason) in &own.not_loaded {
        record.refusals.push(RefusalRecord::refused(
            constant.clone(),
            format!("the .olean loader could not register it as stored: {reason}"),
        ));
    }
    let ordered: BTreeSet<String> = replay.verdicts.iter().map(|(n, _)| n.to_string()).collect();
    for (label, error) in &replay.errors {
        if !ordered.contains(label) && !refused_at_import.contains(label) {
            record
                .refusals
                .push(RefusalRecord::refused(label.clone(), error.clone()));
        }
    }
    for (name, verdict) in &replay.verdicts {
        if let Err(refusal) = verdict {
            // The budget's doing: the declaration was not decided, or every
            // dependency refusing it was not (`ReplayRefusal::undecided`).
            let outcome = if refusal.undecided() {
                RefusalOutcome::BudgetExhausted
            } else {
                RefusalOutcome::Refused
            };
            let constant = name.to_string();
            if !refused_at_import.contains(&constant) {
                record.refusals.push(RefusalRecord {
                    constant,
                    reason: refusal.to_string(),
                    outcome,
                });
            }
        }
    }
    if record.refusals.is_empty() && replay.fail != 0 {
        // Fail-closed: a failure the accounting counted must never read as a
        // pass because no message was attached to it.
        record.refusals.push(RefusalRecord::refused(
            module.to_owned(),
            format!(
                "{} declaration(s) failed without a recorded reason",
                replay.fail
            ),
        ));
    }
    record.budget_exhausted = record
        .refusals
        .iter()
        .filter(|r| r.outcome == RefusalOutcome::BudgetExhausted)
        .count();
    record.first_refusal = record.refusals.first().cloned();
    record.ok = record.refusals.is_empty();
    record.peak_rss_bytes = peak_rss_bytes();
    record
}

#[cfg(test)]
mod tests;
