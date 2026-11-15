// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The replay loop shared by [`super::recheck_closed`] (an empty replay
//! environment) and [`super::ImportedConeGate`] (the consumer's own base).
//!
//! One loop, so the two levels cannot drift apart in what they refuse: the
//! only difference between them is the `given` predicate, which says whether
//! a unit is already in the replay environment as the SAME declaration and
//! may therefore be skipped. For the closed replay nothing is ever given.

use clean_kernel::env::{Declaration, Environment};
use clean_kernel::inductive::InductiveDecl;
use clean_kernel::name::Name;
use std::collections::{BTreeMap, BTreeSet};

use super::extension_binding::{check_binding, extension_hook, BindingVerdict};
use super::replay::{replay_constant, replay_family};
use super::{
    mark_unavailable, ClosedRecheckOptions, ClosedRecheckRefusal, FamilyIndex, ReplayStats, Unit,
    UnitId,
};

/// Where the replay admits what it re-derives: a bare [`Environment`] (the
/// closed replay, the imported-cone gate), or the fenced reference entry
/// (`super::reference_base`), whose every admission is a full check in Lean's
/// theory. The loop reads the target's environment and writes ONLY through
/// these three admissions, so the two cannot differ in what reaches the
/// kernel.
pub(super) trait ReplayTarget {
    /// The environment admissions so far have built.
    fn env(&self) -> &Environment;
    /// Admit an ordinary declaration (`add_decl`).
    fn admit_decl(&mut self, decl: Declaration) -> Result<(), String>;
    /// Admit an inductive family block: `add_inductive_core`, or Clean's
    /// `add_inductive` when `clean_built`.
    fn admit_family(&mut self, decl: InductiveDecl, clean_built: bool) -> Result<(), String>;
    /// Install the kernel's quotient primitives (Lean's `add_quot`).
    fn install_quot(&mut self) -> Result<(), String>;
}

impl ReplayTarget for Environment {
    fn env(&self) -> &Environment {
        self
    }

    fn admit_decl(&mut self, decl: Declaration) -> Result<(), String> {
        self.add_decl(decl).map_err(|e| e.to_string())
    }

    fn admit_family(&mut self, decl: InductiveDecl, clean_built: bool) -> Result<(), String> {
        if clean_built {
            self.add_inductive(decl)
        } else {
            self.add_inductive_core(decl)
        }
        .map_err(|e| e.to_string())
    }

    fn install_quot(&mut self) -> Result<(), String> {
        self.add_quot()
    }
}

/// Whether a unit is already present in the replay environment.
pub(super) enum Given {
    /// Not present: replay it.
    No,
    /// Present as the same declaration: nothing to re-derive.
    Yes,
    /// Present under the same name but as a DIFFERENT declaration (or a family
    /// only partly present): refused, with the reason.
    Conflict(String),
}

/// Everything the loop reads, resolved once by the caller.
pub(super) struct ReplayPlan<'a> {
    pub(super) env: &'a Environment,
    pub(super) index: &'a FamilyIndex,
    pub(super) units: &'a BTreeMap<UnitId, Unit>,
    pub(super) order: &'a [UnitId],
    pub(super) key_fingerprints: &'a BTreeMap<Name, [u8; 32]>,
    pub(super) options: &'a ClosedRecheckOptions,
    /// Re-admit Clean-built families through `add_inductive` (see
    /// [`replay_family`]). False for the closed replay.
    pub(super) clean_families: bool,
}

/// What the loop measured besides refusals and admission stats.
pub(super) struct Driven {
    /// Extension keys that matched the table.
    pub(super) keys_bound: BTreeSet<String>,
    /// Units skipped because they were already given.
    pub(super) given_units: usize,
}

/// Make the kernel's quotient primitives available for a unit that carries
/// one of their names, or say why not.
///
/// They are never admitted from the cone: a family carrying one of their
/// names is refused, and a constant carrying one is compared (by
/// `replay_constant`) against the kernel-built primitive that
/// [`Environment::add_quot`] installs here — after checking, as Lean's
/// `add_quot` does, that the `Eq` their types name is the one they assume.
/// The planner orders every quotient unit after `Eq`.
fn provide_quotient(
    replay: &mut dyn ReplayTarget,
    unit_id: &UnitId,
    options: &ClosedRecheckOptions,
) -> Result<(), String> {
    if let UnitId::Family(head) = unit_id {
        return Err(format!(
            "inductive family {head} carries a kernel-reserved quotient name; the quotient \
             primitives are built by the kernel, never admitted from a cone"
        ));
    }
    if replay.env().quot_installed() {
        return Ok(());
    }
    if !options.install_quotient_primitives {
        return Err("this replay does not provide the quotient primitives".to_string());
    }
    replay
        .install_quot()
        .map_err(|e| format!("the quotient primitives cannot be installed: {e}"))
}

/// Replay `plan.order` into `replay`, in order, fail-closed.
///
/// A unit is refused (and every unit depending on it refused in turn) when a
/// dependency was refused, when `given` reports a conflict, when it carries a
/// quotient name and the quotient cannot be provided ([`provide_quotient`]),
/// when a member is
/// an extension key whose fingerprint the table does not pin, or when the
/// kernel's own admission path refuses it.
pub(super) fn replay_in_order(
    plan: &ReplayPlan<'_>,
    replay: &mut dyn ReplayTarget,
    unavailable: &mut BTreeMap<Name, String>,
    stats: &mut ReplayStats,
    refusals: &mut Vec<ClosedRecheckRefusal>,
    given: &dyn Fn(&Environment, &UnitId, &Unit) -> Given,
) -> Driven {
    let options = plan.options;
    let mut keys_bound: BTreeSet<String> = BTreeSet::new();
    let mut given_units = 0usize;
    for unit_id in plan.order {
        let Some(unit) = plan.units.get(unit_id) else {
            continue;
        };
        match given(replay.env(), unit_id, unit) {
            Given::Yes => {
                given_units += 1;
                continue;
            }
            Given::Conflict(detail) => {
                refusals.push(ClosedRecheckRefusal::BaseConflict {
                    name: unit_id.label(),
                    detail,
                });
                mark_unavailable(unavailable, unit, unit_id);
                continue;
            }
            Given::No => {}
        }
        if let Some(blocker) = unit.deps.iter().find_map(|d| unavailable.get(d).cloned()) {
            refusals.push(ClosedRecheckRefusal::DependencyRefused {
                name: unit_id.label(),
                blocked_by: blocker,
            });
            mark_unavailable(unavailable, unit, unit_id);
            continue;
        }
        let before = refusals.len();
        if let Some(quot) = unit
            .members
            .iter()
            .find(|m| clean_kernel::quot::is_quot_name(m))
        {
            if let Err(detail) = provide_quotient(replay, unit_id, options) {
                refusals.push(ClosedRecheckRefusal::QuotientPrecondition {
                    name: quot.to_string(),
                    detail,
                });
                mark_unavailable(unavailable, unit, unit_id);
                continue;
            }
        }
        for member in &unit.members {
            // A name the replay environment ALSO evaluates by a native reducer
            // (a consumer's base carries Clean's table; the closed replay's
            // carries none) is admitted like any other declaration. Until
            // 2026-09-27 the reducer fired on the name alone, so such a
            // declaration was refused here (`NativeReducerCollision`): the
            // kernel would have computed with the reducer and never consulted
            // it. Since the kernel's native-fold authority
            // (`clean-kernel/src/env/native_fold_authority.rs`), every
            // registered reducer fires only through
            // `TypeChecker::native_reducer_for`, which admits it only when the
            // head's δ-closure IN THIS REPLAY ENVIRONMENT has a canonical
            // digest — a definition reviewed as computing what the reducer
            // computes. So the admitted declaration either is such a
            // definition (the reducer and δ agree) or the reducer never fires
            // on it (δ is the only meaning); neither gives the name two
            // meanings. The refusal had become a refusal of Lean's own
            // `Init`: over the import prelude, every cone reaching `String` or
            // `autoParam` reached v4.30's `BitVec.ofFin` and was refused, 104
            // of `Mathlib/Order/Basic.lean`'s citations
            // (`reports/2026-09-28-extension-binding-v4-30.md`).
            let Some(found) = plan.key_fingerprints.get(member) else {
                continue;
            };
            match check_binding(&options.extension_bindings, member, found) {
                BindingVerdict::Bound => {
                    keys_bound.insert(member.to_string());
                }
                BindingVerdict::Mismatch { expected, found } => {
                    refusals.push(ClosedRecheckRefusal::ExtensionBindingMismatch {
                        name: member.to_string(),
                        hook: extension_hook(member).unwrap_or_default(),
                        table: options.extension_bindings.label().to_string(),
                        expected,
                        found,
                    });
                }
            }
        }
        if refusals.len() != before {
            mark_unavailable(unavailable, unit, unit_id);
            continue;
        }
        match unit_id {
            UnitId::Constant(name) => {
                replay_constant(plan.env, replay, name, stats, refusals);
            }
            UnitId::Family(head) => {
                replay_family(
                    plan.env,
                    plan.index,
                    replay,
                    head,
                    unit,
                    plan.clean_families,
                    stats,
                    refusals,
                );
            }
        }
        if refusals.len() != before {
            mark_unavailable(unavailable, unit, unit_id);
        }
    }
    Driven {
        keys_bound,
        given_units,
    }
}
