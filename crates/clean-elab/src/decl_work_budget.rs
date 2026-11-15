// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The elaborator's side of the declaration-scoped automation work budget.
//!
//! The budget itself lives in `clean-auto` (`work_budget.rs` there carries the
//! measured motivation and the Lean function it ports, `maxHeartbeats` /
//! `Lean.Core.checkMaxHeartbeatsCore`), because the superposition loop that
//! spent 1,421 s of `Mathlib/Logic/Function/Basic.lean` lives there. This
//! module owns the two things only the elaborator can do:
//!
//! * **Refill it once per declaration.** Lean's heartbeat window is one
//!   command (`Lean.Elab.Command.runCore`, `src/lean/Lean/Elab/Command.lean`,
//!   sets `initHeartbeats` from `IO.getNumHeartbeats` as it lifts each
//!   command into `CoreM`), and a `section`/`namespace` member is its own
//!   command. The refill point
//!   is therefore the same OUTERMOST non-container entry the per-declaration
//!   timing record uses ([`crate::decl_timing`]): a container never refills
//!   (its members do), and a call nested inside a declaration (a desugaring
//!   that splits one declaration in several, a `mutual` block's members)
//!   shares the declaration's pot.
//! * **Name it in the failure it causes.** Exhausting the budget makes every
//!   CHARGED automation site of the declaration give up at its next charge
//!   (the prover reports `ResourceLimit`, `simp` trips its traversal budget,
//!   `grind` fails; a tactic that reaches no charge site is not bounded), so
//!   the error that reaches the declaration boundary is whatever the tactic
//!   script failed with afterwards — typically `grind: no progress`. When the
//!   latch is set, that error is wrapped in
//!   [`ElabError::AutomationBudgetExhausted`], the analogue of Lean's
//!   `throwMaxHeartbeat` "(deterministic) timeout … maximum number of
//!   heartbeats" message, so a reader can tell "the search ran out" from "the
//!   search finished and found nothing".
//!
//! One divergence from Lean is deliberate and documented rather than hidden:
//! Lean's heartbeat exception is a RUNTIME exception that `first`/`try` do not
//! catch, so a declaration that exhausts `maxHeartbeats` always FAILS. Here a
//! tactic combinator can still fall through to a non-automation alternative
//! after the automation gave up, and if that alternative closes the goal the
//! declaration PASSES with a kernel-checked proof. That can only accept a
//! proof the kernel accepted, never fabricate one, and the default budget is
//! chosen (by measurement over the pinned slice) so that no passing
//! declaration comes near it.

use std::cell::Cell;

use clean_parser::SurfaceDecl;

use crate::ElabError;

thread_local! {
    /// An outermost declaration scope is open on this thread.
    static ACTIVE: Cell<bool> = const { Cell::new(false) };
}

/// The detail string every automation site reports when the declaration's
/// budget is spent: the limit, the site whose charge found it spent, and the
/// knob. Shared so `simp`, `grind` and the declaration-level error say the
/// same thing.
#[must_use]
pub(crate) fn exhausted_detail() -> String {
    let limit = clean_auto::automation_budget_limit();
    let site = clean_auto::automation_budget_exhausted_at().unwrap_or("automation");
    format!(
        "the declaration spent its whole automation work budget ({limit} units, \
         exhausted in `{site}`); raise it with `--automation-budget <n>`, or 0 \
         for unlimited"
    )
}

/// Charge one unit of `site` work (a `grind` core step or closer attempt) to
/// the declaration's automation budget. `false` means the budget is spent and
/// the caller must give up.
#[must_use]
pub(crate) fn charge(site: &'static str) -> bool {
    clean_auto::charge_automation_work(site, 1)
}

/// Opened at the elaborator's per-declaration entry; refills the automation
/// budget when it is the OUTERMOST non-container declaration, and is inert
/// otherwise.
pub(crate) struct LeafWorkScope {
    armed: bool,
}

impl LeafWorkScope {
    pub(crate) fn enter(decl: &SurfaceDecl) -> Self {
        if crate::decl_timing::is_container(decl) || ACTIVE.with(Cell::get) {
            return Self { armed: false };
        }
        ACTIVE.with(|active| active.set(true));
        clean_auto::begin_automation_declaration();
        Self { armed: true }
    }

    /// Pass `result` through, naming the budget in a failure it left behind.
    ///
    /// A success is returned unchanged even when the budget ran out along the
    /// way (see the module doc for why that is the safe direction), and a
    /// nested scope never rewrites anything: the outermost one does, once.
    pub(crate) fn finish<T>(&self, result: Result<T, ElabError>) -> Result<T, ElabError> {
        if !self.armed {
            return result;
        }
        match result {
            Err(underlying) => match clean_auto::automation_budget_exhausted_at() {
                Some(site) => Err(ElabError::AutomationBudgetExhausted {
                    limit: clean_auto::automation_budget_limit(),
                    site: site.to_owned(),
                    underlying: Box::new(underlying),
                }),
                None => Err(underlying),
            },
            ok => ok,
        }
    }
}

impl Drop for LeafWorkScope {
    fn drop(&mut self) {
        if self.armed {
            ACTIVE.with(|active| active.set(false));
        }
    }
}
