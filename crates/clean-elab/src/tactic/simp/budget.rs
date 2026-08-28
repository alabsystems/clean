// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The growth/work budget for **one** `simp_expr` traversal.
//!
//! # Why this exists
//!
//! `simp` has had a growth budget since the `import Init` stack overflow: the
//! main loop in [`super::simp`] compares the size of each step's result against
//! `nodes(target) * 32` and stops when a step balloons the term. That check is
//! consulted **between** top-level steps, so it can only see a runaway that
//! returns. Measured on the `section ite` slice of `Mathlib/Logic/Basic.lean`
//! (`dite_apply`, `apply_dite₂`, `dite_eq_or_eq`), the runaway does **not**
//! return: it lives inside a *single* `simp_expr` traversal, which recurses
//! into subterms, rewrites them larger, and pays a `whnf`/`instantiate` per
//! candidate lemma at every node of the term it is growing. A 3-second
//! `sample(1)` of that check caught `instantiate_inner` **20,129 frames deep**
//! under
//!
//! ```text
//! simp_expr -> try_apply_simp_lemma_with_proof -> reduce_op_projection_head
//!           -> whnf -> MetaState::instantiate -> instantiate_inner
//! ```
//!
//! with `simp_expr` self-recursing above it. The between-steps check never got
//! a turn; one such `clean check` burned 9.95 CPU-hours and wedged the
//! source-elaboration gate.
//!
//! So the budget has to be consulted **inside** the traversal. This type is
//! that budget: one object per traversal, shared by every frame of the
//! recursion (including the re-entrant ones — `try_simp_ite`'s condition simp
//! and the conditional-lemma discharger's recursive simp), charging
//!
//! * **fuel** — one unit per `simp_expr` frame, so an expensive-per-node
//!   traversal cannot run forever even when nothing grows, and
//! * **size** — the node count of every expression a frame *produces*, so a
//!   rewrite that balloons its subterm is caught where it happens rather than
//!   after the whole traversal has paid for it.
//!
//! # Failing is the point
//!
//! Exceeding the budget is an honest tactic **failure**, never a wrong proof
//! and never a silent partial rewrite. A trip is *sticky*: once set, every
//! enclosing `simp_expr` frame unwinds to `SimpResult::refl` of its own input
//! (see `super::expr::simp_expr_budgeted`), so the traversal's result is the
//! ORIGINAL term with no proof attached, and the caller turns that into
//! [`crate::tactic::TacticError::BudgetExceeded`] with the goal untouched. The
//! kernel therefore never sees a term this tactic could not justify — the same
//! discipline the discharger already uses when it cannot close a side
//! condition.
//!
//! # The ceiling is not lowered
//!
//! `max_nodes` reproduces the existing between-steps formula EXACTLY
//! (`nodes(target) * 32`, floor 4096) so that moving the check inward does not
//! also tighten it; a budget tight enough to refuse legitimate rewrites would
//! be a regression wearing a fix's clothes. The only addition is
//! [`NODE_CEILING`], an absolute clamp that also bounds the *measurement* of
//! the initial target (the old formula counted it with `usize::MAX` as the cap,
//! which is itself unbounded on a share-heavy term).

use std::cell::Cell;
use std::sync::OnceLock;

use clean_kernel::Expr;

use super::expr_node_count_capped;

/// Multiplier applied to the initial target's node count to get the largest
/// intermediate term a traversal may produce. Matches the historical
/// between-steps growth budget.
const NODE_GROWTH_FACTOR: usize = 32;

/// Floor for `max_nodes`, so a tiny goal still gets room to expand. Matches the
/// historical between-steps growth budget.
const NODE_FLOOR: usize = 4096;

/// Absolute clamp on `max_nodes`, and the cap used when measuring the initial
/// target. 4,194,304 nodes is far beyond any legitimate goal (the pinned
/// source-elaboration slice never approaches it) and bounds the cost of the
/// measurement itself on a share-heavy term whose tree unfolding is
/// exponential in its representation.
const NODE_CEILING: usize = 1 << 22;

/// Fuel per traversal, per node of the initial target. A legitimate traversal
/// visits roughly one frame per node, plus the re-entrant frames spent on
/// `ite` conditions and discharged side conditions, so 64x leaves ample room.
const FUEL_PER_NODE: u64 = 64;

/// Floor for fuel: small targets are dominated by re-entrant discharge work,
/// not by their own node count.
const FUEL_FLOOR: u64 = 1 << 16;

/// Absolute clamp on fuel.
const FUEL_CEILING: u64 = 1 << 26;

/// Why a budget tripped.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BudgetTrip {
    /// The traversal visited more `simp_expr` frames than it was given.
    Fuel,
    /// A frame produced a term larger than `max_nodes`.
    Size,
}

/// The work/growth budget for one `simp_expr` traversal.
///
/// Not `Sync` by construction (`Cell`): a traversal is single-threaded, and a
/// budget shared across threads would report a trip that belongs to another
/// goal.
#[derive(Debug)]
pub(crate) struct SimpBudget {
    /// Remaining `simp_expr` frames. Saturating at 0 sets [`Self::trip`].
    fuel: Cell<u64>,
    /// What [`Self::refuel`] resets `fuel` to.
    initial_fuel: u64,
    /// Largest node count any single produced term may have.
    max_nodes: usize,
    /// Sticky trip reason. Once `Some`, the traversal is over.
    trip: Cell<Option<BudgetTrip>>,
}

impl SimpBudget {
    /// The budget a traversal of `target` gets.
    ///
    /// ENSURES: `max_nodes >= NODE_FLOOR` and `max_nodes <= NODE_CEILING`.
    /// ENSURES: the returned budget has not tripped.
    pub(crate) fn for_target(target: &Expr) -> Self {
        let nodes = expr_node_count_capped(target, NODE_CEILING);
        let max_nodes = nodes
            .saturating_mul(NODE_GROWTH_FACTOR)
            .clamp(NODE_FLOOR, NODE_CEILING);
        let fuel = (nodes as u64)
            .saturating_mul(FUEL_PER_NODE)
            .clamp(FUEL_FLOOR, FUEL_CEILING);
        Self::with_limits(
            env_fuel().unwrap_or(fuel),
            env_max_nodes().unwrap_or(max_nodes),
        )
    }

    /// A budget with explicit limits. Used by the refusal fixtures, which need
    /// a trip to be reachable without a pathological goal.
    pub(crate) fn with_limits(fuel: u64, max_nodes: usize) -> Self {
        SimpBudget {
            fuel: Cell::new(fuel),
            initial_fuel: fuel,
            max_nodes,
            trip: Cell::new(None),
        }
    }

    /// A budget that never trips. Test-only: it is what a fixture uses when it
    /// is measuring something OTHER than the budget, and production must not
    /// grow a way to opt out of the guard.
    #[cfg(test)]
    pub(crate) fn unlimited() -> Self {
        Self::with_limits(u64::MAX, usize::MAX)
    }

    /// Charge one `simp_expr` frame.
    ///
    /// ENSURES: returns `false` iff the budget has tripped (now or earlier), in
    ///   which case the caller must not do any further work.
    pub(crate) fn tick(&self) -> bool {
        if self.trip.get().is_some() {
            return false;
        }
        match self.fuel.get().checked_sub(1) {
            Some(remaining) => {
                self.fuel.set(remaining);
                true
            }
            None => {
                self.trip.set(Some(BudgetTrip::Fuel));
                false
            }
        }
    }

    /// Check a produced term against the size limit.
    ///
    /// ENSURES: returns `false` iff `produced` has at least `max_nodes` nodes
    ///   (or the budget had already tripped), and in that case the budget is
    ///   tripped, so the whole traversal unwinds.
    pub(crate) fn admit(&self, produced: &Expr) -> bool {
        if self.trip.get().is_some() {
            return false;
        }
        if self.max_nodes == usize::MAX {
            return true;
        }
        if expr_node_count_capped(produced, self.max_nodes) >= self.max_nodes {
            self.trip.set(Some(BudgetTrip::Size));
            return false;
        }
        true
    }

    /// Reset the fuel for the next top-level step. A tripped budget stays
    /// tripped: refuelling it would hide the failure the caller must report.
    pub(crate) fn refuel(&self) {
        if self.trip.get().is_none() {
            self.fuel.set(self.initial_fuel);
        }
    }

    /// Has this traversal exceeded its budget?
    pub(crate) fn is_tripped(&self) -> bool {
        self.trip.get().is_some()
    }

    /// The trip reason, if any. Test-only: production reads [`Self::detail`],
    /// which is the reportable form.
    #[cfg(test)]
    pub(crate) fn trip_reason(&self) -> Option<BudgetTrip> {
        self.trip.get()
    }

    /// Human-readable trip detail for [`crate::tactic::TacticError::BudgetExceeded`].
    /// Returns `None` when the budget has not tripped.
    pub(crate) fn detail(&self) -> Option<String> {
        match self.trip.get()? {
            BudgetTrip::Fuel => Some(format!(
                "one simplification traversal spent all {} of its frames without finishing; \
                 the goal is left unchanged",
                self.initial_fuel
            )),
            BudgetTrip::Size => Some(format!(
                "a rewrite grew the term past {} nodes in a single traversal; \
                 the goal is left unchanged",
                self.max_nodes
            )),
        }
    }
}

/// `CLEAN_SIMP_FUEL` — override the per-traversal frame budget. Present so the
/// ceiling can be *measured* (raise it and re-measure the battery) rather than
/// argued about, and so the gate can pin it.
fn env_fuel() -> Option<u64> {
    static FUEL: OnceLock<Option<u64>> = OnceLock::new();
    *FUEL.get_or_init(|| {
        std::env::var("CLEAN_SIMP_FUEL")
            .ok()
            .and_then(|v| v.parse::<u64>().ok())
    })
}

/// `CLEAN_SIMP_MAX_NODES` — override the per-traversal size limit.
fn env_max_nodes() -> Option<usize> {
    static MAX_NODES: OnceLock<Option<usize>> = OnceLock::new();
    *MAX_NODES.get_or_init(|| {
        std::env::var("CLEAN_SIMP_MAX_NODES")
            .ok()
            .and_then(|v| v.parse::<usize>().ok())
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::name::Name;

    fn atom() -> Expr {
        Expr::const_(Name::from_string("Nat"), vec![])
    }

    #[test]
    fn test_budget_fuel_trips_after_its_frames_are_spent() {
        let budget = SimpBudget::with_limits(2, usize::MAX);
        assert!(budget.tick(), "first frame is within budget");
        assert!(budget.tick(), "second frame is within budget");
        assert!(!budget.tick(), "third frame must be refused");
        assert_eq!(budget.trip_reason(), Some(BudgetTrip::Fuel));
        assert!(budget.detail().is_some(), "a trip must carry a report");
    }

    #[test]
    fn test_budget_trip_is_sticky_and_refuel_cannot_clear_it() {
        let budget = SimpBudget::with_limits(1, usize::MAX);
        assert!(budget.tick());
        assert!(!budget.tick());
        budget.refuel();
        assert!(
            !budget.tick(),
            "refuel must not resurrect a tripped traversal"
        );
        assert_eq!(budget.trip_reason(), Some(BudgetTrip::Fuel));
    }

    #[test]
    fn test_budget_refuel_restores_an_untripped_budget() {
        let budget = SimpBudget::with_limits(2, usize::MAX);
        assert!(budget.tick());
        budget.refuel();
        assert!(budget.tick());
        assert!(budget.tick(), "refuel restored the full allowance");
        assert!(!budget.tick());
    }

    #[test]
    fn test_budget_size_trips_on_an_oversized_term() {
        let budget = SimpBudget::with_limits(u64::MAX, 3);
        assert!(budget.admit(&atom()), "a single node fits under 3");
        let big = Expr::app(Expr::app(atom(), atom()), atom());
        assert!(!budget.admit(&big), "5 nodes must be refused at limit 3");
        assert_eq!(budget.trip_reason(), Some(BudgetTrip::Size));
        assert!(!budget.tick(), "a size trip stops the traversal too");
    }

    #[test]
    fn test_budget_unlimited_never_trips() {
        let budget = SimpBudget::unlimited();
        for _ in 0..10_000 {
            assert!(budget.tick());
        }
        let big = Expr::app(Expr::app(atom(), atom()), atom());
        assert!(budget.admit(&big));
        assert!(!budget.is_tripped());
        assert_eq!(budget.detail(), None);
    }

    #[test]
    fn test_budget_for_target_respects_floor_and_ceiling() {
        let budget = SimpBudget::for_target(&atom());
        // A one-node target still gets the floor, never `32`.
        assert!(
            budget.max_nodes >= NODE_FLOOR,
            "max_nodes {} below floor",
            budget.max_nodes
        );
        assert!(budget.max_nodes <= NODE_CEILING);
        assert!(budget.initial_fuel >= FUEL_FLOOR);
        assert!(!budget.is_tripped());
    }
}
