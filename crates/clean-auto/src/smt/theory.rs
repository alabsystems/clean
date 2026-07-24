// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Theory-facing SMT control-plane types and hooks.
//!
//! This module keeps the DPLL(T) theory interface separate from the term and
//! result data types in `types.rs`, which reduces merge pressure on the
//! frequently edited ay-alignment surface (#2386).

use super::types::{SmtTerm, TermId};
use crate::cdcl::Lit;
use std::any::Any;
use std::sync::Arc;

/// A theory literal - represents an atomic formula in a theory
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TheoryLiteral {
    /// Equality between two terms: t1 = t2
    Eq(TermId, TermId),
    /// Disequality: t1 ≠ t2
    Neq(TermId, TermId),
    /// Arithmetic: t1 < t2
    Lt(TermId, TermId),
    /// Arithmetic: t1 ≤ t2
    Le(TermId, TermId),
    /// Boolean variable (positive polarity)
    Bool(u32),
    /// Boolean variable (negative polarity)
    NegBool(u32),
}

impl TheoryLiteral {
    /// Negate this theory literal
    #[must_use]
    pub(crate) fn negate(&self) -> Self {
        match self {
            TheoryLiteral::Eq(a, b) => TheoryLiteral::Neq(*a, *b),
            TheoryLiteral::Neq(a, b) => TheoryLiteral::Eq(*a, *b),
            TheoryLiteral::Lt(a, b) => TheoryLiteral::Le(*b, *a), // ¬(a < b) ≡ b ≤ a
            TheoryLiteral::Le(a, b) => TheoryLiteral::Lt(*b, *a), // ¬(a ≤ b) ≡ b < a
            TheoryLiteral::Bool(v) => TheoryLiteral::NegBool(*v),
            TheoryLiteral::NegBool(v) => TheoryLiteral::Bool(*v),
        }
    }
}

/// Result of theory consistency check
#[derive(Clone, Debug)]
#[must_use = "theory check results affect SAT solver state"]
pub enum TheoryCheckResult {
    /// Theory is consistent with current assignment
    Consistent,
    /// Theory found a conflict - returns the conflicting literals
    Conflict(Vec<Lit>),
    /// Theory propagated new literals — each with explanation premises.
    /// Tuple: (propagated_lit, explanation_premises). The SAT solver adds
    /// the clause `NOT(p1) OR ... OR NOT(pn) OR propagated_lit` so the
    /// propagation becomes non-unit when premises are backtracked (#2309).
    #[allow(dead_code)]
    // ay API contract + test-constructed; waiver in .code_quality_waivers.toml
    Propagation(Vec<(Lit, Vec<Lit>)>),
    /// Theory cannot decide consistency (e.g., non-linear arithmetic,
    /// overflow, incomplete reasoning). Sound: avoids false Consistent
    /// claims. The DPLL(T) loop returns SmtResult::Unknown (#2384).
    Unknown,
}

/// Semantic lemma requests discovered by a theory during one SAT-model check.
///
/// The theory reports the request, but the SMT solver owns all fresh term
/// allocation and learned-clause insertion required to materialize it.
#[derive(Clone, Debug, PartialEq, Eq)]
#[must_use = "theory lemma requests must be materialized or discarded intentionally"]
pub enum TheoryLemmaRequest {
    /// Request the standard lazy array extensionality lemma:
    /// `lhs = rhs OR select(lhs, k) != select(rhs, k)` for a fresh witness `k`.
    ArrayExtensionality {
        lhs: TermId,
        rhs: TermId,
        diseq_reason: Lit,
    },
}

/// Trait for theory solvers in DPLL(T).
///
/// Each theory solver maintains internal state (equivalence classes, bounds,
/// equality/disequality sets) that must be consistent with the SAT solver's
/// current partial assignment. The [`push`](Self::push) and
/// [`backtrack`](Self::backtrack) methods manage incremental scoping so the
/// SAT solver can explore and retract search branches.
///
/// clean's production DPLL(T) loop now replays the CDCL SAT trail into
/// theories in trail order, calling [`push`](Self::push) when the SAT solver
/// enters a new decision level. After each SAT-model check, the solver tears
/// theories back down with [`reset`](Self::reset) to restore the
/// post-internalization baseline for the next attempt.
///
/// # Push/backtrack contract (ay#3686, ay#3736)
///
/// ## Behavioral equivalence invariant
///
/// After `push(); <mutations>; backtrack(level);`, the solver's observable
/// behavior (`check()`, `assert_literal()`) MUST be identical to the pre-push
/// state. "Identical" means: given the same sequence of future calls, the
/// solver produces the same results as if the pushed scope never existed.
///
/// ## Must restore on backtrack
///
/// These are scope-local effects that MUST be fully undone:
///
/// - **Asserted literals**: truncate assertion vectors or replay surviving
///   trail entries. Replay must be idempotent (no duplicate semantic effects).
/// - **Union-find / equivalence classes** (EqualityTheory): must reflect only
///   surviving assertions. clean rebuilds the E-graph from scratch (#2310).
/// - **Variable bounds** (ArithmeticTheory): bounds tightened by retracted
///   assertions restored via bound trail.
/// - **Per-atom state**: entries added in the retracted scope are removed;
///   overwritten entries are restored. Examples: `term_to_hypothesis`
///   (Equality), `term_to_var` (Arithmetic, #2312), tableau and assignment
///   snapshots (Arithmetic, #2296), index maps (Arrays, #2353).
///
/// ## Must clear on backtrack
///
/// These are derived state that becomes stale and MUST be cleared (re-derived
/// on the next `check()` / `assert_literal()`):
///
/// - **Pending propagation buffers**: `pending_deduced` (Equality, #2344),
///   `pending_equalities` / `pending_set` (Arrays, #2313),
///   and pending theory-lemma request queues.
/// - **Pending conflict state**: any conflict flags from the retracted scope.
/// - **Nelson-Oppen equality pair sets**: stale pairs prevent conflict
///   detection in alternate search branches (ay#3686, ay#3736).
///
/// ## May persist across backtrack
///
/// These are globally valid artifacts that do not depend on the assertion
/// set and MAY be retained for performance:
///
/// - Structural caches (term shapes, hash-cons, `func_decls`).
/// - Globally valid learned lemmas (managed by the SAT solver, not theories).
pub trait TheorySolver: Send + Sync {
    /// Called when a literal becomes true in the SAT solver.
    /// Returns propagated literals or a conflict.
    fn assert_literal(&mut self, lit: Lit, theory_lit: &TheoryLiteral) -> TheoryCheckResult;

    /// Check full consistency of the theory.
    fn check(&self) -> TheoryCheckResult;

    /// Backtrack to a given decision level, undoing all scope-local effects
    /// from levels above `level`.
    ///
    /// After this call, the solver's observable behavior MUST be identical to
    /// its state at the time of the matching [`push`](Self::push) for `level`.
    /// All assertions, equivalence class merges, bound changes, and per-atom
    /// state from retracted levels are undone. Derived state (pending
    /// propagations, equality pairs, conflict flags) is cleared.
    ///
    /// If `level >= self.level`, this is a no-op.
    ///
    /// See the [trait-level docs](TheorySolver) for the full contract.
    fn backtrack(&mut self, level: u32);

    /// Push a new decision level, saving a boundary marker so that all
    /// semantic effects after this call can be undone by [`backtrack`](Self::backtrack).
    ///
    /// Scopes nest: `push(); push(); backtrack(0);` restores to the state
    /// before the first `push()`. Each implementation records trail lengths
    /// or snapshots sufficient to undo one level of mutations.
    ///
    /// See the [trait-level docs](TheorySolver) for the full contract.
    #[allow(dead_code)] // ay API contract + test-used; waiver in .code_quality_waivers.toml
    fn push(&mut self);

    /// Get the name of this theory (for debugging)
    fn name(&self) -> &'static str;

    /// Set the terms used by this theory (for theories that need term structure).
    /// Terms are shared via `Arc<[SmtTerm]>` to avoid per-theory cloning (#2308).
    fn set_terms(&mut self, _terms: Arc<[SmtTerm]>);

    /// Pre-register a theory literal's terms with the theory solver (#2386).
    ///
    /// Called once per registered theory literal before the DPLL(T) solve loop,
    /// after [`set_terms`](Self::set_terms). Allows theories to eagerly build
    /// internal data structures (E-graph nodes, simplex variables) for all
    /// terms that may appear in assertions, removing lazy initialization from
    /// the hot [`assert_literal`](Self::assert_literal) path.
    ///
    /// Convergence with ay's `internalize_atom` trait method
    /// (`ay-core/src/theory.rs`). Must be idempotent: calling with the same
    /// literal multiple times has no additional effect.
    ///
    /// Default is a no-op — theories that don't benefit from pre-registration
    /// (e.g., ArrayTheory which analyzes terms in `set_terms`) can skip this.
    fn internalize_atom(&mut self, _theory_lit: &TheoryLiteral) {}

    /// Prepare theory-local pending equalities for the current model (#2366).
    ///
    /// Called immediately before `drain_deduced_equalities` in the generic
    /// propagation collector. Theories that need a computation step before
    /// draining (e.g., arithmetic model-equality detection) override this.
    /// Must be idempotent within one `check_theories_attributed` batch.
    ///
    /// Default is a no-op — theories that don't need preparation keep zero cost.
    fn prepare_deduced_equalities(&mut self) {}

    /// Drain deduced equalities for Nelson-Oppen theory combination (#2391).
    ///
    /// Returns pairs of equal terms with their explanation (SAT literals that
    /// justify the equality). Called by the generic propagation collector
    /// after `prepare_deduced_equalities` (#2366).
    ///
    /// Default returns empty — theories that don't produce deduced equalities
    /// (e.g., a future BV theory) need not override.
    fn drain_deduced_equalities(&mut self) -> Vec<(TermId, TermId, Vec<Lit>)> {
        Vec::new()
    }

    /// Drain semantic theory-lemma requests discovered in the current batch.
    ///
    /// The default returns no requests. The SMT solver owns fresh term
    /// allocation, learned-clause insertion, and any restart/resync behavior
    /// needed to materialize returned requests.
    fn drain_lemma_requests(&mut self) -> Vec<TheoryLemmaRequest> {
        Vec::new()
    }

    /// Reset theory state to its post-internalization baseline (#2386).
    ///
    /// Clears all assertion state, trail infrastructure, and pending buffers
    /// while preserving structural state from [`set_terms`](Self::set_terms)
    /// and [`internalize_atom`](Self::internalize_atom). After reset, the
    /// theory is in the same state as after the initial `set_terms` +
    /// `internalize_atom` sequence — ready for a fresh
    /// `push`/`assert_literal`/`check`/`backtrack` cycle.
    ///
    /// **WARNING:** The default delegates to [`backtrack`](Self::backtrack)`(0)`.
    /// That only removes scopes above level 0; it does **not** clear root-level
    /// assertions. Any theory with mutable assertion state **must** override
    /// `reset()` with explicit cleanup. The default is only correct for
    /// stateless/trivial theories.
    fn reset(&mut self) {
        self.backtrack(0);
    }

    /// Clear only per-attempt assertion state between SAT model iterations.
    ///
    /// The DPLL(T) loop calls this after checking the current SAT model and
    /// before the next SAT solve attempt. Implementations that have no
    /// learned/permanent theory state can inherit the default and reuse
    /// [`reset`](Self::reset). Theories that eventually preserve learned
    /// cuts or caches across SAT iterations can override this without changing
    /// the rest of the solver surface.
    ///
    /// Convergence with ay's `soft_reset()` trait method
    /// (`ay-core/src/theory.rs`).
    fn soft_reset(&mut self) {
        self.reset();
    }

    /// Assert a shared equality deduced by another theory (Nelson-Oppen) (#2386).
    ///
    /// Called during cross-theory forwarding when theory T1 deduces t1 = t2
    /// and the solver forwards it to theory T2. Unlike [`assert_literal`],
    /// which handles direct SAT-model assertions, this method explicitly
    /// identifies the equality as a cross-theory shared fact.
    ///
    /// Convergence with ay's `assert_shared_equality(lhs, rhs, reason)`
    /// (`ay-core/src/theory.rs`).
    ///
    /// Default delegates to [`assert_literal`] with `TheoryLiteral::Eq(t1, t2)`.
    ///
    /// [`assert_literal`]: Self::assert_literal
    fn assert_shared_equality(&mut self, t1: TermId, t2: TermId, reason: Lit) -> TheoryCheckResult {
        self.assert_literal(reason, &TheoryLiteral::Eq(t1, t2))
    }

    /// Assert a shared disequality deduced by another theory (Nelson-Oppen) (#2386).
    ///
    /// Symmetric counterpart to [`assert_shared_equality`] for forwarded
    /// disequalities. Called when the SAT solver negates a shared equality
    /// variable during cross-theory forwarding.
    ///
    /// Default delegates to [`assert_literal`] with `TheoryLiteral::Neq(t1, t2)`.
    ///
    /// [`assert_shared_equality`]: Self::assert_shared_equality
    /// [`assert_literal`]: Self::assert_literal
    fn assert_shared_disequality(
        &mut self,
        t1: TermId,
        t2: TermId,
        reason: Lit,
    ) -> TheoryCheckResult {
        self.assert_literal(reason, &TheoryLiteral::Neq(t1, t2))
    }

    /// Collect per-theory runtime statistics (#2386).
    ///
    /// Returns theory-prefixed key-value pairs for aggregation in
    /// [`SmtSolver::stats`](crate::smt::SmtSolver::stats), matching the
    /// remaining ay-style statistics tail hook.
    ///
    /// Default returns an empty list.
    #[allow(dead_code)] // ay API contract + test-used; waiver in .code_quality_waivers.toml
    fn collect_statistics(&self) -> Vec<(&'static str, u64)> {
        Vec::new()
    }

    /// Suggest a polarity for a registered theory atom from the current state.
    ///
    /// Called after a full theory check and before
    /// [`reset`](Self::reset), so implementations can reuse the live model /
    /// E-graph / bound state they already built for the current SAT attempt.
    /// The SMT solver applies only consensus hints: if multiple theories
    /// return conflicting polarities for the same shared atom, the hint is
    /// ignored rather than forcing an arbitrary choice.
    ///
    /// Returns `Some(true)` for the positive/base atom polarity,
    /// `Some(false)` for the negative polarity, or `None` when the theory has
    /// no useful guidance for this atom.
    ///
    /// Convergence with ay's `suggest_phase()` tail hook
    /// (`ay-core/src/theory.rs`), adapted to clean's `TheoryLiteral` atom
    /// representation instead of ay term IDs.
    fn suggest_phase(&self, _theory_lit: &TheoryLiteral) -> Option<bool> {
        None
    }

    /// Downcast support for accessing concrete theory implementations
    fn as_any(&self) -> &dyn Any;

    /// Mutable downcast support
    fn as_any_mut(&mut self) -> &mut dyn Any;
}

/// Level-aware adapter for theories participating in SAT-trail replay.
///
/// The SMT solver tracks one global SAT decision level while replaying the
/// current assignment into all theories. This trait lifts
/// [`TheorySolver::push`] and [`TheorySolver::backtrack`] into
/// level-targeted helpers so the solver can keep each theory aligned with the
/// current SAT level without open-coding the push/pop loops everywhere.
pub(crate) trait LeveledTheoryState: TheorySolver {
    /// Advance from `current_level` to `target_level` by pushing one scope per
    /// SAT decision level.
    fn push_to_level(&mut self, current_level: u32, target_level: u32) {
        for _ in current_level..target_level {
            self.push();
        }
    }

    /// Retract all scopes above `target_level`.
    fn pop_to_level(&mut self, current_level: u32, target_level: u32) {
        if target_level < current_level {
            self.backtrack(target_level);
        }
    }
}

impl<T: TheorySolver + ?Sized> LeveledTheoryState for T {}
