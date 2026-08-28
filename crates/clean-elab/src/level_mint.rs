// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! U2 stage 3 — the level-mint registry.
//!
//! (`docs/analysis/u2-implementation-plan-2026-08-24.md` §3 stage 3, the
//! rung-1 remainder of `designs/2026-08-08-u2-universe-polymorphism-ladder.md`
//! and brick U1 of `docs/plans/UNIVERSE_LEVER_DESIGN_2026-07-12.md`.)
//!
//! # The defect this closes
//!
//! Level identity in the elaborator is the `u_N` STRING: there is no
//! `LevelMVarId`, the union-find is `Name`-keyed
//! (`MetaState::add_level_constraint`), and rigid-vs-assignable is a side set
//! (`MetaState::rigid_level_params`). Two independent counters therefore mean
//! two independent name spaces that ALIAS, and the elaborator ran exactly
//! that: `ElabCtx::next_universe` and `ProofState::next_universe` were
//! separate `u64` fields.
//!
//! U2 stage 1 (2026-08-25) seeded the ProofState's counter from the ElabCtx's
//! at the bridge ENTRY and raised the ElabCtx's past the ProofState's at the
//! bridge EXIT. That closes the aliasing across a whole tactic block, but not
//! WITHIN one: a tactic step elaborates its term arguments through the ELABCTX
//! (`elaborate_exact_term`, `elaborate_refine_term`, `have`/`rw` term
//! arguments — every polymorphic head constant mints one level per declared
//! level param in `elab_app`) and mints its lemma instances on the PROOFSTATE
//! (`ProofState::mk_const`, `resolve_env_rewrite_equation`). Between entry and
//! exit the two counters both start at the seed value `N`, so the first
//! mid-block mint on each side is the same string `u_N`.
//!
//! MEASURED, not inferred (2026-08-25, this box, builtin prelude, no Mathlib,
//! `CLEAN_U2_MINT_TRACE=1` plus a scratch double-mint report): of eight tactic
//! scripts over a `.{u}`-polymorphic `pid`/`pid_eq` pair, SEVEN double-minted
//! `u_3`, and in each of the seven the two authorities held DIFFERENT values
//! for that one name at the bridge exit — `elabctx=S(0) proofstate=u` (×5),
//! `elabctx=S(0) proofstate=v`, and `elabctx=u_3 proofstate=S(0)` (the
//! ElabCtx's still ABSTRACT, awaiting generalization at declaration close,
//! against a concrete tactic-side solve — the silent-monomorphization
//! direction). The bridge exit's `ps.metas.instantiate_levels(&proof)` runs
//! immediately after that point and realizes the ProofState's value into
//! every occurrence of the name, the ElabCtx's included. With the shared
//! counter the same run reports ZERO double-minted names. The five shapes are
//! `tests/fixtures/universes/p45_bridge_mint_registry.lean`; the identity
//! property is pinned in `infer::tests::tactic_bridge_levels`.
//!
//! Two faces had nothing to do with the ElabCtx at all and are closed by the
//! same handle: `create_sub_proof_state` COPIED the counter, so a
//! `have h : T := by …` sub-state and its parent aliased into ONE spliced
//! proof term; and the decreasing-goal bridge entry
//! (`wf_recursion::decreasing::try_tactic_on_goal`) had no copy-back at all,
//! so after such a block the ElabCtx could re-mint names it had already used.
//!
//! No verdict flipped at HEAD, and that is an accident rather than a defence:
//! every ElabCtx→ProofState handoff eagerly `instantiate_levels` what it hands
//! over, so an already-SOLVED ElabCtx level is substituted away before it can
//! be conflated. Unsolved ones pass through unchanged
//! (`adopt_residual_elab_metas`, `elaborate_refine_term`'s pending-goal
//! types), which is the surviving exposure. Soundness posture is unchanged
//! throughout — `verify_tactic_proof` and the mandatory decl-close kernel
//! re-check stand behind every accepted proof, so a conflation is a LOUD
//! reject or a wrong monomorphization, never an unsound accept.
//!
//! # The fix, and why this shape
//!
//! One monotone counter, shared by handle. Both minting authorities draw ids
//! from the same cell, so no two mints can ever produce the same name — the
//! identity guarantee is STRUCTURAL (a counter that never repeats) instead of
//! CONVENTIONAL (two counters a human must keep in sync at the right
//! boundaries). It is the smallest change that makes the class unreachable:
//! step-boundary re-synchronisation would leave the intra-step window open,
//! because a single compound tactic interleaves ElabCtx and ProofState mints
//! several times.
//!
//! This does NOT make level identity a first-class `LevelMVarId` — the union
//! find is still `Name`-keyed. It removes the one way two mints could end up
//! with the same name. See the plan's stage-3 section for the remaining
//! rung-1 items.
//!
//! AMENDED 2026-08-26 (U2 stage-3 deferral 1,
//! `docs/analysis/u2-stage3-deferrals-2026-08-26.md`). Two corrections to the
//! paragraph above. First, "the legacy `level_constraints` map is still
//! written" is no longer true — that map was verified dead and REMOVED the
//! same day (deferral 2). Second, and more important: a shared counter closes
//! MINT-vs-MINT aliasing, and there is a second door it does not reach —
//! a mint aliasing a USER-WRITTEN name. `def badAutoCollide (β : Sort _) :
//! Sort u_0 := Nat` was accepted and silently monomorphized because the
//! auto-bind path read `universe_params` (the union of the rigid names and
//! these mints) as a rigidity proxy. Closed by
//! [`crate::level_role::LevelParamRole`]; the mint namespace remains
//! user-writable, which is the residue named in that module.
//!
//! AMENDED 2026-08-26b — THE RESIDUE IS CLOSED. The mint namespace is no
//! longer user-writable. See [`MINT_PREFIX`] below and `crate::level_role`'s
//! §"the residue" for the measurement; the short version is that the two
//! populations now live in DISJOINT spellings, so "a mint aliasing a
//! user-written name" is unreachable by construction rather than resolved
//! after the fact.
//!
//! `Arc<AtomicU64>` rather than `Rc<Cell<u64>>`: `ProofState` is `Send`
//! (it carries a `std::sync::Mutex` type-checker cache) and must stay so.

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

/// The RESERVED spelling every universe-level METAVARIABLE is minted into
/// (U2 stage-3 deferral 1 follow-up, 2026-08-26b).
///
/// # Why a prefix the surface cannot lex
///
/// Level identity in the elaborator is the `Name`, so two levels that share a
/// spelling ARE one level. Until this prefix landed, mints were spelled `u_0`,
/// `u_1`, … — names a user may also write — and every consequence of that
/// followed: a written `u_0` colliding with a mint was first silently
/// monomorphized (the p47 defect), then, once
/// [`crate::level_role::LevelParamRole`] made the classification total,
/// loudly REFUSED where Lean accepts (the p49 cost). Both faces are the same
/// root cause, and neither is a solver bug: it is one namespace serving two
/// populations that must never meet.
///
/// `?` is not an identifier-start character (`clean_parser`'s
/// `is_ident_start`), so `Sort ?u_0` cannot lex as a level parameter — the
/// surface grammar has no production for a name in this space. It matches the
/// sigil Clean already prints for term metavariables (`?m.1`) and Lean prints
/// for level ones (`?u.1`), so an unsolved mint that reaches a diagnostic now
/// READS as the metavariable it is instead of impersonating a declared
/// parameter.
///
/// # The one door that is not the lexer's, and how it is shut
///
/// Guillemet identifiers (`«…»`) pass their contents through verbatim, and
/// `Sort «my?weird»` does elaborate (measured 2026-08-26 on the release binary
/// at `2ce2cf2c1`: `1 passed, 0 failed`). So `«?u_0»` would otherwise be a way
/// back into the mint namespace. `ElabCtx::elab_level` refuses any WRITTEN
/// universe name in this space outright — see [`is_reserved_level_name`] —
/// which is what makes "the user literally cannot write one" a checked
/// statement rather than a lexer accident.
///
/// The guard is on BOTH productions that turn a written identifier into a
/// `Level::Param`: the ordinary `LevelExpr::Param` arm and the antiquotation
/// arm (`$«?u_0»`, which does not pass through the first). Total over the
/// level grammar, not total over one of its productions.
///
/// One route is deliberately NOT guarded, because it cannot do harm and
/// guarding it would mean reaching outside the level grammar: a declaration's
/// own `.{…}` list (`def f.{«?u_0»}`) installs its names through
/// `set_decl_universe_params` without elaborating a level expression. Such a
/// parameter is declared RIGID and is therefore skipped by the mint's skip
/// loop — which is why that loop is kept even though ordinary elaboration can
/// no longer reach it — so it can still never alias a mint. And it can never
/// be USED: every use site is a level expression and is refused by the guard
/// above. Measured 2026-08-26b: `def declaredReserved.{«?u_0»} (a : Nat) :
/// Nat := a` plus a call site is `2 passed, 0 failed` (the parameter is
/// unused, so it is dropped at declaration close and the registered arity is
/// zero), while `def declaredUsed.{«?u_0»} (α : Sort «?u_0») (a : α) : α := a`
/// is refused with `ReservedUniverseName`. So a reserved name can be
/// declared-and-unused; it can never be written into a level.
///
/// # What the user still sees
///
/// A mint that survives to declaration close is renamed out of this space by
/// `ElabCtx::finalize_level_params` — the `levelMVarToParam` boundary — through
/// [`LevelMint::next_generalized_name`], which draws from this same counter but
/// spells `u_N`. Sharing the counter is what makes the registered names
/// byte-identical rather than merely similar: `def holeOnly (β : Sort _)
/// (x : β) : β := x` kept `u_1` at `2ce2cf2c1` and keeps `u_1` here.
///
/// What that argument covers is the `finalize_level_params` path (definitions,
/// theorems, axioms, opaques). Inductive and structure elaboration collects
/// `level_params` straight off the finished expressions with no rename step, so
/// a reserved name COULD in principle reach one of those interfaces. Measured
/// rather than assumed: checking all 127 `.lean` files under `tests/fixtures/`
/// and `demos/` with `--prelude builtin` surfaced a reserved spelling in
/// seven — six diagnostics quoting an UNSOLVED metavariable, plus p51 itself,
/// which writes one on purpose — and in ZERO registered declarations. An
/// unsolved metavariable is exactly the case where the old `u_N` spelling was
/// a lie, since it read as a parameter the author could have named.
pub(crate) const MINT_PREFIX: &str = "?u_";

/// Whether `name` inhabits the reserved metavariable namespace, i.e. whether a
/// user who WROTE it is reaching into [`MINT_PREFIX`].
///
/// Deliberately broader than the prefix itself: `?` leads Clean's whole
/// metavariable-display space, no surface identifier can begin with it, and a
/// declaration that smuggles one in through `«…»` should be refused whichever
/// sub-space it aimed at rather than only the one the mint happens to use
/// today.
pub(crate) fn is_reserved_level_name(name: &str) -> bool {
    name.starts_with('?')
}

/// A shared, monotone source of universe-level parameter ids.
///
/// Cloning a `LevelMint` clones the HANDLE, not the counter: every clone draws
/// from the same cell. That is the whole point — see the module docs.
#[derive(Debug, Clone)]
pub(crate) struct LevelMint(Arc<AtomicU64>);

impl LevelMint {
    /// A brand-new, independent counter starting at 0.
    ///
    /// Use this only where a minting authority genuinely stands alone (a
    /// declaration's `ElabCtx`, a `ProofState` opened outside the elaborator).
    /// Anything that mints alongside an existing authority must take that
    /// authority's handle instead — see [`ProofState::seed_universe_world`].
    ///
    /// [`ProofState::seed_universe_world`]: crate::tactic::ProofState::seed_universe_world
    pub(crate) fn new() -> Self {
        Self(Arc::new(AtomicU64::new(0)))
    }

    /// Reserve and return the next id. Never returns the same id twice, for
    /// any handle on the same counter.
    pub(crate) fn next_id(&self) -> u64 {
        self.0.fetch_add(1, Ordering::Relaxed)
    }

    /// Reserve the next id and spell it as a universe METAVARIABLE name, in
    /// the reserved [`MINT_PREFIX`] space no surface identifier can reach.
    ///
    /// This is the name every `Type _` / `Sort _` hole and every implicit
    /// level of an applied polymorphic constant is born with.
    pub(crate) fn next_name(&self) -> String {
        format!("{MINT_PREFIX}{}", self.next_id())
    }

    /// Reserve the next id and spell it as a USER-FACING parameter name.
    ///
    /// The counterpart of [`Self::next_name`], and the only minting entry
    /// point allowed to produce a writable spelling: it names a level that has
    /// stopped being a metavariable, i.e. one that survived to declaration
    /// close and is being generalized into the declaration's interface
    /// (`ElabCtx::finalize_level_params`, Lean's `levelMVarToParam`).
    ///
    /// Both spellings draw from the SAME counter, which is what keeps the
    /// registered names byte-identical to the pre-reservation elaborator: a
    /// declaration whose hole took id 0 and whose generalization took id 1
    /// registered `u_1` before and registers `u_1` now.
    ///
    /// A caller must still reject a candidate that the declaration's own
    /// `universe_params` already holds — a user may legitimately have written
    /// `u_1` — exactly as the mint's skip loop always did.
    pub(crate) fn next_generalized_name(&self) -> String {
        format!("u_{}", self.next_id())
    }

    /// The id the next mint would take, without reserving it. Diagnostics and
    /// tests only — a caller that acts on this value has a race by
    /// construction.
    #[cfg(test)]
    pub(crate) fn peek(&self) -> u64 {
        self.0.load(Ordering::Relaxed)
    }

    /// True iff `self` and `other` are handles on the SAME counter, i.e. their
    /// mints cannot alias.
    pub(crate) fn shares_counter_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl Default for LevelMint {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::LevelMint;

    /// The defining property: a cloned handle shares the counter, so ids drawn
    /// through either handle are globally distinct.
    #[test]
    fn test_level_mint_cloned_handle_shares_counter_ids_never_repeat() {
        let a = LevelMint::new();
        let b = a.clone();
        assert!(a.shares_counter_with(&b));
        let ids = [a.next_id(), b.next_id(), a.next_id(), b.next_id()];
        assert_eq!(
            ids,
            [0, 1, 2, 3],
            "shared counter must be strictly monotone"
        );
        assert_eq!(a.peek(), 4);
        assert_eq!(b.peek(), 4);
    }

    /// Two independently-constructed mints are exactly what stage 3 forbids at
    /// the bridge: they DO collide. `LevelMint::new` is therefore only correct
    /// where the authority genuinely stands alone.
    #[test]
    fn test_level_mint_independent_counters_do_collide() {
        let a = LevelMint::new();
        let b = LevelMint::new();
        assert!(!a.shares_counter_with(&b));
        assert_eq!(a.next_id(), b.next_id());
    }

    /// THE RESERVATION. Every metavariable spelling is in the reserved space
    /// and every generalized spelling is out of it — the disjointness that
    /// makes a mint/user-name collision unreachable rather than resolved.
    #[test]
    fn test_mint_names_are_reserved_and_generalized_names_are_not() {
        let m = LevelMint::new();
        let minted = m.next_name();
        assert_eq!(minted, "?u_0");
        assert!(
            super::is_reserved_level_name(&minted),
            "a metavariable spelling must be unwritable: {minted}"
        );
        let generalized = m.next_generalized_name();
        assert_eq!(
            generalized, "u_1",
            "both spellings draw from ONE counter — that is what keeps registered \
             names byte-identical to the pre-reservation elaborator"
        );
        assert!(
            !super::is_reserved_level_name(&generalized),
            "a generalized parameter is part of the declaration's interface and \
             must be a name a user can write: {generalized}"
        );
    }

    /// The reservation predicate is about the `?` SPACE, not about the mint's
    /// current sub-spelling: a smuggled `«?anything»` is refused too, so a
    /// later change to `MINT_PREFIX` cannot silently re-open the door.
    #[test]
    fn test_reserved_level_name_covers_the_whole_question_mark_space() {
        assert!(super::is_reserved_level_name("?u_0"));
        assert!(super::is_reserved_level_name("?m"));
        assert!(super::is_reserved_level_name("?"));
        assert!(!super::is_reserved_level_name("u_0"));
        assert!(!super::is_reserved_level_name("u"));
        assert!(!super::is_reserved_level_name("my?weird"));
    }
}
