// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! U2 stage-3 deferral 1 — the TOTAL role of a universe-level parameter name.
//!
//! (`docs/analysis/u2-implementation-plan-2026-08-24.md` §3 stage 3, delta 3c,
//! first bullet; executed 2026-08-26 after the failure it said was missing was
//! exhibited.)
//!
//! # Why a role and not a bool
//!
//! Rigid-vs-assignable is a SIDE SET (`MetaState::rigid_level_params`), and
//! `is_rigid_level_param` is its membership test. That predicate is PARTIAL in
//! the way that matters: a name outside the set is not "assignable", it is
//! *unclassified*, and every caller silently rounded that down to assignable.
//!
//! The elaborator actually knows THREE populations, and they are recoverable
//! with no new state because `ElabCtx::universe_params` is the union of the
//! first two:
//!
//! | role      | how the name got here                                    | assignable? |
//! |-----------|----------------------------------------------------------|-------------|
//! | `Rigid`   | declared `.{u}` / file-scope `universe u` / auto-bound    | never       |
//! | `Minted`  | `ElabCtx::fresh_universe_param` (a level metavariable)    | yes         |
//! | `Foreign` | not bound by this declaration at all                     | yes (today) |
//!
//! `Minted = universe_params \ rigid_level_params`, so [`LevelParamRole`] is a
//! total classification of every name against the declaration's own state. It
//! adds no field, no undo record, no snapshot/restore obligation and no
//! generation bump — which is exactly why it is the shape that landed rather
//! than a parallel registry.
//!
//! # The measured failure behind it (EXHIBITED 2026-08-26, this box, builtin
//! prelude)
//!
//! Stage 3 deferred this item with the honest reason "no measured failure
//! behind it today. Schedule it when one appears." One appeared, and it is
//! the p30 silent-monomorphization class reached through a door p30 does not
//! cover.
//!
//! `infer/elab_core.rs`'s auto-bind path used `universe_params` membership as
//! a PROXY for "this name is already a parameter of the declaration":
//!
//! ```text
//! if !self.universe_params.contains(name) {
//!     self.universe_params.push(name.clone());
//!     self.metas.add_rigid_level_param(Name::from_string(name));
//! }
//! ```
//!
//! But `universe_params` also holds every MINTED name — `fresh_universe_param`
//! pushes there so the next mint skips it. So a user-written universe name
//! that collides with a name this declaration already minted takes the
//! not-a-parameter branch, never reaches the rigid set, and stays SOLVABLE.
//! Five shapes, one declaration body, differing only in the NAME (measured on
//! the release binary at `9cd4f68f6`, `--prelude builtin`):
//!
//! ```text
//! def badNoHole                  : Sort u_0 := Nat   FAIL  (auto-bound rigid)
//! def badDeclared.{u_0}          : Sort u_0 := Nat   FAIL  (declared rigid)
//! universe u_0; def badFile      : Sort u_0 := Nat   FAIL  (file-scope rigid)
//! def badAutoNamed (β : Sort _)  : Sort w   := Nat   FAIL  (auto-bound rigid)
//! def badAutoCollide (β : Sort _): Sort u_0 := Nat   PASS  <-- THE DEFECT
//! ```
//!
//! The fourth and fifth lines are the same declaration with the universe
//! renamed `w` -> `u_0`. The `Sort _` hole mints `u_0` first, so the written
//! `u_0` is read as "already a parameter", never becomes rigid, and
//! `add_level_constraint` solves it to `1`. The parameter then VANISHES —
//! p30's own tell, reproduced verbatim:
//!
//! ```text
//! def asType : Type := badAutoCollide Nat          -- typechecks (collapsed)
//! def atZero : Type := @badAutoCollide.{0} Nat
//!   -- UniverseLevelMismatch { name: "badAutoCollide", expected: 0, actual: 1 }
//!   -- i.e. ZERO universe parameters survived
//! ```
//!
//! Lean rejects that declaration. Clean accepted it.
//!
//! # What this closes, and what it does NOT
//!
//! CLOSED: a user-WRITTEN universe name is now classified by role, so it
//! becomes rigid whatever else shares its spelling — the verdict no longer
//! depends on whether an earlier hole happened to mint the same string.
//!
//! NOT CLOSED BY THIS MODULE: two DIFFERENT levels sharing one name. Level
//! identity is the `Name` (`clean_kernel::Level` has `Param(Name)` and no
//! metavariable constructor), so a classifier can only resolve the collision
//! by making BOTH occurrences rigid — the loud-refusal direction, never the
//! silent-solve one — not by separating them.
//!
//! That residue had a MEASURED COST, pinned rather than left unstated: a
//! declaration whose hole and whose written `u_N` must be INDEPENDENT was
//! refused, because the forcing constraint landed on the shared rigid name.
//! Isolated by spelling alone —
//!
//! ```text
//! def n3w (β : Sort _) (γ : Sort w)   (y : γ) (l : List β) : Nat := 0  PASS
//! def n3  (β : Sort _) (γ : Sort u_0) (y : γ) (l : List β) : Nat := 0  FAIL
//!   -- cannot assign rigid universe parameter u_0 := u_1 + 1
//! ```
//!
//! Lean accepts both. Before this brick Clean accepted both too — by solving
//! the written `u_0` away and registering universes the source does not
//! declare, reporting nothing. So the verdict still depended on the SPELLING;
//! only its direction changed, silent to loud.
//!
//! # THE RESIDUE IS CLOSED (2026-08-26b) — and NOT by this module
//!
//! The two follow-up routes were "reserve the mint namespace" and
//! "first-class `LevelMVarId`". The FIRST landed, and it is the cheaper one
//! precisely because it needs nothing from the kernel: universe metavariables
//! are now minted into a reserved spelling the surface grammar cannot produce
//! (`?u_0`, `?u_1`, …; [`crate::level_mint::MINT_PREFIX`], with the one
//! guillemet door shut by `elab_level`'s `ReservedUniverseName` refusal). A
//! written name and a minted one therefore inhabit DISJOINT namespaces, so
//! "two different levels sharing one name" is unreachable rather than
//! resolved. `clean_kernel::Level` is untouched; level identity is still
//! `Param(Name)`. p49 flipped to a positive fixture
//! (`p49_mint_collision_independence.lean`), p51 pins the reservation itself,
//! and p47 keeps failing with its fragment byte-identical — which is what
//! proves the cost was removed without relaxing the refusal.
//!
//! WHAT THAT MEANS FOR THIS MODULE, stated so nobody deletes it as dead: a
//! WRITTEN name can no longer be classified `Minted`, because it can no longer
//! be spelled like a mint. The classification stays anyway, and stays the
//! right shape. `universe_params`-membership was never a correct answer to
//! "is this name already a parameter of this declaration" — it was a proxy
//! that happened to be right whenever the two populations did not overlap.
//! Reserving the namespace makes them not overlap TODAY; the classifier is
//! what keeps the auto-bind path correct if that ever stops being true, and
//! it is still the total answer for the `Minted` names the elaborator itself
//! asks about. `infer::tests::mint_name_collision` asserts both halves — the
//! roles, and that a minted name is reserved.
//!
//! `Foreign` is likewise honest rather than aspirational: names from OTHER
//! declarations' `level_params` do reach `add_level_constraint` (simp's
//! env-lemma path records constraints under a lemma's own declared param
//! names — see `infer/elab_tactic.rs`), and they remain assignable exactly as
//! before. Classifying THEM is the wider refactor; this module only stops the
//! declaration's own names from being misread.

/// The role of a universe-level parameter NAME within the declaration
/// currently being elaborated. Total: every name has exactly one role.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LevelParamRole {
    /// A genuine `Level.param` of this declaration — written `.{u}`, declared
    /// by a file-scope `universe u`, or auto-bound from `Type u`. Unification
    /// must never assign it.
    Rigid,
    /// A universe METAVARIABLE this declaration minted
    /// (`fresh_universe_param`, from a `Type _` / `Sort _` hole or an
    /// application's implicit levels). Assignable, and generalized at
    /// declaration close if it never solves.
    Minted,
    /// Not bound by this declaration: another declaration's level parameter,
    /// or a name never seen here. Assignable today — see the module docs.
    Foreign,
}

impl LevelParamRole {
    /// Whether a name in this role may be assigned by unification.
    #[must_use]
    pub(crate) fn is_assignable(self) -> bool {
        !matches!(self, Self::Rigid)
    }
}

#[cfg(test)]
mod tests {
    use super::LevelParamRole;

    /// `Rigid` is the one role unification may not assign — the property every
    /// caller of the old side-set predicate was really asking about.
    #[test]
    fn test_level_param_role_only_rigid_is_unassignable() {
        assert!(!LevelParamRole::Rigid.is_assignable());
        assert!(LevelParamRole::Minted.is_assignable());
        assert!(LevelParamRole::Foreign.is_assignable());
    }
}
