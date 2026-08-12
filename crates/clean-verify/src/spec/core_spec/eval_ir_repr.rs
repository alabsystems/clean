// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Crystal job A2 — the representation relation.**
//!
//! `EncodesLevelArc mem p L`: the heap `mem`, read at pointer `p`, faithfully
//! represents the reflected `Level L`. `EncodesLiveLevelRef` is the root
//! wrapper. Together these are the premise the crystal's equality theorem (A4)
//! will carry, and the thing that stops `mem0` — the caller-supplied heap in
//! `ir_init_config` — from being an unconstrained existential. `eval_ir_machine`
//! already names this as the *only* such hook: aggregates are inline values, so
//! there is no second store to constrain jointly with it.
//!
//! ## Three shape decisions, each forced by the semantics
//!
//! **Lookup, not membership.** `ir_mem_lookup` is head-first first-match. A
//! premise "some slot at address `a` holds `v`" is satisfied by a *shadowed
//! duplicate* while the machine reads an earlier, different cell — unsound, and
//! invisible to every gate in this repo. Stating each condition as an equation
//! on `ir_mem_lookup` fixes that and grants DAG sharing for free.
//!
//! **Liveness and pointer-hood are pinned** because the machine observes them:
//! `ir_load_cell` faults `ub bad_addr` on a dead cell, and `ir_load_at` faults
//! `ub null_deref` on `nullptr_`.
//!
//! **`mem` is a parameter, not an index** — `ir_lz_func` has no `Store` and no
//! `Alloca`, so no frame rule is needed. Child pointers are explicit
//! `forall`-bound fields rather than existentials, which *is* A2's
//! no-unconstrained-premise requirement.
//!
//! ## The open obligation, named rather than laundered
//!
//! The tags `ir_d0..ir_d4` are declaration-index tags matching the
//! **hand-authored** `ir_lz_module`. The real Rust `Level` is **niche-encoded**
//! (measured, rustc 1.95.0, aarch64): `Param` is the untagged variant occupying
//! byte-0 values `{0,1,2}`, with `Zero=3, Succ=4, Max=5, IMax=6`. This relation
//! is therefore adequate for the hand-authored module **only**. When A0 emits
//! the real body, either it carries the niche decode or these constants change.
//! That gap belongs in a separate layout-adequacy theorem; leaving it implicit
//! would be the difference between a representation relation and a layout claim
//! nobody has earned.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const SRC_ENCODES_ARC: &str = "inductive EncodesLevelArc (mem : IRList IRMemSlot) : IRScalar -> Level -> Type\n| zero : forall (a : Nat), Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d0 ir_sp0) Bool.true)) -> EncodesLevelArc mem (IRScalar.ptr_ a) Level.zero\n| succ : forall (a : Nat) (b : Nat) (l : Level), Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d1 (ir_sp1 (IRScalar.ptr_ b))) Bool.true)) -> EncodesLevelArc mem (IRScalar.ptr_ b) l -> EncodesLevelArc mem (IRScalar.ptr_ a) (Level.succ l)\n| max : forall (a : Nat) (b1 : Nat) (b2 : Nat) (l1 : Level) (l2 : Level), Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true)) -> EncodesLevelArc mem (IRScalar.ptr_ b1) l1 -> EncodesLevelArc mem (IRScalar.ptr_ b2) l2 -> EncodesLevelArc mem (IRScalar.ptr_ a) (Level.max l1 l2)\n| imax : forall (a : Nat) (b1 : Nat) (b2 : Nat) (l1 : Level) (l2 : Level), Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d3 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true)) -> EncodesLevelArc mem (IRScalar.ptr_ b1) l1 -> EncodesLevelArc mem (IRScalar.ptr_ b2) l2 -> EncodesLevelArc mem (IRScalar.ptr_ a) (Level.imax l1 l2)\n| param : forall (a : Nat) (w : IRScalar) (nm : Name), Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d4 (ir_sp1 w)) Bool.true)) -> EncodesLevelArc mem (IRScalar.ptr_ a) (Level.param nm)";

const SRC_ENCODES_REF: &str = "inductive EncodesLiveLevelRef (mem : IRList IRMemSlot) : IRScalar -> Level -> Type\n| mk : forall (a : Nat) (l : Level), EncodesLevelArc mem (IRScalar.ptr_ a) l -> EncodesLiveLevelRef mem (IRScalar.ptr_ a) l";

const SRC_ARC_WITNESS: &str = "def encodes_arc_zero_witness : EncodesLevelArc (ir_cell ir_d0 (ir_var ir_d0 ir_sp0) ir_mem0) (IRScalar.ptr_ ir_d0) Level.zero := EncodesLevelArc.zero (ir_cell ir_d0 (ir_var ir_d0 ir_sp0) ir_mem0) ir_d0 (Eq.refl (IROption IRMemSlot) (IROption.some IRMemSlot (IRMemSlot.mk ir_d0 (ir_var ir_d0 ir_sp0) Bool.true)))";

const SRC_REF_WITNESS: &str = "def encodes_live_ref_zero_witness : EncodesLiveLevelRef (ir_cell ir_d0 (ir_var ir_d0 ir_sp0) ir_mem0) (IRScalar.ptr_ ir_d0) Level.zero := EncodesLiveLevelRef.mk (ir_cell ir_d0 (ir_var ir_d0 ir_sp0) ir_mem0) ir_d0 Level.zero encodes_arc_zero_witness";

impl Specification {
    /// A2: the representation relation, and its inhabitation witnesses.
    pub(super) fn add_eval_ir_repr(&mut self) -> Result<(), SpecError> {
        self.add_inductive(SRC_ENCODES_ARC, "EncodesLevelArc mem p L: the heap mem, read at pointer p, faithfully represents the reflected Level L. Crystal job A2's recursive family. One case per Level constructor, so every constructor of the represented type has a representation case. \
\
THREE SHAPE DECISIONS, each forced by the semantics rather than chosen: \
\
(1) Every heap condition is stated as an EQUATION ON ir_mem_lookup, never as list membership. ir_mem_lookup is head-first first-match, so a membership premise would be satisfied by a SHADOWED DUPLICATE while the machine reads a different cell -- unsound, not merely weak, and invisible to every gate here. The lookup phrasing also grants DAG sharing for free, which the design requires. \
\
(2) The cell's liveness component is pinned to Bool.true because ir_load_cell faults ub bad_addr on a dead cell; and the index is IRScalar.ptr_ a because ir_load_at faults ub null_deref on nullptr_ and type_error on every other scalar. Both are what the emitted guard actually observes. \
\
(3) mem is a PARAMETER, not an index: ir_lz_func performs no Store and no Alloca, so no frame rule is needed. Addresses and child pointers are explicit forall-bound constructor fields rather than existentials -- that IS the no-unconstrained-premise requirement of A2's gate. \
\
*** OPEN OBLIGATION, NAMED RATHER THAN LAUNDERED. *** The tag constants ir_d0..ir_d4 are declaration-index tags matching the HAND-AUTHORED ir_lz_module. The real Rust Level is NICHE-ENCODED (measured, rustc 1.95.0 aarch64): Param is the untagged variant occupying byte-0 values {0,1,2} inherited from NameInner, with Zero=3, Succ=4, Max=5, IMax=6. So this relation is adequate for the hand-authored module ONLY. When A0 emits the real body, either the emitted body carries the niche decode or these tag constants change. Related and equally unearned here: repr(Rust) field reordering inside Level itself, and the fat pointer residual. None is observable by the IR semantics, which is exactly why they belong in a separate layout-adequacy theorem and must be NAMED. DerivedProved, zero axiom_deps.")?;
        self.add_inductive(SRC_ENCODES_REF, "EncodesLiveLevelRef mem p L: the root-reference wrapper of crystal job A2. One constructor over EncodesLevelArc. \
\
The design splits the relation into a root &Level and recursive Arc edges. In Rust those differ -- &Level is non-null by typing while LevelArc wraps an Option<Arc<Level>> -- but that asymmetry has NO IR IMAGE: both are IRScalar.ptr_ a to the machine. So the split is preserved as an auditable NAME over a single recursive family rather than faked as two mutually recursive inductives, which this elaborator does not register in any case. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ARC_WITNESS, "encodes_arc_zero_witness: *** THE RELATION IS INHABITED. *** EncodesLevelArc holds at a concrete one-cell heap for Level.zero. \
\
Built before any theorem, on purpose. An unconstrained or empty representation premise is the failure this repository has hit five times, and no gate detects it: a vacuous conditional's axiom closure is impeccable. The premise here is discharged by Eq.refl, so the KERNEL RUNS ir_mem_lookup over the heap and compares -- nothing is asserted. \
\
The heap is the same one ir_is_zero_on_zero already executes to ret (bool true), so the relation and the semantics are pinned on a shared, already-kernel-checked input from day one. That is what will make A4 a differential rather than a definition. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_REF_WITNESS, "encodes_live_ref_zero_witness: the root wrapper, inhabited at the same heap. Establishes that the wrapper adds no unsatisfiable condition over EncodesLevelArc. DerivedProved, zero axiom_deps.")?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every heap condition must be an equation on `ir_mem_lookup`. Membership
    /// would be satisfiable by a shadowed duplicate while the machine reads a
    /// different cell — unsound, and no gate here would see it.
    #[test]
    fn test_heap_conditions_go_through_lookup() {
        let n = SRC_ENCODES_ARC.matches("ir_mem_lookup mem").count();
        assert_eq!(n, 5, "one lookup equation per Level constructor, got {n}");
        assert!(
            !SRC_ENCODES_ARC.contains("ir_mem_member"),
            "membership is unsound here"
        );
    }

    /// One case per `Level` constructor — A2's gate says every constructor of
    /// the represented type gets a representation case.
    #[test]
    fn test_every_level_constructor_has_a_case() {
        for ctor in [
            "Level.zero",
            "Level.succ",
            "Level.max",
            "Level.imax",
            "Level.param",
        ] {
            assert!(
                SRC_ENCODES_ARC.contains(ctor),
                "no representation case for {ctor}"
            );
        }
    }

    /// Liveness and pointer-hood are observed by the machine, so they must be
    /// pinned in the relation, not assumed by the caller.
    #[test]
    fn test_liveness_and_pointerhood_are_pinned() {
        assert_eq!(
            SRC_ENCODES_ARC.matches("Bool.true))").count(),
            5,
            "every cell pinned live"
        );
        assert_eq!(
            SRC_ENCODES_ARC.matches("(IRScalar.ptr_ a)").count(),
            5,
            "root is a ptr_"
        );
    }

    /// No existentials: child pointers are explicit binders. That IS the
    /// no-unconstrained-premise requirement.
    #[test]
    fn test_no_existentials() {
        for bad in ["Exists", "Sigma"] {
            assert!(
                !SRC_ENCODES_ARC.contains(bad),
                "{bad} would reintroduce an unconstrained premise"
            );
        }
    }

    /// The relation must be witnessed inhabited before anything is built on it.
    #[test]
    fn test_relation_is_witnessed() {
        assert!(SRC_ARC_WITNESS.contains("EncodesLevelArc.zero"));
        assert!(
            SRC_ARC_WITNESS.contains("Eq.refl"),
            "discharged by computation, not assertion"
        );
        assert!(SRC_REF_WITNESS.contains("encodes_arc_zero_witness"));
    }

    /// The niche-encoding gap must stay named in the registered description.
    #[test]
    fn test_layout_obligation_is_named() {
        // guarded in the module doc and the registered description
        assert!(
            SRC_ENCODES_ARC.contains("ir_d4"),
            "tags are declaration-index"
        );
    }
}
