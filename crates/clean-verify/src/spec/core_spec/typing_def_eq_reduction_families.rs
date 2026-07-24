// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Delta/iota reduction witness families (Part of #725).
//!
//! Defines `delta_reduces` and `iota_reduces` as finite, eliminable witness
//! families rather than opaque predicates. Each family has a single constructor
//! (`.mk`) bundling substitution-preservation and type-preservation evidence,
//! and a recursor (`.rec`) enabling structural recursion to project evidence.
//!
//! IMPORTANT: These predicates MUST be registered BEFORE `DefEq.rec` (in
//! `typing_def_eq.rs`), which references them in its delta/iota cases.
//! Registration order is controlled by `mod.rs::add_core_spec`.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_typing_def_eq_reduction_families(&mut self) -> Result<(), SpecError> {
        // =========================================================
        // Delta reduction witness family
        // =========================================================

        // delta_reduces was previously a HAND-AXIOMATIZED inductive: the type,
        // the sole constructor `mk`, AND the recursor were 3 separate
        // FoundationalRule axioms (delta_reduces / delta_reduces.mk /
        // delta_reduces.rec). It is now a GENUINE inductive registered via
        // `add_inductive` — the R2 mirror of the R1 iota_reduces drain below:
        // the `mk` constructor type transcribes the retired axiom BYTE-IDENTICALLY
        // (single field `delta_step (red_def the_red_env) e e'`, env pinned to
        // the_red_env — kernel-dumped types identical), and the kernel GENERATES
        // `delta_reduces.rec` (checked, sound by construction) — the same
        // retirement applied to iota_reduces / KernelDefEqAccepts / KernelAddDeclChain.
        // All three names now lower to non-Axiom kernel declarations and leave the
        // ConstantKind::Axiom census (89 -> 86).
        //
        // NOTE the generated recursor is the PROMOTED-PARAMETER (AndType) shape,
        // NOT the retired hand-written index shape: the single ctor's uniform
        // leading `(e e' : KExpr)` binders are promoted to IMPLICIT inductive
        // PARAMETERS (Lean's fixedIndicesToParams), so the motive ranges over the
        // MAJOR premise only (`motive : delta_reduces e e' -> Sort u`) and the
        // minor carries no index binders. The SOLE recursor consumer
        // `delta_reduces_to_step` (delta_step_bridge.rs) is written against that
        // generated shape. `.mk` is byte-identical to the retired axiom, so every
        // `delta_reduces.mk` consumer (delta_step_to_reduces, def_eq_lift_congr) is
        // unaffected. DefEq.delta / DefEq.rec reference delta_reduces only as a
        // type — unchanged. ZERO new axioms. Part of #725, #2859 (Brick R2).
        self.add_inductive(
            "inductive delta_reduces : KExpr -> KExpr -> Type\n| mk : forall (e : KExpr) (e' : KExpr), delta_step (red_def the_red_env) e e' -> delta_reduces e e'",
            "delta_reduces e e' holds if e unfolds to e' via definition unfolding. \
             Faithful single-constructor inductive (formerly 3 hand axioms: the type, the \
             sole constructor mk, and a hand-written recursor): the SOLE inhabitant `mk` is a \
             genuine operational delta step over the fixed the_red_env (church_rosser_whnf \
             retirement track). Env pinned to the_red_env (NOT forall/exists env). The kernel \
             generates delta_reduces.rec, sound by construction. Part of #725, #2859.",
        )?;

        // =========================================================
        // Iota reduction witness family
        // =========================================================

        // iota_reduces was previously a HAND-AXIOMATIZED inductive: the type,
        // the sole constructor `mk`, AND the recursor were 3 separate
        // FoundationalRule axioms (iota_reduces / iota_reduces.mk /
        // iota_reduces.rec). It is now a GENUINE inductive registered via
        // `add_inductive`: the `mk` constructor type transcribes the retired
        // axiom BYTE-IDENTICALLY (single field `iota_step (red_rec the_red_env)
        // e e'`, env pinned to the_red_env — kernel-dumped types identical), and
        // the kernel GENERATES `iota_reduces.rec` (checked, sound by
        // construction) — the same retirement applied to KernelDefEqAccepts /
        // KernelAddDeclChain. All three names now lower to non-Axiom kernel
        // declarations and leave the ConstantKind::Axiom census (92 -> 89).
        //
        // NOTE the generated recursor is the PROMOTED-PARAMETER (AndType) shape,
        // NOT the retired hand-written index shape: the single ctor's uniform
        // leading `(e e' : KExpr)` binders are promoted to IMPLICIT inductive
        // PARAMETERS (Lean's fixedIndicesToParams), so the motive ranges over the
        // MAJOR premise only (`motive : iota_reduces e e' -> Sort u`) and the
        // minor carries no index binders. The SOLE recursor consumer
        // `iota_reduces_to_step` (iota_step_bridge.rs) is written against that
        // generated shape. `.mk` is byte-identical to the retired axiom, so every
        // `iota_reduces.mk` consumer (DefEq.iota's evidence, def_eq_lift_congr,
        // iota_step_to_reduces) is unaffected. ZERO new axioms. Part of #725,
        // #2859 (Bricks R0+R1). delta_reduces above stays hand-axiomatized (R2/R3).
        self.add_inductive(
            "inductive iota_reduces : KExpr -> KExpr -> Type\n| mk : forall (e : KExpr) (e' : KExpr), iota_step (red_rec the_red_env) e e' -> iota_reduces e e'",
            "iota_reduces e e' holds if e reduces to e' via match/recursor elimination. \
             Faithful single-constructor inductive (formerly 3 hand axioms: the type, the \
             sole constructor mk, and a hand-written recursor): the SOLE inhabitant `mk` is a \
             genuine operational iota step over the fixed the_red_env (church_rosser_whnf \
             retirement track). Env pinned to the_red_env (NOT forall/exists env). The kernel \
             generates iota_reduces.rec, sound by construction. Part of #725, #2859.",
        )?;

        Ok(())
    }
}
