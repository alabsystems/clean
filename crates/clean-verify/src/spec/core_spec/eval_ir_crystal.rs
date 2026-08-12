// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `EvalIR` — the crystal's worked example (job **C3**, acceptance gate).
//!
//! C3's gate is *"a hand-executed `is_zero` derivation on `Level.zero` and
//! `Level.param n` returns the right Bool"*. This module registers the module
//! literal and **six** such executions — the two the gate names, plus four more
//! that exercise the parts of the semantics the two easy cases do not touch:
//! recursion, `CondBr` short-circuiting, the `IMax` asymmetry, and the panic arm.
//!
//! | witness | input | expected |
//! |---|---|---|
//! | `ir_is_zero_on_zero` | `Level::Zero` | `ret [bool true]` |
//! | `ir_is_zero_on_param` | `Level::Param n`, ∀ n | `ret [bool false]` |
//! | `ir_is_zero_on_succ` | `Level::Succ(0)` | `ret [bool false]` |
//! | `ir_is_zero_on_max_zero_zero` | `Level::Max(0, 0)` | `ret [bool true]` |
//! | `ir_is_zero_on_max_zero_param` | `Level::Max(0, Param n)`, ∀ n | `ret [bool false]` |
//! | `ir_is_zero_on_imax_param_zero` | `Level::IMax(Param n, 0)`, ∀ n | `ret [bool true]` |
//! | `ir_is_zero_dead_arc_panics` | `Level::Max(<dead arc>, _)` | `ub assert_failed` |
//!
//! Each is a `def … : Eq IROutcome (ir_eval …) (…) := Eq.refl …`, so it is
//! **kernel-checked by computation** — the kernel actually runs the machine and
//! compares. Nothing is asserted.
//!
//! Every one of these agrees with `clean_kernel::Level::is_zero`
//! (`level/mod.rs:524-531`) and with the already-reflected `level_is_zero`
//! (`kexpr_beq.rs`), which is what makes the example a *cross-check* rather than
//! a restatement: three independent descriptions of the same classifier — the
//! Rust body, the layer-2 reflection, and this IR execution — give the same
//! answer on the same inputs.
//!
//! ## What this module is NOT, stated plainly
//!
//! `M_level_is_zero` here is **hand-authored**, not emitted. It cannot be
//! emitted today: the measured Phase-A probe finding is that `Level::is_zero`
//! does not lower at all — `register_enum`'s scalar-only field wall rejects
//! `Ty(enum-def)` on `Level` (job T1, the 64k-reject binding constraint), and
//! even past that the shared-ref payload-enum `Load` comparator fail-closes
//! (job T2). So there is no A0 artifact to transcribe yet.
//!
//! What that means for the crystal's five links: this module supplies the
//! **semantics** link (A3) and demonstrates that the semantics is adequate for
//! the target's shape. It does **not** supply the artifact link (A1) or the
//! representation link (A2). When T1/T2 land and A0 emits the real body, this
//! literal is replaced by the transcribed artifact and these seven witnesses
//! become the differential that says the transcription is faithful — which is
//! more use than they would have been written later.
//!
//! The shape below is the expected lowering, and the two places it may differ
//! from what A0 actually emits are named so the comparison is cheap:
//!
//! 1. **The `LevelArc` null check.** `LevelArc` is
//!    `pub struct LevelArc(Option<Arc<Level>>)` (`level/mod.rs:38`) whose
//!    `Deref` does `self.0.as_deref().expect("live LevelArc must contain a
//!    level")` — it *panics on `None`*. `Arc` is non-null, so
//!    `Option<Arc<Level>>` is niche-encoded as a nullable pointer, which is why
//!    a dead arc is `nullptr_` here and a live one is `ptr_`. This module
//!    lowers the `expect` to `ICmp ne` + `Assert`; a real emission may instead
//!    emit `CondBr` to a panic block. Both reach the panic on `None`, which is
//!    the property `ir_is_zero_dead_arc_panics` pins.
//! 2. **Discriminant read.** An enum is an ordinary aggregate value whose
//!    payload spine holds the discriminant at slot 0 and the selected variant's
//!    fields at slots 1.. — the convention fixed in [`super::eval_ir_state`],
//!    which is the trust-ir producer's own, so `ExtractField 0` reads the tag
//!    with no special case anywhere in the semantics. A real emission may read
//!    the tag with a `Load` of a discriminant place instead of an
//!    `ExtractField`.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// The whole `EvalIR` stage: syntax, state, value-level ops, machine, and
    /// the crystal's worked example.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check.
    pub(super) fn add_eval_ir(&mut self) -> Result<(), SpecError> {
        self.add_eval_ir_syntax()?;
        self.add_eval_ir_state()?;
        self.add_eval_ir_ops()?;
        self.add_eval_ir_machine()?;
        self.add_eval_ir_crystal()
    }

    /// The hand-authored `Level::is_zero` module and its execution witnesses.
    fn add_eval_ir_crystal(&mut self) -> Result<(), SpecError> {
        self.add_eval_ir_numerals()?;
        self.add_eval_ir_builders()?;
        self.add_eval_ir_level_module()?;
        self.add_eval_ir_witnesses()
    }

    /// Small unary numerals, named once so the module literal reads as a
    /// program rather than as a tower of `Nat.succ`.
    fn add_eval_ir_numerals(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def("def ir_d0 : Nat := Nat.zero", "EvalIR numeral 0.")?;
        self.add_recursive_def("def ir_d1 : Nat := Nat.succ ir_d0", "EvalIR numeral 1.")?;
        self.add_recursive_def("def ir_d2 : Nat := Nat.succ ir_d1", "EvalIR numeral 2.")?;
        self.add_recursive_def("def ir_d3 : Nat := Nat.succ ir_d2", "EvalIR numeral 3.")?;
        self.add_recursive_def("def ir_d4 : Nat := Nat.succ ir_d3", "EvalIR numeral 4.")?;
        self.add_recursive_def("def ir_d5 : Nat := Nat.succ ir_d4", "EvalIR numeral 5.")?;
        self.add_recursive_def("def ir_d6 : Nat := Nat.succ ir_d5", "EvalIR numeral 6.")?;
        self.add_recursive_def("def ir_d7 : Nat := Nat.succ ir_d6", "EvalIR numeral 7.")?;
        self.add_recursive_def("def ir_d8 : Nat := Nat.succ ir_d7", "EvalIR numeral 8.")?;
        self.add_recursive_def("def ir_d9 : Nat := Nat.succ ir_d8", "EvalIR numeral 9.")?;
        self.add_recursive_def("def ir_d10 : Nat := Nat.succ ir_d9", "EvalIR numeral 10.")?;
        self.add_recursive_def("def ir_d11 : Nat := Nat.succ ir_d10", "EvalIR numeral 11.")?;
        self.add_recursive_def("def ir_d12 : Nat := Nat.succ ir_d11", "EvalIR numeral 12.")?;
        self.add_recursive_def("def ir_d13 : Nat := Nat.succ ir_d12", "EvalIR numeral 13.")?;
        self.add_recursive_def("def ir_d14 : Nat := Nat.succ ir_d13", "EvalIR numeral 14.")?;
        self.add_recursive_def("def ir_d15 : Nat := Nat.succ ir_d14", "EvalIR numeral 15.")?;
        self.add_recursive_def("def ir_d16 : Nat := Nat.succ ir_d15", "EvalIR numeral 16.")?;

        // Fuel. `ir_run`'s Nat.rec only unfolds one level per machine step and
        // the `halted` minor ignores its induction hypothesis, so surplus fuel
        // costs nothing in reduction — it just has to be large enough. The
        // longest witness below (Max with two recursive calls) takes fewer than
        // thirty steps.
        self.add_recursive_def(
            "def ir_fuel : Nat := ir_nat_pow2 ir_d7",
            "128 steps of fuel: enough for every witness in this module with headroom, and \
             cheap because `ir_run` stops unfolding as soon as the machine halts.",
        )?;

        Ok(())
    }

    /// One-line list and node builders, so the module literal is reviewable.
    fn add_eval_ir_builders(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            "def ir_nl0 : IRList Nat := IRList.nil Nat",
            "Empty id list.",
        )?;
        self.add_recursive_def(
            "def ir_nl1 (a : Nat) : IRList Nat := IRList.cons Nat a ir_nl0",
            "One-element id list.",
        )?;
        self.add_recursive_def(
            "def ir_nl2 (a : Nat) (b : Nat) : IRList Nat := IRList.cons Nat a (ir_nl1 b)",
            "Two-element id list.",
        )?;

        self.add_recursive_def(
            "def ir_vl0 : IRList IRScalar := IRList.nil IRScalar",
            "Empty value list.",
        )?;
        self.add_recursive_def(
            "def ir_vl1 (a : IRScalar) : IRList IRScalar := IRList.cons IRScalar a ir_vl0",
            "One-element value list.",
        )?;
        self.add_recursive_def(
            "def ir_nd (i : IRInst) : IRNode := IRNode.mk i ir_nl0",
            "A node that binds nothing (a terminator, a Store, an Assert).",
        )?;
        self.add_recursive_def(
            "def ir_nd1 (i : IRInst) (r : Nat) : IRNode := IRNode.mk i (ir_nl1 r)",
            "A node that binds one result.",
        )?;

        self.add_recursive_def(
            "def ir_bd0 : IRList IRNode := IRList.nil IRNode",
            "Empty node list.",
        )?;
        self.add_recursive_def(
            "def ir_bd1 (a : IRNode) : IRList IRNode := IRList.cons IRNode a ir_bd0",
            "One-node body.",
        )?;
        self.add_recursive_def(
            "def ir_bd2 (a : IRNode) (b : IRNode) : IRList IRNode := IRList.cons IRNode a (ir_bd1 b)",
            "Two-node body.",
        )?;
        self.add_recursive_def(
            "def ir_bd3 (a : IRNode) (b : IRNode) (c : IRNode) : IRList IRNode := IRList.cons IRNode a (ir_bd2 b c)",
            "Three-node body.",
        )?;
        self.add_recursive_def(
            concat!(
                "def ir_bd6 (a : IRNode) (b : IRNode) (c : IRNode) (d : IRNode) (e : IRNode) (f : IRNode) : IRList IRNode := ",
                "IRList.cons IRNode a (IRList.cons IRNode b (IRList.cons IRNode c (ir_bd3 d e f)))",
            ),
            "Six-node body (the Max/IMax arms: extract, null constant, compare, assert, call, \
             terminator).",
        )?;

        self.add_recursive_def(
            "def ir_sc0 : IRList IRSwitchCase := IRList.nil IRSwitchCase",
            "Empty Switch arm list.",
        )?;
        self.add_recursive_def(
            concat!(
                "def ir_sc (v : Nat) (t : Nat) (rest : IRList IRSwitchCase) : IRList IRSwitchCase := ",
                "IRList.cons IRSwitchCase (IRSwitchCase.mk v t ir_nl0) rest",
            ),
            "Cons a no-argument Switch arm: selector value v jumps to block t.",
        )?;

        self.add_recursive_def(
            "def ir_blk0 : IRList IRBlock := IRList.nil IRBlock",
            "Empty block list.",
        )?;
        self.add_recursive_def(
            "def ir_blk (b : IRBlock) (rest : IRList IRBlock) : IRList IRBlock := IRList.cons IRBlock b rest",
            "Cons a block.",
        )?;

        self.add_recursive_def(
            "def ir_mem0 : IRList IRMemSlot := IRList.nil IRMemSlot",
            "Empty memory.",
        )?;
        self.add_recursive_def(
            concat!(
                "def ir_cell (a : Nat) (v : IRScalar) (rest : IRList IRMemSlot) : IRList IRMemSlot := ",
                "IRList.cons IRMemSlot (IRMemSlot.mk a v Bool.true) rest",
            ),
            "Cons a LIVE memory cell. Every cell a witness supplies is live, which is what the \
             representation premise A2 will have to entail.",
        )?;

        self.add_recursive_def(
            "def ir_sp0 : IRScalar := IRScalar.vnil",
            "Empty payload spine: an aggregate with no fields.",
        )?;
        self.add_recursive_def(
            "def ir_sp1 (a : IRScalar) : IRScalar := IRScalar.vcons a ir_sp0",
            "One-field payload spine.",
        )?;
        self.add_recursive_def(
            "def ir_sp2 (a : IRScalar) (b : IRScalar) : IRScalar := IRScalar.vcons a (ir_sp1 b)",
            "Two-field payload spine.",
        )?;
        self.add_recursive_def(
            concat!(
                "def ir_var (tag : Nat) (fs : IRScalar) : IRScalar := ",
                "IRScalar.aggv (IRScalar.vcons (IRScalar.int_ tag) fs)",
            ),
            "Build an enum value: the discriminant at spine slot 0, then the selected variant's \
             fields — the trust-ir producer's tag-at-field-0 convention \
             (`interpret.rs:1628-1684`), so `ExtractField 0` reads the tag and \
             `ExtractField (succ j)` reads payload field j with no special case in the semantics.",
        )?;

        Ok(())
    }

    /// The module literal.
    fn add_eval_ir_level_module(&mut self) -> Result<(), SpecError> {
        // Shorthands for the three types this body mentions.
        self.add_recursive_def(
            "def ir_tLevel : IRTy := IRTy.enum_ ir_d0",
            "The `Level` enum type, enum id 0. A real emission's id comes from the module's type \
             table; nothing in the semantics depends on the number.",
        )?;
        self.add_recursive_def("def ir_tBool : IRTy := IRTy.bool_", "The `bool` type.")?;
        self.add_recursive_def(
            "def ir_tU8 : IRTy := IRTy.uint_ ir_d8",
            "The enum-discriminant lane for Level. Five variants require the producer's smallest \
             canonical tag representation, U8 — not the legacy tuple representation's I64.",
        )?;
        self.add_recursive_def(
            "def ir_tPtr : IRTy := IRTy.ptr_",
            "The opaque pointer type.",
        )?;

        // ── b0: load the Level, read its discriminant, dispatch ─────
        //
        // Mirrors `match self { … }` over the five variants. Succ and Param
        // both go to the false block, which is exactly how the Rust body groups
        // them: `Level::Succ(_) | Level::Param(_) => false`
        // (`level/mod.rs:527`).
        self.add_recursive_def(
            concat!(
                "def ir_lz_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_bd3 ",
                "(ir_nd1 (IRInst.load ir_tLevel ir_d0 Bool.false) ir_d1) ",
                "(ir_nd1 (IRInst.extractfield ir_tU8 ir_d1 ir_d0) ir_d2) ",
                "(ir_nd (IRInst.switch ir_d2 ir_d6 ir_nl0 ",
                "(ir_sc ir_d0 ir_d1 (ir_sc ir_d1 ir_d2 (ir_sc ir_d2 ir_d3 ",
                "(ir_sc ir_d3 ir_d5 (ir_sc ir_d4 ir_d2 ir_sc0))))) Bool.true)))",
            ),
            "Entry block of Level::is_zero: load *self, read the discriminant, dispatch. The \
             Switch arms are zero->b1 (true), succ->b2 (false), max->b3, imax->b5, param->b2 \
             (false) — succ and param share the false block exactly as the Rust body shares that \
             match arm. exhaustive_enum_unreachable is TRUE because the five arms are the enum's \
             full tag set and the default is Unreachable; the flag licenses nothing in the \
             semantics, it is a claim to be proved against it.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_lz_b1 : IRBlock := IRBlock.mk ir_d1 ir_nl0 (ir_bd2 ",
                "(ir_nd1 (IRInst.const_ ir_tBool (IRConst.bool_ Bool.true)) ir_d3) ",
                "(ir_nd (IRInst.ret (ir_nl1 ir_d3))))",
            ),
            "Zero => true.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_lz_b2 : IRBlock := IRBlock.mk ir_d2 ir_nl0 (ir_bd2 ",
                "(ir_nd1 (IRInst.const_ ir_tBool (IRConst.bool_ Bool.false)) ir_d4) ",
                "(ir_nd (IRInst.ret (ir_nl1 ir_d4))))",
            ),
            "Succ | Param => false. Reached from two Switch arms, which is why it binds its own \
             constant rather than taking a block parameter.",
        )?;

        // ── b3/b4: Max(l1, l2) => l1.is_zero() && l2.is_zero() ──────
        //
        // The `&&` short-circuits, so it is a CondBr on the first result, not a
        // BinOp::And. Each recursive step first derefs a LevelArc, which is
        // where the null check and the panic live.
        self.add_recursive_def(
            concat!(
                "def ir_lz_b3 : IRBlock := IRBlock.mk ir_d3 ir_nl0 (ir_bd6 ",
                "(ir_nd1 (IRInst.extractfield ir_tPtr ir_d1 ir_d1) ir_d5) ",
                "(ir_nd1 (IRInst.const_ ir_tPtr IRConst.null_) ir_d6) ",
                "(ir_nd1 (IRInst.icmp IRICmpOp.ne_ ir_tPtr ir_d5 ir_d6) ir_d7) ",
                "(ir_nd (IRInst.assert ir_d7)) ",
                "(ir_nd1 (IRInst.call ir_d0 (ir_nl1 ir_d5)) ir_d8) ",
                "(ir_nd (IRInst.condbr ir_d8 ir_d4 ir_nl0 ir_d2 ir_nl0)))",
            ),
            "Max, left operand: deref the first LevelArc (field 0 of the variant, so index 1), \
             ASSERT it is non-null — the `expect(\"live LevelArc must contain a level\")` in \
             LevelArc::Deref — recurse, and short-circuit to the false block if the left side is \
             not zero. The `&&` is a CondBr, not a BinOp::And, because it short-circuits.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_lz_b4 : IRBlock := IRBlock.mk ir_d4 ir_nl0 (ir_bd6 ",
                "(ir_nd1 (IRInst.extractfield ir_tPtr ir_d1 ir_d2) ir_d9) ",
                "(ir_nd1 (IRInst.const_ ir_tPtr IRConst.null_) ir_d10) ",
                "(ir_nd1 (IRInst.icmp IRICmpOp.ne_ ir_tPtr ir_d9 ir_d10) ir_d11) ",
                "(ir_nd (IRInst.assert ir_d11)) ",
                "(ir_nd1 (IRInst.call ir_d0 (ir_nl1 ir_d9)) ir_d12) ",
                "(ir_nd (IRInst.ret (ir_nl1 ir_d12))))",
            ),
            "Max, right operand: reached only when the left side was zero, so the result of the \
             whole Max is the right side's.",
        )?;

        // ── b5: IMax(_, l2) => l2.is_zero() ─────────────────────────
        self.add_recursive_def(
            concat!(
                "def ir_lz_b5 : IRBlock := IRBlock.mk ir_d5 ir_nl0 (ir_bd6 ",
                "(ir_nd1 (IRInst.extractfield ir_tPtr ir_d1 ir_d2) ir_d13) ",
                "(ir_nd1 (IRInst.const_ ir_tPtr IRConst.null_) ir_d14) ",
                "(ir_nd1 (IRInst.icmp IRICmpOp.ne_ ir_tPtr ir_d13 ir_d14) ir_d15) ",
                "(ir_nd (IRInst.assert ir_d15)) ",
                "(ir_nd1 (IRInst.call ir_d0 (ir_nl1 ir_d13)) ir_d16) ",
                "(ir_nd (IRInst.ret (ir_nl1 ir_d16))))",
            ),
            "IMax(_, l2) => l2.is_zero(). The FIRST operand is never read — impredicative \
             collapse, `Level::IMax(_, l2) => l2.is_zero()` at level/mod.rs:529 — and \
             ir_is_zero_on_imax_param_zero pins that asymmetry by putting a Param (which is not \
             zero) in the ignored position.",
        )?;

        self.add_recursive_def(
            "def ir_lz_b6 : IRBlock := IRBlock.mk ir_d6 ir_nl0 (ir_bd1 (ir_nd IRInst.unreachable))",
            "The Switch default: unreachable, because the five arms are the enum's full tag set. \
             In the semantics reaching it is UB, so a proof that it is unreachable is a real \
             obligation and not a definition.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_lz_func : IRFunc := IRFunc.mk ir_d0 (ir_nl1 ir_d0) ir_d0 ",
                "(ir_blk ir_lz_b0 (ir_blk ir_lz_b1 (ir_blk ir_lz_b2 (ir_blk ir_lz_b3 ",
                "(ir_blk ir_lz_b4 (ir_blk ir_lz_b5 (ir_blk ir_lz_b6 ir_blk0)))))))",
            ),
            "Level::is_zero as an EvalIR function: id 0, one parameter (the &Level receiver, SSA \
             id 0), entry block 0, seven blocks.",
        )?;

        self.add_recursive_def(
            "def ir_lz_module : IRModule := IRModule.mk (IRList.cons IRFunc ir_lz_func (IRList.nil IRFunc)) (IRList.nil IRGlobal)",
            "M_level_is_zero: the single-function module the crystal's equality theorem quantifies \
             over. HAND-AUTHORED, not emitted — see this module's docs for exactly why, and for \
             what that does and does not license.",
        )?;

        Ok(())
    }

    /// The seven kernel-checked executions.
    fn add_eval_ir_witnesses(&mut self) -> Result<(), SpecError> {
        // Every witness runs `ir_eval ir_fuel ir_lz_module 0 [ptr 0] heap
        // next_addr` and is proved by Eq.refl — the kernel executes the machine
        // and compares the outcome. Aggregates are inline values, so a heap cell
        // holds the enum value itself; there is no arena argument and no handle
        // counter to supply. If any arm of the semantics were wrong for these
        // inputs the definition would not typecheck.
        self.add_recursive_def(
            concat!(
                "def ir_is_zero_on_zero : Eq IROutcome ",
                "(ir_eval ir_fuel ir_lz_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) ",
                "(ir_cell ir_d0 (ir_var ir_d0 ir_sp0) ir_mem0) ir_d1) ",
                "(IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true))) := ",
                "Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true)))",
            ),
            "GATE WITNESS 1: Level::Zero is definitely zero. The heap holds one live cell at \
             address 0 containing the payload-free enum value with tag 0. Proved by Eq.refl: the \
             kernel runs the machine.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_is_zero_on_param (n : Nat) : Eq IROutcome ",
                "(ir_eval ir_fuel ir_lz_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) ",
                "(ir_cell ir_d0 (ir_var ir_d4 (ir_sp1 (IRScalar.int_ n))) ir_mem0) ir_d1) ",
                "(IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false))) := ",
                "Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false)))",
            ),
            "GATE WITNESS 2: Level::Param n is NOT definitely zero, for EVERY n — the parameter \
             is universally quantified, so this is not a spot check. This is also the arm whose \
             converse must not be claimed: a parameter may be zero under some assignment, which \
             is why level_is_zero_sound is one-directional.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_is_zero_on_succ : Eq IROutcome ",
                "(ir_eval ir_fuel ir_lz_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) ",
                "(ir_cell ir_d0 (ir_var ir_d1 (ir_sp1 (IRScalar.ptr_ ir_d1))) ",
                "(ir_cell ir_d1 (ir_var ir_d0 ir_sp0) ir_mem0)) ir_d2) ",
                "(IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false))) := ",
                "Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false)))",
            ),
            "Succ(Zero) is not zero, and the recursive edge is NOT followed to decide it: succ is \
             a leaf arm. The inner Zero is present in the heap precisely so that a semantics which \
             wrongly recursed would return true and fail to typecheck.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_is_zero_on_max_zero_zero : Eq IROutcome ",
                "(ir_eval ir_fuel ir_lz_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) ",
                "(ir_cell ir_d0 ",
                "(ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ ir_d1) (IRScalar.ptr_ ir_d2))) ",
                "(ir_cell ir_d1 (ir_var ir_d0 ir_sp0) ",
                "(ir_cell ir_d2 (ir_var ir_d0 ir_sp0) ir_mem0))) ir_d3) ",
                "(IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true))) := ",
                "Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true)))",
            ),
            "Max(Zero, Zero) is zero. THE INTERESTING ONE: two nested recursive calls, two frame \
             pushes and pops, two LevelArc null checks that pass, and a CondBr that takes the \
             then-edge — all executed by the kernel.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_is_zero_on_max_zero_param (n : Nat) : Eq IROutcome ",
                "(ir_eval ir_fuel ir_lz_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) ",
                "(ir_cell ir_d0 ",
                "(ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ ir_d1) (IRScalar.ptr_ ir_d2))) ",
                "(ir_cell ir_d1 (ir_var ir_d0 ir_sp0) ",
                "(ir_cell ir_d2 (ir_var ir_d4 (ir_sp1 (IRScalar.int_ n))) ir_mem0))) ir_d3) ",
                "(IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false))) := ",
                "Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false)))",
            ),
            "Max(Zero, Param n) is not zero, for every n: the left side is zero so the CondBr \
             takes the then-edge into the right operand, and the right side decides. Together with \
             the previous witness this pins BOTH edges of the short-circuit.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_is_zero_on_imax_param_zero (n : Nat) : Eq IROutcome ",
                "(ir_eval ir_fuel ir_lz_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) ",
                "(ir_cell ir_d0 ",
                "(ir_var ir_d3 (ir_sp2 (IRScalar.ptr_ ir_d1) (IRScalar.ptr_ ir_d2))) ",
                "(ir_cell ir_d1 (ir_var ir_d4 (ir_sp1 (IRScalar.int_ n))) ",
                "(ir_cell ir_d2 (ir_var ir_d0 ir_sp0) ir_mem0))) ir_d3) ",
                "(IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true))) := ",
                "Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true)))",
            ),
            "IMax(Param n, Zero) IS zero — the impredicative collapse. The first operand is a \
             Param, which is not definitely zero, so a semantics that read it (as Max does) would \
             answer false. That it answers true is the asymmetry, pinned for every n.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_is_zero_dead_arc_panics : Eq IROutcome ",
                "(ir_eval ir_fuel ir_lz_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) ",
                "(ir_cell ir_d0 ",
                "(ir_var ir_d2 (ir_sp2 IRScalar.nullptr_ IRScalar.nullptr_)) ir_mem0) ir_d1) ",
                "(IROutcome.ub IRFault.assert_failed) := ",
                "Eq.refl IROutcome (IROutcome.ub IRFault.assert_failed)",
            ),
            "THE PANIC ARM, REACHED. A Max whose LevelArc edges are dead (None, niche-encoded as a \
             null pointer) makes LevelArc::Deref's expect() fire. The machine does NOT return a \
             Bool — it stops with ub assert_failed. This is why the crystal's theorem must carry a \
             liveness premise: `is_zero` is not panic-free at the IR level, and a theorem stated \
             without EncodesLiveLevelArc would be false, not merely weak.",
        )?;

        Ok(())
    }
}
