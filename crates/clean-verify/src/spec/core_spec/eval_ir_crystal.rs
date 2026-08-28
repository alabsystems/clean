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
//! `ir_lzm_module` here — the `m` is for MODEL — is **hand-authored**, not
//! emitted, and it is **structurally different from what the compiler
//! emits**. Until 2026-08-22 it was registered as `ir_lz_module`, the chain's
//! name, and the A4/A5 theorems over it were quoted on the status page as the
//! designated target's link 4. The mint (`src/ir_mint`, `tests/crystal_a2_mint_lz.rs`)
//! then derived the emitted body mechanically and diffed it against this one,
//! and the two differ in FOUR classes — measured, printed verbatim by the gate,
//! and pinned in `tests/crystal_a1_lineage/level_is_zero.rs`:
//!
//! 1. **The switch.** This module: five arms `{0→b1, 1→b2, 2→b3, 3→b5, 4→b2}`,
//!    default `unreachable`, `exhaustive_enum_unreachable` TRUE. Emitted: four
//!    arms `{0→bb1, 1→bb2, 4→bb3, 2→bb4}`, `IMax` (tag 3) on the DEFAULT edge,
//!    no `unreachable` anywhere, flag FALSE. The flagship's wrong-exhaustive-flag
//!    class, on the designated target itself.
//! 2. **Per-arm `ret`** here vs `br` to a join block with a `bool` parameter
//!    (`bb6(%1)`, plus an inner join `bb9(%2)`) there.
//! 3. **The deref.** Here: `extractfield` the `LevelArc` pointer out of the
//!    loaded enum, `icmp ne null`, `assert`, one self-call — the deref INLINED
//!    as a null check. Emitted: `gep` the receiver to byte offset 8 / 16 and
//!    `call <LevelArc as Deref>::deref` before each self-call; no assert, no
//!    null constant.
//! 4. **Three emitted-only blocks** (right-Max recursion, short-circuit false
//!    arm, inner join): 10 blocks against 7.
//!
//! So this module is the SEMANTIC MODEL of `Level::is_zero`, and
//! `ir_lzm_correct` / `ir_lzm_machine_sound` are theorems about the model. The
//! emitted module is registered separately, under the chain's name
//! `ir_lz_module`, by [`super::eval_ir_level_minted`] — replayed from the
//! minted script, checked by three readers — and over THAT module the A4
//! sentence is REFUTED, kernel-checked (`ir_lz_minted_refutes_a4_on_max`): the
//! emitted body calls a function the module does not define, so the `Max` and
//! `IMax` arms go `stuck no_func` where A4 says they return. Link 4 of the
//! designated target is OPEN; the decision and the scoped route to close it
//! are in `designs/2026-08-22-is-zero-model-vs-minted-decision.md`.
//!
//! ### The history, kept because the page cites it
//!
//! Until 2026-08-12 these paragraphs said the body "does not lower at all".
//! That was true when written and false since 2026-08-10; the measured release
//! row (`data/crystal_a0_a6_probe.json`) is `lowered / spliced`, 28 instrs,
//! `unsupported: []`, `agreed`. The emitted body calls out of the fragment
//! through `<LevelArc as Deref>::deref`, whose own callees — `Option::as_deref`
//! and `Option::expect` — are declaration-only in the assembled module (rustc
//! has no cross-crate THIR), which is the A0 criterion *bodyful reachable
//! closure*, recorded FAIL and architectural. That is what blocks a theorem
//! about the EMITTED body from reaching the kernel function through the
//! artifact alone; it never blocked the IDENTITY of the module, which is why
//! the minted one now exists beside this one.
//!
//! What this module still supplies, unchanged: the **semantics** link (A3) —
//! seven executions that exercise recursion, the short-circuit, the `IMax`
//! asymmetry and the panic arm — and the proof ARCHITECTURE (representation
//! relation, cost function, activation induction, A4, A5 composed with
//! `level_is_zero_sound`) that a re-derivation over the emitted CFG will reuse.

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
        self.add_eval_ir_witnesses()?;
        // The MINTED module for the same body, under the chain's name, with
        // its own computed witnesses -- including the two that go STUCK.
        self.add_eval_ir_level_minted_module()?;
        // Option B step one: the same minted body with a deref MODEL beside
        // it, under its OWN module name. Must follow the minted module --
        // `ir_lzb_module` names `ir_lz_func` rather than transcribing it, which
        // is the whole point and also a hard ordering dependency.
        self.add_eval_ir_lzb_module()
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
        // ── the 2026-08-22 widening: ir_d17..ir_d63 ──────────────────────
        // The designated target's mint refusal was "SSA positions reach 20,
        // above the ir_d0..ir_d16 atom pool". Structural slots (SSA ids, block
        // ids, function ids) stay ATOMS by design — a garbage numeral must
        // keep refusing loudly — so the pool grows to 63 instead of the rule
        // dissolving into literals. TWO gaps, deliberate: ir_d32 and ir_d64
        // are ALREADY registered by the chains that own them (Nat.add forms in
        // eval_ir_bvar_range.rs / eval_ir_valid_char.rs, registered after this
        // section — a second definition here would be a duplicate, and the
        // lineage suite's numeral_names_carry_their_values proved exactly that
        // the first time this widening was built). ir_d33 therefore takes the
        // Nat.add form, since ir_d32 does not exist yet at this point in the
        // registration order. Cost, measured before adoption: see the lz
        // migration commit.
        self.add_recursive_def("def ir_d17 : Nat := Nat.succ ir_d16", "EvalIR numeral 17.")?;
        self.add_recursive_def("def ir_d18 : Nat := Nat.succ ir_d17", "EvalIR numeral 18.")?;
        self.add_recursive_def("def ir_d19 : Nat := Nat.succ ir_d18", "EvalIR numeral 19.")?;
        self.add_recursive_def("def ir_d20 : Nat := Nat.succ ir_d19", "EvalIR numeral 20.")?;
        self.add_recursive_def("def ir_d21 : Nat := Nat.succ ir_d20", "EvalIR numeral 21.")?;
        self.add_recursive_def("def ir_d22 : Nat := Nat.succ ir_d21", "EvalIR numeral 22.")?;
        self.add_recursive_def("def ir_d23 : Nat := Nat.succ ir_d22", "EvalIR numeral 23.")?;
        self.add_recursive_def("def ir_d24 : Nat := Nat.succ ir_d23", "EvalIR numeral 24.")?;
        self.add_recursive_def("def ir_d25 : Nat := Nat.succ ir_d24", "EvalIR numeral 25.")?;
        self.add_recursive_def("def ir_d26 : Nat := Nat.succ ir_d25", "EvalIR numeral 26.")?;
        self.add_recursive_def("def ir_d27 : Nat := Nat.succ ir_d26", "EvalIR numeral 27.")?;
        self.add_recursive_def("def ir_d28 : Nat := Nat.succ ir_d27", "EvalIR numeral 28.")?;
        self.add_recursive_def("def ir_d29 : Nat := Nat.succ ir_d28", "EvalIR numeral 29.")?;
        self.add_recursive_def("def ir_d30 : Nat := Nat.succ ir_d29", "EvalIR numeral 30.")?;
        self.add_recursive_def("def ir_d31 : Nat := Nat.succ ir_d30", "EvalIR numeral 31.")?;
        self.add_recursive_def("def ir_d33 : Nat := Nat.add ir_d16 ir_d17", "EvalIR numeral 33 (ir_d32 is chain-owned and not yet registered here; the sum form keeps this section self-contained).")?;
        self.add_recursive_def("def ir_d34 : Nat := Nat.succ ir_d33", "EvalIR numeral 34.")?;
        self.add_recursive_def("def ir_d35 : Nat := Nat.succ ir_d34", "EvalIR numeral 35.")?;
        self.add_recursive_def("def ir_d36 : Nat := Nat.succ ir_d35", "EvalIR numeral 36.")?;
        self.add_recursive_def("def ir_d37 : Nat := Nat.succ ir_d36", "EvalIR numeral 37.")?;
        self.add_recursive_def("def ir_d38 : Nat := Nat.succ ir_d37", "EvalIR numeral 38.")?;
        self.add_recursive_def("def ir_d39 : Nat := Nat.succ ir_d38", "EvalIR numeral 39.")?;
        self.add_recursive_def("def ir_d40 : Nat := Nat.succ ir_d39", "EvalIR numeral 40.")?;
        self.add_recursive_def("def ir_d41 : Nat := Nat.succ ir_d40", "EvalIR numeral 41.")?;
        self.add_recursive_def("def ir_d42 : Nat := Nat.succ ir_d41", "EvalIR numeral 42.")?;
        self.add_recursive_def("def ir_d43 : Nat := Nat.succ ir_d42", "EvalIR numeral 43.")?;
        self.add_recursive_def("def ir_d44 : Nat := Nat.succ ir_d43", "EvalIR numeral 44.")?;
        self.add_recursive_def("def ir_d45 : Nat := Nat.succ ir_d44", "EvalIR numeral 45.")?;
        self.add_recursive_def("def ir_d46 : Nat := Nat.succ ir_d45", "EvalIR numeral 46.")?;
        self.add_recursive_def("def ir_d47 : Nat := Nat.succ ir_d46", "EvalIR numeral 47.")?;
        self.add_recursive_def("def ir_d48 : Nat := Nat.succ ir_d47", "EvalIR numeral 48.")?;
        self.add_recursive_def("def ir_d49 : Nat := Nat.succ ir_d48", "EvalIR numeral 49.")?;
        self.add_recursive_def("def ir_d50 : Nat := Nat.succ ir_d49", "EvalIR numeral 50.")?;
        self.add_recursive_def("def ir_d51 : Nat := Nat.succ ir_d50", "EvalIR numeral 51.")?;
        self.add_recursive_def("def ir_d52 : Nat := Nat.succ ir_d51", "EvalIR numeral 52.")?;
        self.add_recursive_def("def ir_d53 : Nat := Nat.succ ir_d52", "EvalIR numeral 53.")?;
        self.add_recursive_def("def ir_d54 : Nat := Nat.succ ir_d53", "EvalIR numeral 54.")?;
        self.add_recursive_def("def ir_d55 : Nat := Nat.succ ir_d54", "EvalIR numeral 55.")?;
        self.add_recursive_def("def ir_d56 : Nat := Nat.succ ir_d55", "EvalIR numeral 56.")?;
        self.add_recursive_def("def ir_d57 : Nat := Nat.succ ir_d56", "EvalIR numeral 57.")?;
        self.add_recursive_def("def ir_d58 : Nat := Nat.succ ir_d57", "EvalIR numeral 58.")?;
        self.add_recursive_def("def ir_d59 : Nat := Nat.succ ir_d58", "EvalIR numeral 59.")?;
        self.add_recursive_def("def ir_d60 : Nat := Nat.succ ir_d59", "EvalIR numeral 60.")?;
        self.add_recursive_def("def ir_d61 : Nat := Nat.succ ir_d60", "EvalIR numeral 61.")?;
        self.add_recursive_def("def ir_d62 : Nat := Nat.succ ir_d61", "EvalIR numeral 62.")?;
        self.add_recursive_def("def ir_d63 : Nat := Nat.succ ir_d62", "EvalIR numeral 63.")?;

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

        // The CONSTANT-side counterparts. `trust_ir::Constant::Aggregate` is an
        // element list, and `IRConst` carries it as an inline spine for the same
        // nested-inductive reason `IRScalar` does, so these mirror
        // ir_sp0/ir_sp1/ir_sp2/ir_var one for one.
        self.add_recursive_def(
            "def ir_cs0 : IRConst := IRConst.vnil",
            "Empty constant element spine: `Constant::Aggregate(vec![])`.",
        )?;
        self.add_recursive_def(
            "def ir_cs1 (a : IRConst) : IRConst := IRConst.vcons a ir_cs0",
            "One-element constant spine.",
        )?;
        self.add_recursive_def(
            "def ir_cs2 (a : IRConst) (b : IRConst) : IRConst := IRConst.vcons a (ir_cs1 b)",
            "Two-element constant spine.",
        )?;
        self.add_recursive_def(
            "def ir_cvar (tag : Nat) : IRConst := IRConst.aggv (ir_cs1 (IRConst.int_ tag))",
            "Build a FIELDLESS enum CONSTANT: `const enum.N { tag }`. MEASURED shape — this is \
             exactly what `mode::CleanMode::from_source_system` (`const enum.13 { k }`) and \
             `<tc::ExprPathStep as Clone>::clone` (`const enum.181 { k }`) emit at every arm: \
             `Constant::Aggregate([Constant::Int(k)])`, arity one, element kind Int, nesting \
             depth one. `ir_const_value (ir_cvar k)` is definitionally `ir_var k ir_sp0`, so a \
             materialized enum constant and a loaded enum value are the SAME value and \
             ExtractField reads both the same way.",
        )?;

        Ok(())
    }

    /// The module literal.
    fn add_eval_ir_level_module(&mut self) -> Result<(), SpecError> {
        // Shorthands for the three types this body mentions.
        self.add_recursive_def(
            "def ir_tLevel : IRTy := IRTy.enum_ ir_d2",
            "The `Level` enum type, enum id 2 -- the id the emitted body names in `%3 = load \
             enum.2, ptr %0` (tests/fixtures/level_is_zero.trust-ir.txt), and the same id \
             `ir_ko_tenum` carries for the same Rust type in the kind_ord chain. \
             \
             CORRECTED 2026-08-19 from `IRTy.enum_ ir_d0`, whose description read \"enum id 0. A \
             real emission's id comes from the module's type table; nothing in the semantics \
             depends on the number.\" Both halves of that sentence were true and together they \
             were a licence to write a number that matches no emission at all: the placeholder \
             was then copied into `ir_h2_b0`, where the artifact says enum.13. The semantics \
             indeed does not depend on the number -- `ir_exec` binds the load's type and discards \
             it -- but the CLAIM that a registered module is the emitted one does, and that claim \
             is what the A1 load lane now checks.",
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
                "def ir_lzm_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_bd3 ",
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
             semantics, it is a claim to be proved against it. MEASURED 2026-08-22 against the \
             emitted body (ir_lz_b0, minted): the compiler emits FOUR arms with IMax on the \
             default edge and the flag FALSE -- this block is the MODEL's dispatch, not the \
             artifact's.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_lzm_b1 : IRBlock := IRBlock.mk ir_d1 ir_nl0 (ir_bd2 ",
                "(ir_nd1 (IRInst.const_ ir_tBool (IRConst.bool_ Bool.true)) ir_d3) ",
                "(ir_nd (IRInst.ret (ir_nl1 ir_d3))))",
            ),
            "Zero => true.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_lzm_b2 : IRBlock := IRBlock.mk ir_d2 ir_nl0 (ir_bd2 ",
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
                "def ir_lzm_b3 : IRBlock := IRBlock.mk ir_d3 ir_nl0 (ir_bd6 ",
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
                "def ir_lzm_b4 : IRBlock := IRBlock.mk ir_d4 ir_nl0 (ir_bd6 ",
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
                "def ir_lzm_b5 : IRBlock := IRBlock.mk ir_d5 ir_nl0 (ir_bd6 ",
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
            "def ir_lzm_b6 : IRBlock := IRBlock.mk ir_d6 ir_nl0 (ir_bd1 (ir_nd IRInst.unreachable))",
            "The Switch default: unreachable, because the five arms are the enum's full tag set. \
             In the semantics reaching it is UB, so a proof that it is unreachable is a real \
             obligation and not a definition.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_lzm_func : IRFunc := IRFunc.mk ir_d0 (ir_nl1 ir_d0) ir_d0 ",
                "(ir_blk ir_lzm_b0 (ir_blk ir_lzm_b1 (ir_blk ir_lzm_b2 (ir_blk ir_lzm_b3 ",
                "(ir_blk ir_lzm_b4 (ir_blk ir_lzm_b5 (ir_blk ir_lzm_b6 ir_blk0)))))))",
            ),
            "Level::is_zero as an EvalIR function: id 0, one parameter (the &Level receiver, SSA \
             id 0), entry block 0, seven blocks.",
        )?;

        self.add_recursive_def(
            "def ir_lzm_module : IRModule := IRModule.mk (IRList.cons IRFunc ir_lzm_func (IRList.nil IRFunc)) (IRList.nil IRGlobal)",
            "ir_lzm_module -- the m is for MODEL: the hand-authored single-function SEMANTIC MODEL \
             of Level::is_zero with the deref inlined, which ir_lzm_correct (A4) and \
             ir_lzm_machine_sound (A5) quantify over. NOT the emitted body: measured 2026-08-22 \
             to differ from the minted ir_lz_module in four classes (see this module's docs). \
             Renamed out of the chain's namespace the same day so the minted module could take \
             it; the theorems over this module are theorems about the model.",
        )?;

        Ok(())
    }

    /// The seven kernel-checked executions.
    fn add_eval_ir_witnesses(&mut self) -> Result<(), SpecError> {
        // Every witness runs `ir_eval ir_fuel ir_lzm_module 0 [ptr 0] heap
        // next_addr` and is proved by Eq.refl — the kernel executes the machine
        // and compares the outcome. Aggregates are inline values, so a heap cell
        // holds the enum value itself; there is no arena argument and no handle
        // counter to supply. If any arm of the semantics were wrong for these
        // inputs the definition would not typecheck.
        self.add_recursive_def(
            concat!(
                "def ir_is_zero_on_zero : Eq IROutcome ",
                "(ir_eval ir_fuel ir_lzm_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) ",
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
                "(ir_eval ir_fuel ir_lzm_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) ",
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
                "(ir_eval ir_fuel ir_lzm_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) ",
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
                "(ir_eval ir_fuel ir_lzm_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) ",
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
                "(ir_eval ir_fuel ir_lzm_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) ",
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
                "(ir_eval ir_fuel ir_lzm_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) ",
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
                "(ir_eval ir_fuel ir_lzm_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) ",
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

        self.add_eval_ir_const_witnesses()
    }

    /// Kernel-executed witnesses for the constant evaluator.
    ///
    /// Two jobs, and both are load-bearing. First, the AGGREGATE form added for
    /// `mode::CleanMode::from_source_system` has a real evaluation case, and
    /// these run it: at an aggregate type it materializes the value, at a
    /// scalar type it fails closed, and a bare element-spine node fails closed.
    /// Second — and this is the regression guard — the SEVEN pre-existing
    /// constructors keep their exact meaning after `ir_const_value` was
    /// re-authored from a `match` into an `IRConst.rec`. Every one of them is
    /// pinned here by `Eq.refl`, so a mis-ordered recursor minor cannot pass.
    fn add_eval_ir_const_witnesses(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            "def ir_const_value_int_unchanged (n : Nat) : Eq IRScalar (ir_const_value (IRConst.int_ n)) (IRScalar.int_ n) := Eq.refl IRScalar (IRScalar.int_ n)",
            "REGRESSION PIN: the int_ arm of ir_const_value, for every n. DerivedProved, zero \
             axiom_deps.",
        )?;
        self.add_recursive_def(
            "def ir_const_value_bool_unchanged (b : Bool) : Eq IRScalar (ir_const_value (IRConst.bool_ b)) (IRScalar.bool_ b) := Eq.refl IRScalar (IRScalar.bool_ b)",
            "REGRESSION PIN: the bool_ arm, for every b.",
        )?;
        self.add_recursive_def(
            "def ir_const_value_unit_unchanged : Eq IRScalar (ir_const_value IRConst.unit_) IRScalar.unit_ := Eq.refl IRScalar IRScalar.unit_",
            "REGRESSION PIN: the unit_ arm.",
        )?;
        self.add_recursive_def(
            "def ir_const_value_null_unchanged : Eq IRScalar (ir_const_value IRConst.null_) IRScalar.nullptr_ := Eq.refl IRScalar IRScalar.nullptr_",
            "REGRESSION PIN: the null_ arm — note the constructor names differ on the two sides \
             (IRConst.null_ vs IRScalar.nullptr_), which is exactly the pairing a mis-ordered \
             recursor would break.",
        )?;
        self.add_recursive_def(
            "def ir_const_value_undef_unchanged : Eq IRScalar (ir_const_value IRConst.undef_) IRScalar.undef_ := Eq.refl IRScalar IRScalar.undef_",
            "REGRESSION PIN: the undef_ arm.",
        )?;
        self.add_recursive_def(
            "def ir_const_value_float_unchanged (n : Nat) : Eq IRScalar (ir_const_value (IRConst.float_ n)) (IRScalar.float_ n) := Eq.refl IRScalar (IRScalar.float_ n)",
            "REGRESSION PIN: the float_ arm, for every bit pattern.",
        )?;
        self.add_recursive_def(
            "def ir_const_value_func_unchanged (f : Nat) : Eq IRScalar (ir_const_value (IRConst.func_ f)) (IRScalar.fnptr_ f) := Eq.refl IRScalar (IRScalar.fnptr_ f)",
            "REGRESSION PIN: the func_ arm, for every function id.",
        )?;
        self.add_recursive_def(
            "def ir_const_eval_int_still_wraps : Eq IRStepResult (ir_const_eval ir_u2 (IRConst.int_ 7)) (IRStepResult.value (IRScalar.int_ 3)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ 3))",
            "REGRESSION PIN, the typed lane: an integer constant is still canonicalized modulo \
             2^w — 7 at width 2 is 3. This is the arm the kind_ord chain's answers travel \
             through, kept exact across the aggregate extension.",
        )?;
        self.add_recursive_def(
            "def ir_const_eval_int_rejects_agg_ty : Eq IRStepResult (ir_const_eval (IRTy.enum_ ir_d13) (IRConst.int_ ir_d1)) (IRStepResult.fault (IROutcome.type_error IRFault.not_int)) := Eq.refl IRStepResult (IRStepResult.fault (IROutcome.type_error IRFault.not_int))",
            "REGRESSION PIN, the other direction: a SCALAR constant at an aggregate type is still \
             type_error not_int. The two typed lanes reject each other's types, so neither the \
             new form nor the old one can be smuggled through the wrong one.",
        )?;

        self.add_recursive_def(
            "def ir_const_value_agg_is_ir_var (k : Nat) : Eq IRScalar (ir_const_value (ir_cvar k)) (ir_var k ir_sp0) := Eq.refl IRScalar (ir_var k ir_sp0)",
            "THE AGGREGATE MATERIALIZATION, for every tag: `const enum.N { k }` denotes exactly \
             the value a LOADED fieldless enum with discriminant k denotes. That is what makes \
             the new constant form interoperate with the tag-at-slot-0 convention rather than \
             sit beside it — ExtractField, the representation relations and the switch all see \
             one value shape. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            "def ir_const_eval_agg_at_enum (k : Nat) : Eq IRStepResult (ir_const_eval (IRTy.enum_ ir_d13) (ir_cvar k)) (IRStepResult.value (ir_var k ir_sp0)) := Eq.refl IRStepResult (IRStepResult.value (ir_var k ir_sp0))",
            "THE NEW EVALUATION CASE, executed: at an enum type an aggregate constant evaluates \
             to the aggregate value, for every tag. Not a stub and not a fallthrough — the \
             kernel computes it.",
        )?;
        self.add_recursive_def(
            "def ir_const_eval_agg_at_struct : Eq IRStepResult (ir_const_eval (IRTy.struct_ ir_d2) (ir_cvar ir_d1)) (IRStepResult.value (ir_var ir_d1 ir_sp0)) := Eq.refl IRStepResult (IRStepResult.value (ir_var ir_d1 ir_sp0))",
            "The aggregate lane is not enum-only: struct, tuple and array types accept an \
             aggregate constant too, which is what ir_ty_is_agg says.",
        )?;
        self.add_recursive_def(
            "def ir_const_eval_agg_at_scalar_fails_closed : Eq IRStepResult (ir_const_eval ir_tU8 (ir_cvar ir_d1)) (IRStepResult.fault (IROutcome.type_error IRFault.not_agg)) := Eq.refl IRStepResult (IRStepResult.fault (IROutcome.type_error IRFault.not_agg))",
            "FAIL-CLOSED: an aggregate constant at a scalar type is a type error, not a silently \
             accepted value. The IRTy on Inst::Const is semantic input here exactly as it is for \
             integer constants.",
        )?;
        self.add_recursive_def(
            "def ir_const_eval_bare_spine_fails_closed : Eq IRStepResult (ir_const_eval (IRTy.enum_ ir_d13) IRConst.vnil) (IRStepResult.fault (IROutcome.type_error IRFault.not_agg)) := Eq.refl IRStepResult (IRStepResult.fault (IROutcome.type_error IRFault.not_agg))",
            "FAIL-CLOSED on the inline spine's junk inhabitants: a BARE vnil is an element-list \
             node, not a constant of any type. The price of the inline spine, paid explicitly \
             rather than left representable and unexamined.",
        )?;
        self.add_recursive_def(
            "def ir_const_eval_bare_cons_fails_closed : Eq IRStepResult (ir_const_eval (IRTy.enum_ ir_d13) (ir_cs1 (IRConst.int_ ir_d1))) (IRStepResult.fault (IROutcome.type_error IRFault.not_agg)) := Eq.refl IRStepResult (IRStepResult.fault (IROutcome.type_error IRFault.not_agg))",
            "FAIL-CLOSED: the same for a bare vcons node.",
        )?;
        self.add_recursive_def(
            "def ir_const_agg_nonspine_has_no_fields : Eq IRStepResult (ir_ef_at (ir_const_value (IRConst.aggv (IRConst.int_ ir_d3))) ir_d0) (IRStepResult.fault (IROutcome.type_error IRFault.bad_field)) := Eq.refl IRStepResult (IRStepResult.fault (IROutcome.type_error IRFault.bad_field))",
            "The remaining junk inhabitant, run: an aggregate whose element list is not a spine \
             (`aggv (int_ 3)`) materializes to a value with zero fields, so ExtractField on it \
             is bad_field. Same fail-closed reading IRScalar's module doc records for its own \
             non-spine payloads, now reachable from the CONSTANT side too.",
        )?;
        self.add_recursive_def(
            "def ir_const_agg_empty : Eq IRScalar (ir_const_value (IRConst.aggv ir_cs0)) (IRScalar.aggv IRScalar.vnil) := Eq.refl IRScalar (IRScalar.aggv IRScalar.vnil)",
            "`Constant::Aggregate(vec![])` — the zero-element aggregate — materializes to the \
             empty aggregate value.",
        )?;
        self.add_recursive_def(
            "def ir_const_agg_two_elements : Eq IRScalar (ir_const_value (IRConst.aggv (ir_cs2 (IRConst.int_ ir_d7) (IRConst.bool_ Bool.true)))) (IRScalar.aggv (ir_sp2 (IRScalar.int_ ir_d7) (IRScalar.bool_ Bool.true))) := Eq.refl IRScalar (IRScalar.aggv (ir_sp2 (IRScalar.int_ ir_d7) (IRScalar.bool_ Bool.true)))",
            "The spine is materialized RECURSIVELY and heterogeneously: a two-element aggregate \
             with an integer and a boolean element becomes the corresponding two-element value \
             spine. The emitted fragment only ever needs arity one, so this is the case that \
             shows the recursion is real rather than a one-element special case.",
        )?;
        self.add_recursive_def(
            "def ir_const_agg_nested : Eq IRScalar (ir_const_value (IRConst.aggv (ir_cs1 (IRConst.aggv (ir_cs1 (IRConst.int_ ir_d2)))))) (IRScalar.aggv (ir_sp1 (IRScalar.aggv (ir_sp1 (IRScalar.int_ ir_d2))))) := Eq.refl IRScalar (IRScalar.aggv (ir_sp1 (IRScalar.aggv (ir_sp1 (IRScalar.int_ ir_d2)))))",
            "NESTING DEPTH TWO. Measured, no body in clean-kernel's flippable set emits a nested \
             aggregate constant — depth is one everywhere — so this witness is deliberately \
             beyond the emitted fragment: the semantics is defined by structural recursion, not \
             by the shape that happened to be needed, and the kernel executes it to prove so.",
        )?;

        Ok(())
    }
}
