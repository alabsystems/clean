// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Execution vocabulary and shared literal builders, without Crystal examples.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// Install the existing execution semantics and generic producer helpers.
    /// Historical kernel-model examples are installed only by `add_eval_ir`.
    pub(super) fn add_eval_ir_execution(&mut self) -> Result<(), SpecError> {
        self.add_eval_ir_syntax()?;
        self.add_eval_ir_state()?;
        self.add_eval_ir_ops()?;
        self.add_eval_ir_machine()?;
        self.add_eval_ir_numerals()?;
        self.add_eval_ir_builders()
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

        // ── the 2026-09-16 widening: ir_d65..ir_d130 (64 is already taken) ──
        //
        // STRUCTURAL slots only, and that distinction is the whole safety
        // argument. `mint::nat` (SSA ids, block ids, function ids, aggregate
        // interning ids) draws from THIS pool; `mint::nat_data` draws from a
        // SEPARATE one whose cutoff deliberately stays at 16, and it is the DATA
        // cutoff whose widening would respell landed artifacts -- `ir_mt`'s
        // committed defs spell `IRConst.int_ 63` and `IRConst.int_ 64` as RAW
        // literals, which is what that separation buys.
        //
        // So no committed chain changes: a structural index at or above 64 could
        // not have been minted under the old bound, so none exists to respell.
        // Byte-identity of every landed artifact is the widening's own
        // regression gate and the crystal_a2_mint_* m3 arms are where it runs.
        //
        // 130 is the max SSA result id of `tc::heartbeat::tick_heartbeat`, the
        // callee whose absence makes infer_type's transitive closure cyclic; the
        // designated target's own body reaches 39.
        // ir_d64 is NOT defined here: `eval_ir_valid_char.rs` already registers it
        // as `Nat.add ir_d32 ir_d32` -- the machine WIDTH -- and three files assert
        // it is defined exactly once. It is definitionally 64, so the mint's atom
        // name resolves; this pool simply chains 65 onward from it. The first
        // attempt at this widening redefined it and the spec refused to build,
        // which is how the collision surfaced.
        // 65 is built from 63, NOT from ir_d64: `eval_ir_valid_char.rs` owns that
        // name (as `Nat.add ir_d32 ir_d32`, the machine WIDTH) and registers it in
        // a LATER stage, so it is not in scope here. Chaining through it failed
        // with `Unknown identifier: ir_d64` -- an ORDERING fact, not a value one;
        // the two are definitionally equal and the mint's atom name resolves
        // against whichever is in scope at the use site.
        self.add_recursive_def(
            "def ir_d65 : Nat := Nat.succ (Nat.succ ir_d63)",
            "EvalIR numeral 65.",
        )?;
        self.add_recursive_def("def ir_d66 : Nat := Nat.succ ir_d65", "EvalIR numeral 66.")?;
        self.add_recursive_def("def ir_d67 : Nat := Nat.succ ir_d66", "EvalIR numeral 67.")?;
        self.add_recursive_def("def ir_d68 : Nat := Nat.succ ir_d67", "EvalIR numeral 68.")?;
        self.add_recursive_def("def ir_d69 : Nat := Nat.succ ir_d68", "EvalIR numeral 69.")?;
        self.add_recursive_def("def ir_d70 : Nat := Nat.succ ir_d69", "EvalIR numeral 70.")?;
        self.add_recursive_def("def ir_d71 : Nat := Nat.succ ir_d70", "EvalIR numeral 71.")?;
        self.add_recursive_def("def ir_d72 : Nat := Nat.succ ir_d71", "EvalIR numeral 72.")?;
        self.add_recursive_def("def ir_d73 : Nat := Nat.succ ir_d72", "EvalIR numeral 73.")?;
        self.add_recursive_def("def ir_d74 : Nat := Nat.succ ir_d73", "EvalIR numeral 74.")?;
        self.add_recursive_def("def ir_d75 : Nat := Nat.succ ir_d74", "EvalIR numeral 75.")?;
        self.add_recursive_def("def ir_d76 : Nat := Nat.succ ir_d75", "EvalIR numeral 76.")?;
        self.add_recursive_def("def ir_d77 : Nat := Nat.succ ir_d76", "EvalIR numeral 77.")?;
        self.add_recursive_def("def ir_d78 : Nat := Nat.succ ir_d77", "EvalIR numeral 78.")?;
        self.add_recursive_def("def ir_d79 : Nat := Nat.succ ir_d78", "EvalIR numeral 79.")?;
        self.add_recursive_def("def ir_d80 : Nat := Nat.succ ir_d79", "EvalIR numeral 80.")?;
        self.add_recursive_def("def ir_d81 : Nat := Nat.succ ir_d80", "EvalIR numeral 81.")?;
        self.add_recursive_def("def ir_d82 : Nat := Nat.succ ir_d81", "EvalIR numeral 82.")?;
        self.add_recursive_def("def ir_d83 : Nat := Nat.succ ir_d82", "EvalIR numeral 83.")?;
        self.add_recursive_def("def ir_d84 : Nat := Nat.succ ir_d83", "EvalIR numeral 84.")?;
        self.add_recursive_def("def ir_d85 : Nat := Nat.succ ir_d84", "EvalIR numeral 85.")?;
        self.add_recursive_def("def ir_d86 : Nat := Nat.succ ir_d85", "EvalIR numeral 86.")?;
        self.add_recursive_def("def ir_d87 : Nat := Nat.succ ir_d86", "EvalIR numeral 87.")?;
        self.add_recursive_def("def ir_d88 : Nat := Nat.succ ir_d87", "EvalIR numeral 88.")?;
        self.add_recursive_def("def ir_d89 : Nat := Nat.succ ir_d88", "EvalIR numeral 89.")?;
        self.add_recursive_def("def ir_d90 : Nat := Nat.succ ir_d89", "EvalIR numeral 90.")?;
        self.add_recursive_def("def ir_d91 : Nat := Nat.succ ir_d90", "EvalIR numeral 91.")?;
        self.add_recursive_def("def ir_d92 : Nat := Nat.succ ir_d91", "EvalIR numeral 92.")?;
        self.add_recursive_def("def ir_d93 : Nat := Nat.succ ir_d92", "EvalIR numeral 93.")?;
        self.add_recursive_def("def ir_d94 : Nat := Nat.succ ir_d93", "EvalIR numeral 94.")?;
        self.add_recursive_def("def ir_d95 : Nat := Nat.succ ir_d94", "EvalIR numeral 95.")?;
        self.add_recursive_def("def ir_d96 : Nat := Nat.succ ir_d95", "EvalIR numeral 96.")?;
        self.add_recursive_def("def ir_d97 : Nat := Nat.succ ir_d96", "EvalIR numeral 97.")?;
        self.add_recursive_def("def ir_d98 : Nat := Nat.succ ir_d97", "EvalIR numeral 98.")?;
        self.add_recursive_def("def ir_d99 : Nat := Nat.succ ir_d98", "EvalIR numeral 99.")?;
        self.add_recursive_def(
            "def ir_d100 : Nat := Nat.succ ir_d99",
            "EvalIR numeral 100.",
        )?;
        self.add_recursive_def(
            "def ir_d101 : Nat := Nat.succ ir_d100",
            "EvalIR numeral 101.",
        )?;
        self.add_recursive_def(
            "def ir_d102 : Nat := Nat.succ ir_d101",
            "EvalIR numeral 102.",
        )?;
        self.add_recursive_def(
            "def ir_d103 : Nat := Nat.succ ir_d102",
            "EvalIR numeral 103.",
        )?;
        self.add_recursive_def(
            "def ir_d104 : Nat := Nat.succ ir_d103",
            "EvalIR numeral 104.",
        )?;
        self.add_recursive_def(
            "def ir_d105 : Nat := Nat.succ ir_d104",
            "EvalIR numeral 105.",
        )?;
        self.add_recursive_def(
            "def ir_d106 : Nat := Nat.succ ir_d105",
            "EvalIR numeral 106.",
        )?;
        self.add_recursive_def(
            "def ir_d107 : Nat := Nat.succ ir_d106",
            "EvalIR numeral 107.",
        )?;
        self.add_recursive_def(
            "def ir_d108 : Nat := Nat.succ ir_d107",
            "EvalIR numeral 108.",
        )?;
        self.add_recursive_def(
            "def ir_d109 : Nat := Nat.succ ir_d108",
            "EvalIR numeral 109.",
        )?;
        self.add_recursive_def(
            "def ir_d110 : Nat := Nat.succ ir_d109",
            "EvalIR numeral 110.",
        )?;
        self.add_recursive_def(
            "def ir_d111 : Nat := Nat.succ ir_d110",
            "EvalIR numeral 111.",
        )?;
        self.add_recursive_def(
            "def ir_d112 : Nat := Nat.succ ir_d111",
            "EvalIR numeral 112.",
        )?;
        self.add_recursive_def(
            "def ir_d113 : Nat := Nat.succ ir_d112",
            "EvalIR numeral 113.",
        )?;
        self.add_recursive_def(
            "def ir_d114 : Nat := Nat.succ ir_d113",
            "EvalIR numeral 114.",
        )?;
        self.add_recursive_def(
            "def ir_d115 : Nat := Nat.succ ir_d114",
            "EvalIR numeral 115.",
        )?;
        self.add_recursive_def(
            "def ir_d116 : Nat := Nat.succ ir_d115",
            "EvalIR numeral 116.",
        )?;
        self.add_recursive_def(
            "def ir_d117 : Nat := Nat.succ ir_d116",
            "EvalIR numeral 117.",
        )?;
        self.add_recursive_def(
            "def ir_d118 : Nat := Nat.succ ir_d117",
            "EvalIR numeral 118.",
        )?;
        self.add_recursive_def(
            "def ir_d119 : Nat := Nat.succ ir_d118",
            "EvalIR numeral 119.",
        )?;
        self.add_recursive_def(
            "def ir_d120 : Nat := Nat.succ ir_d119",
            "EvalIR numeral 120.",
        )?;
        self.add_recursive_def(
            "def ir_d121 : Nat := Nat.succ ir_d120",
            "EvalIR numeral 121.",
        )?;
        self.add_recursive_def(
            "def ir_d122 : Nat := Nat.succ ir_d121",
            "EvalIR numeral 122.",
        )?;
        self.add_recursive_def(
            "def ir_d123 : Nat := Nat.succ ir_d122",
            "EvalIR numeral 123.",
        )?;
        self.add_recursive_def(
            "def ir_d124 : Nat := Nat.succ ir_d123",
            "EvalIR numeral 124.",
        )?;
        self.add_recursive_def(
            "def ir_d125 : Nat := Nat.succ ir_d124",
            "EvalIR numeral 125.",
        )?;
        self.add_recursive_def(
            "def ir_d126 : Nat := Nat.succ ir_d125",
            "EvalIR numeral 126.",
        )?;
        self.add_recursive_def(
            "def ir_d127 : Nat := Nat.succ ir_d126",
            "EvalIR numeral 127.",
        )?;
        self.add_recursive_def(
            "def ir_d128 : Nat := Nat.succ ir_d127",
            "EvalIR numeral 128.",
        )?;
        self.add_recursive_def(
            "def ir_d129 : Nat := Nat.succ ir_d128",
            "EvalIR numeral 129.",
        )?;
        self.add_recursive_def(
            "def ir_d130 : Nat := Nat.succ ir_d129",
            "EvalIR numeral 130.",
        )?;

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
            "def ir_nl0 : IRList Nat := @IRList.nil Nat",
            "Empty id list.",
        )?;
        self.add_recursive_def(
            "def ir_nl1 (a : Nat) : IRList Nat := @IRList.cons Nat a ir_nl0",
            "One-element id list.",
        )?;
        self.add_recursive_def(
            "def ir_nl2 (a : Nat) (b : Nat) : IRList Nat := @IRList.cons Nat a (ir_nl1 b)",
            "Two-element id list.",
        )?;

        self.add_recursive_def(
            "def ir_vl0 : IRList IRScalar := @IRList.nil IRScalar",
            "Empty value list.",
        )?;
        self.add_recursive_def(
            "def ir_vl1 (a : IRScalar) : IRList IRScalar := @IRList.cons IRScalar a ir_vl0",
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
            "def ir_bd0 : IRList IRNode := @IRList.nil IRNode",
            "Empty node list.",
        )?;
        self.add_recursive_def(
            "def ir_bd1 (a : IRNode) : IRList IRNode := @IRList.cons IRNode a ir_bd0",
            "One-node body.",
        )?;
        self.add_recursive_def(
            "def ir_bd2 (a : IRNode) (b : IRNode) : IRList IRNode := @IRList.cons IRNode a (ir_bd1 b)",
            "Two-node body.",
        )?;
        self.add_recursive_def(
            "def ir_bd3 (a : IRNode) (b : IRNode) (c : IRNode) : IRList IRNode := @IRList.cons IRNode a (ir_bd2 b c)",
            "Three-node body.",
        )?;
        self.add_recursive_def(
            concat!(
                "def ir_bd6 (a : IRNode) (b : IRNode) (c : IRNode) (d : IRNode) (e : IRNode) (f : IRNode) : IRList IRNode := ",
                "@IRList.cons IRNode a (@IRList.cons IRNode b (@IRList.cons IRNode c (ir_bd3 d e f)))",
            ),
            "Six-node body (the Max/IMax arms: extract, null constant, compare, assert, call, \
             terminator).",
        )?;

        self.add_recursive_def(
            "def ir_sc0 : IRList IRSwitchCase := @IRList.nil IRSwitchCase",
            "Empty Switch arm list.",
        )?;
        self.add_recursive_def(
            concat!(
                "def ir_sc (v : Nat) (t : Nat) (rest : IRList IRSwitchCase) : IRList IRSwitchCase := ",
                "@IRList.cons IRSwitchCase (IRSwitchCase.mk v t ir_nl0) rest",
            ),
            "Cons a no-argument Switch arm: selector value v jumps to block t.",
        )?;

        self.add_recursive_def(
            "def ir_blk0 : IRList IRBlock := @IRList.nil IRBlock",
            "Empty block list.",
        )?;
        self.add_recursive_def(
            "def ir_blk (b : IRBlock) (rest : IRList IRBlock) : IRList IRBlock := @IRList.cons IRBlock b rest",
            "Cons a block.",
        )?;

        self.add_recursive_def(
            "def ir_mem0 : IRList IRMemSlot := @IRList.nil IRMemSlot",
            "Empty memory.",
        )?;
        self.add_recursive_def(
            concat!(
                "def ir_cell (a : Nat) (v : IRScalar) (rest : IRList IRMemSlot) : IRList IRMemSlot := ",
                "@IRList.cons IRMemSlot (IRMemSlot.mk a v Bool.true) rest",
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
}
