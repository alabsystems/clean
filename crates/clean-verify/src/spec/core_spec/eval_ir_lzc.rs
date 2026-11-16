// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Phase A of retiring the authored deref model: the deref's OWN emitted
//! body, minted beside `is_zero` from the same dump — and the stuck site one
//! call deeper.**
//!
//! `ir_lz_module` (`eval_ir_level_minted.rs`) is the designated target alone:
//! it CALLS `<LevelArc as Deref>::deref` and does not define it, so the `Max`
//! and `IMax` arms halt `IROutcome.stuck IRFault.no_func` at the call itself
//! ("the kernel executed eight steps", `eval_ir_level_minted.rs:142`).
//! `ir_lzb_module` (`eval_ir_lzb.rs`) closes that by putting an AUTHORED model
//! of the deref beside the minted body — the residual assumption of the whole
//! chain.
//!
//! **`ir_lzc_module` is the third position, and it assumes nothing.** Both
//! functions are MINTED, from one reader-A projection of one dump: function 0
//! is `level::Level::is_zero` re-minted under `ir_lzc_*` names, function 1 is
//! `<LevelArc as Deref>::deref`'s own six-instruction body as the compiler
//! emits it. The module also carries the first non-empty globals list in this
//! programme — the 34-byte `expect` message the deref hands to
//! `Option::expect`.
//!
//! ## What the module is, and what it still cannot run
//!
//! The emitted deref is `call 2` (`Option::as_deref`), `globaladdr 0`,
//! `const u64 34`, `ptrfromparts`, `call 3` (`Option::expect`), `ret`. Its two
//! callees are DECLARATIONS in the crate artifact — headers with no
//! instructions (`dump-control:120627` and `:117847`) — so this module defines
//! functions 0 and 1 and calls 2 and 3 without defining them.
//!
//! So `ir_lzc` does not answer `Max` either. What changed is WHERE it stops:
//! `ir_lz` is stuck at the `call 1` in the root's own `b4`; `ir_lzc` resolves
//! that call, pushes the deref frame, and is stuck at THAT frame's first
//! instruction, `call 2`. One call deeper, and the arms are named for it —
//! `ir_lzc_on_max_stuck_in_deref`, not `..._stuck`. The step counts pin the
//! difference by computation: `ir_lzc_max_running_at_8` says the machine is
//! still RUNNING where `ir_lz` had already halted, and
//! `ir_lzc_max_stuck_at_9` says it halts one step later.
//!
//! Phase B replaces the two declarations with sidecar-derived bodies; nothing
//! here anticipates that, and no declaration in this file is weakened to make
//! room for it.
//!
//! ## `ir_lzc_func` IS `ir_lz_func`
//!
//! Function 0 is re-minted under new names rather than reused by name, because
//! reusing `ir_lz_tlevel` and `ir_lz_b0..b9` would double-register them. That
//! creates exactly one obligation, and it is discharged as an equation the
//! kernel checks by unfolding both sides:
//! `ir_lzc_func0_is_the_lz_mint : Eq IRFunc ir_lzc_func ir_lz_func`. It is what
//! keeps `ir_lz` BYTE-FROZEN while `ir_lzc` re-mints it: a re-mint that drifted
//! from the frozen projection in any block, any node or any operand fails
//! HERE, at build time.
//!
//! ## The global, and the heap addresses it moves
//!
//! `ir_globals_mem` materialises one live cell per global at the address that
//! IS its id (`eval_ir_machine.rs:1211-1230`), `ir_init` puts those cells at
//! the FRONT of the caller's heap, and `ir_mem_lookup` is head-first
//! (`eval_ir_state.rs:1429-1441`). The global's canonical id is 0, so cell 0
//! of every `ir_lzc` run belongs to the message, not to the caller.
//!
//! `ir_lzm_init_mem_is_mem0` (`eval_ir_fuel.rs:47,64-68`) is the lemma that
//! NAMED this hazard, over a module it cannot fire for: it states the
//! concatenation is the IDENTITY, but only for `ir_lzm_module`, the hand model,
//! which has no globals and will never gain them.
//! `ir_lzc_init_mem` is its twin for the module that DOES declare one — the
//! concat is `cons ir_lzc_g0_cell mem`, NOT the identity — and the shadow set
//! is pinned in BOTH directions rather than in the convenient one:
//! `ir_lzc_global_shadows_cell_zero` (cell 0 IS shadowed, for every `mem`) and
//! `ir_lzc_global_shadows_only_cell_zero` (every other address passes
//! straight through). Together they say the shadow set is exactly `{0}`.
//!
//! That is why every witness heap here is RESTATED off cell 0: the receiver
//! sits at 40, its two `LevelArc` fields at 48 and 56 (the byte offsets the
//! emitted body `gep`s to), and the children where `ir_lzb` put them. `ir_d32`
//! is deliberately not used — it is chain-owned and registered by
//! `eval_ir_bvar_range.rs:185`, which is why `eval_ir_crystal.rs:155-158`
//! leaves a deliberate gap at 32 in the numeral pool. The addresses here stay
//! inside the pool this stage owns.
//!
//! `DerivedProved`, empty axiom closures. Census stays 11: every definition is
//! either a minted literal, an `Eq.refl` the kernel discharges by running the
//! machine, or one `Eq.subst` on a decided `Bool`.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// The minted script, byte for byte what `ir_mint::mint` produces from the
/// committed core under the committed tag table (M3 of
/// `tests/crystal_a2_mint_lzc.rs`).
const MINTED_IR_LZC: &str = include_str!("generated/ir_lzc.defs.txt");

/// One rationale per `def` line, in registration order; the count is asserted
/// against the script so a regenerated script with a different shape fails
/// rather than silently reusing the wrong doc.
const MINTED_IR_LZC_DOCS: &[&str] = &[
    "ir_lzc_tlevel: the Level enum type, enum id 3 (2 before the 2026-10-07 rebaseline) -- the SAME crate id ir_lz_tlevel names, under a NEW alias because registering one name twice is a duplicate. That the two aliases are the same type is not asserted here; it falls out of ir_lzc_func0_is_the_lz_mint, which unfolds both. DerivedProved, zero axiom_deps.",
    "ir_lzc_g0: *** THE FIRST NON-EMPTY GLOBALS LIST IN THIS PROGRAMME. *** The `expect` message, promoted by the producer to a module-table global (dump-control:14998, `global internal @__trust_promoted_4557 [ty.0 x 34] = array[108, 105, ...]`). The 34 int_ bytes ARE the message `live LevelArc must contain a level` -- 108 105 118 101 32 is `live `, and the aggregate is the literal the producer promoted, not a length or a handle. IRGlobal.mk carries an id and a value and NOTHING ELSE: no type slot, no linkage slot, so `[u8 x 34]` and `internal` are pinned in generated/ir_lzc.tags.json and compared by ir_mint::project rather than represented here. Its id 0 IS its address, which is why every heap in this file starts at 40. DerivedProved, zero axiom_deps.",
    "ir_lzc_b0: entry block of the re-minted root -- load the Level, extractfield the u8 discriminant, four-case switch with IMax on the DEFAULT edge and exhaustive_enum_unreachable FALSE. Identical to ir_lz_b0 under the prefix; the equation below is what says so. DerivedProved, zero axiom_deps.",
    "ir_lzc_b1: Zero => true, br to the join b6. DerivedProved, zero axiom_deps.",
    "ir_lzc_b2: Succ => false, br b6. DerivedProved, zero axiom_deps.",
    "ir_lzc_b3: Param => false, br b6 -- its own block as emitted. DerivedProved, zero axiom_deps.",
    "ir_lzc_b4: the Max arm. gep the receiver to byte offsets 8 and 16, call 1 (the deref) on the first, call 0 (self) on its result, condbr to b7 or b8. Over ir_lz_module the call-1 site is where the machine goes stuck; over THIS module it resolves, and the stuck site moves inside the callee. DerivedProved, zero axiom_deps.",
    "ir_lzc_b5: the IMax arm, reached through the switch DEFAULT. gep to offset 16 only -- the impredicative collapse -- then call 1, call 0, br b6. DerivedProved, zero axiom_deps.",
    "ir_lzc_b6: the return join, taking a bool block parameter and returning it. DerivedProved, zero axiom_deps.",
    "ir_lzc_b7: Max, right operand: call 1 (deref) on the offset-16 pointer, call 0 (self), br b9. DerivedProved, zero axiom_deps.",
    "ir_lzc_b8: Max, short-circuit false. DerivedProved, zero axiom_deps.",
    "ir_lzc_b9: the inner join for the && -- a bool block parameter forwarded to b6. DerivedProved, zero axiom_deps.",
    "ir_lzc_func: Level::is_zero as EvalIR, id 0, one ptr parameter, entry b0, ten blocks. Re-minted from the same reader-A projection ir_lz_func was minted from, and TIED to it by ir_lzc_func0_is_the_lz_mint rather than trusted to match. DerivedProved, zero axiom_deps.",
    "ir_lad_b0: *** THE DEREF'S OWN EMITTED BODY -- NOT A MODEL. *** Six instructions, one block, read off dump-control:83740-83751: call 2 (std::option::Option::<T>::as_deref) on the receiver, globaladdr 0 (the message), const u64 34 (its length), ptrfromparts building the &str fat pointer from those two, call 3 (std::option::Option::<T>::expect) on the pair, ret. Compare ir_lzb_deref_b0, which is an ASSUMPTION with seven authored nodes: this block assumes nothing about as_deref or expect, and correspondingly computes nothing about them -- both callees are DECLARATIONS in the crate artifact (headers with no instructions), so this frame goes stuck at its first node. That is Phase A: the assumption is replaced by the emitted text, and the residual moves from `what does the deref do` to `what do its two callees do`. DerivedProved, zero axiom_deps.",
    "ir_lad_func: the deref as a function at canonical id 1 -- the id the root's three `call 1` sites name, pinned to <level::LevelArc as std::ops::Deref>::deref (crate id 3894) by generated/ir_lzc.tags.json's funcs lane. One ptr parameter, one block, entry b0. DerivedProved, zero axiom_deps.",
    "ir_lzc_module: TWO minted functions and ONE minted global -- the first module in this programme that carries a global, and the first whose second function is emitted rather than authored. It calls functions 2 and 3 that it does not define, so, exactly like ir_lz_module, it is representation-equal to the artifact and is NOT a module A4 holds over. The difference from ir_lz_module is where it stops, and ir_lzc_max_running_at_8 / ir_lzc_max_stuck_at_9 measure that difference rather than describing it. DerivedProved, zero axiom_deps.",
];

/// The receiver, at cell 40 rather than at cell 0: the module's global occupies
/// cell 0 (`ir_lzc_global_shadows_cell_zero`).
const ARGS0: &str = "(ir_vl1 (IRScalar.ptr_ ir_d40))";

/// The next free address for the whole file. Inert -- no body here allocas --
/// and above every address any heap below uses (56), so it cannot collide.
const NA: &str = "ir_d57";

const HEAP_ZERO: &str = "(ir_cell ir_d40 (ir_var ir_d0 ir_sp0) ir_mem0)";
const HEAP_SUCC: &str = "(ir_cell ir_d40 (ir_var ir_d1 (ir_sp1 (IRScalar.ptr_ ir_d1))) (ir_cell ir_d48 (IRScalar.ptr_ ir_d1) (ir_cell ir_d17 (ir_var ir_d0 ir_sp0) ir_mem0)))";
const HEAP_PARAM: &str = "(ir_cell ir_d40 (ir_var ir_d4 (ir_sp1 (IRScalar.int_ n))) ir_mem0)";
const HEAP_MAXZZ: &str = "(ir_cell ir_d40 (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ ir_d1) (IRScalar.ptr_ ir_d2))) (ir_cell ir_d48 (IRScalar.ptr_ ir_d1) (ir_cell ir_d56 (IRScalar.ptr_ ir_d2) (ir_cell ir_d17 (ir_var ir_d0 ir_sp0) (ir_cell ir_d18 (ir_var ir_d0 ir_sp0) ir_mem0)))))";
const HEAP_IMAXPZ: &str = "(ir_cell ir_d40 (ir_var ir_d3 (ir_sp2 (IRScalar.ptr_ ir_d1) (IRScalar.ptr_ ir_d2))) (ir_cell ir_d48 (IRScalar.ptr_ ir_d1) (ir_cell ir_d56 (IRScalar.ptr_ ir_d2) (ir_cell ir_d17 (ir_var ir_d4 (ir_sp1 (IRScalar.int_ n))) (ir_cell ir_d18 (ir_var ir_d0 ir_sp0) ir_mem0)))))";

const RET_TRUE: &str = "(IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true)))";
const RET_FALSE: &str = "(IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false)))";
const STUCK_NO_FUNC: &str = "(IROutcome.stuck IRFault.no_func)";

/// The memory `ir_init` hands the machine, spelled as the cons it really is.
const G0_CONS: &str = "(@IRList.cons IRMemSlot ir_lzc_g0_cell mem)";

fn run(fid: &str, args: &str, heap: &str) -> String {
    format!("(ir_eval ir_fuel ir_lzc_module {fid} {args} {heap} {NA})")
}

fn init(heap: &str) -> String {
    format!("(ir_init ir_lzc_module ir_d0 {ARGS0} {heap} {NA})")
}

/// The initial configuration of the Max(Zero, Zero) run that
/// `ir_lzc_max_running_at_8` / `ir_lzc_max_stuck_at_9` are stated at. Exposed so
/// the stacking split's R and F witnesses (`eval_ir_stack_split.rs`) cite the
/// SAME term those two theorems name, not a retyped copy that could drift.
pub(super) fn lzc_maxzz_init() -> String {
    init(HEAP_MAXZZ)
}

/// A witness proved by `Eq.refl`: the kernel runs the machine and compares.
fn witness(name: &str, binder: &str, fid: &str, args: &str, heap: &str, out: &str) -> String {
    format!(
        "def {name} {binder}: @Eq IROutcome {} {out} := @Eq.refl IROutcome {out}",
        run(fid, args, heap)
    )
}

impl Specification {
    /// Phase A's two-minted-function module, the global it carries, the shadow
    /// set that global creates, and the five arms. Needs the IR types, the
    /// numerals, the builders, `ir_fuel` and `ir_lz_func`, so it belongs to the
    /// `EvalIr` bundle and is called from `add_eval_ir_crystal` AFTER
    /// `add_eval_ir_lzb_module` — `ir_lzc_func0_is_the_lz_mint` names
    /// `ir_lz_func`, which is a hard ordering dependency.
    ///
    /// # Errors
    /// Returns `SpecError` if the minted script and the rationale table
    /// disagree in length, or if any declaration fails to elaborate or
    /// kernel-check.
    pub(super) fn add_eval_ir_lzc_module(&mut self) -> Result<(), SpecError> {
        let minted: Vec<&str> = MINTED_IR_LZC
            .lines()
            .map(str::trim)
            .filter(|l| !l.is_empty())
            .collect();
        if minted.len() != MINTED_IR_LZC_DOCS.len() {
            return Err(SpecError::EnvError(format!(
                "the minted ir_lzc script has {} definitions but {} rationales are declared; \
                 regenerate the docs table with the script rather than reusing it",
                minted.len(),
                MINTED_IR_LZC_DOCS.len()
            )));
        }
        for (line, doc) in minted.iter().zip(MINTED_IR_LZC_DOCS) {
            self.add_recursive_def(line, doc)?;
        }

        self.add_recursive_def(
            "def ir_lzc_func0_is_the_lz_mint : @Eq IRFunc ir_lzc_func ir_lz_func := @Eq.refl IRFunc ir_lz_func",
            "ir_lzc_func0_is_the_lz_mint: *** THE EQUATION THAT KEEPS ir_lz BYTE-FROZEN WHILE ir_lzc RE-MINTS IT. *** Function 0 of this chain is the designated target under NEW names -- ir_lzc_tlevel for ir_lz_tlevel, ir_lzc_b0..b9 for ir_lz_b0..b9 -- because re-using the old names would register each of them twice. @Eq.refl makes the kernel unfold both sides through delta and compare the whole function: every block, every node, every operand, the switch table and its exhaustive flag. A re-mint that drifted from the frozen projection anywhere fails HERE, at build time, rather than leaving two `is_zero` terms in the environment that nothing compares. DerivedProved, zero axiom_deps.",
        )?;

        for (name, idx, tgt, doc) in [
            (
                "ir_lzc_func1_is_the_minted_deref",
                "ir_d1",
                "(@IROption.some IRFunc ir_lad_func)",
                "ir_lzc_func1_is_the_minted_deref: id 1 of this module resolves to the deref's OWN EMITTED BODY. This is the one structural difference from ir_lz_module and the whole point of the chain: over ir_lz_module ir_func_find returns none at id 1 and ir_call_exec halts stuck; here it returns the minted ir_lad_func. Note what is NOT claimed -- that the frame it pushes computes anything. It does not; see ir_lzc_callee2_is_a_declaration. DerivedProved, zero axiom_deps.",
            ),
            (
                "ir_lzc_callee2_is_a_declaration",
                "ir_d2",
                "(@IROption.none IRFunc)",
                "ir_lzc_callee2_is_a_declaration: *** THE HONEST PHASE-A STATEMENT. *** id 2 is std::option::Option::<T>::as_deref, which the crate artifact carries as a HEADER WITH NO INSTRUCTIONS (dump-control:120627, `rustcc fn @std::option::Option::<T>::as_deref(functy.900) {}`). It is not in this module's function list, so ir_func_find returns none and the deref frame goes stuck at its first node. Registered as an equation rather than left implicit, because it is the precise residual Phase B has to retire: not `what does the deref do` any more, but `what do these two declarations do`. DerivedProved, zero axiom_deps.",
            ),
            (
                "ir_lzc_callee3_is_a_declaration",
                "ir_d3",
                "(@IROption.none IRFunc)",
                "ir_lzc_callee3_is_a_declaration: id 3 is std::option::Option::<T>::expect (dump-control:117847, functy.896), the other declaration. NEVER REACHED in Phase A -- the frame is already stuck at call 2 -- so this equation is about the module's shape, not about a run. DerivedProved, zero axiom_deps.",
            ),
        ] {
            self.add_recursive_def(
                &format!("def {name} : @Eq (IROption IRFunc) (ir_func_find (ir_mod_funcs ir_lzc_module) {idx}) {tgt} := @Eq.refl (IROption IRFunc) {tgt}"),
                doc,
            )?;
        }

        self.add_recursive_def(
            "def ir_lzc_global_is_declared : @Eq (IROption IRGlobal) (ir_global_find (ir_mod_globals ir_lzc_module) ir_d0) (@IROption.some IRGlobal ir_lzc_g0) := @Eq.refl (IROption IRGlobal) (@IROption.some IRGlobal ir_lzc_g0)",
            "ir_lzc_global_is_declared: ir_global_find resolves id 0 of this module's globals list to the message. The globals half of the func_find equations above, and the premise ir_globaladdr_eval discharges. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            "def ir_lzc_globaladdr_evals : @Eq IRStepResult (ir_globaladdr_eval ir_lzc_module ir_d0) (IRStepResult.value (IRScalar.ptr_ ir_d0)) := @Eq.refl IRStepResult (IRStepResult.value (IRScalar.ptr_ ir_d0))",
            "ir_lzc_globaladdr_evals: the deref's second instruction, EXECUTED. `globaladdr 0` yields ptr 0 -- a global's id IS its address, which is exactly what ir_init's cell materialisation makes true. This is a POSITIVE globaladdr equation and it is NEW: the only precedent in the tree, ir_w2c_ga_no_global (eval_ir_w2c_synth.rs:155), is the NEGATIVE one -- the no_global fault on a module that declares nothing. Nothing before this chain had a global to address. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            "def ir_lzc_g0_cell : IRMemSlot := @IRGlobal.rec (fun (_ : IRGlobal) => IRMemSlot) (fun (i : Nat) (c : IRConst) => IRMemSlot.mk i (ir_const_value c) Bool.true) ir_lzc_g0",
            "ir_lzc_g0_cell: the memory cell ir_globals_mem materialises for this global -- live, at the address that is its id, holding ir_const_value of the promoted aggregate. Spelled through @IRGlobal.rec rather than as a literal so that a change to the global's id or value moves the cell with it instead of leaving a stale copy beside it. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            &format!("def ir_lzc_init_mem (mem : IRList IRMemSlot) : @Eq (IRList IRMemSlot) (ir_mem_concat (ir_globals_mem (ir_mod_globals ir_lzc_module)) mem) {G0_CONS} := @Eq.refl (IRList IRMemSlot) {G0_CONS}"),
            "ir_lzc_init_mem: *** THE TWIN OF ir_lzm_init_mem_is_mem0, FOR THE MODULE THAT DOES DECLARE A GLOBAL. *** That lemma (eval_ir_fuel.rs:47,64-68) states that ir_init's globals concatenation is the IDENTITY on the caller heap, and says in its own rationale that it exists so it STOPS REDUCING when a module with globals arrives. That alarm is quantified over ir_lzm_module alone, which has no globals and never will, so it did NOT fire when this module arrived -- ir_lzc_module is a separate constant, and this twin is written, not triggered; the alarm's value was the sentence in its rationale, not an automatic refusal. The concat here is NOT the identity: it is one cons, the message cell in front of whatever heap the caller supplied, for every mem. Stated rather than discovered, so no theorem over this module can quietly assume the caller's heap is what the machine sees. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            &format!("def ir_lzc_global_shadows_cell_zero (mem : IRList IRMemSlot) : @Eq (IROption IRMemSlot) (ir_mem_lookup {G0_CONS} ir_d0) (@IROption.some IRMemSlot ir_lzc_g0_cell) := @Eq.refl (IROption IRMemSlot) (@IROption.some IRMemSlot ir_lzc_g0_cell)"),
            "ir_lzc_global_shadows_cell_zero: cell 0 IS shadowed -- for EVERY caller heap, the lookup at address 0 returns the message cell and never reaches mem. Half of `the shadow set is exactly {0}`, and the half a one-directional passthrough lemma would leave unproved: without it, `only cell zero` would be consistent with the global shadowing NOTHING. ir_mem_lookup is head-first (eval_ir_state.rs:1429-1441) and ir_nat_eqb 0 0 is true, so Eq.refl. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            &format!("def ir_lzc_global_shadows_only_cell_zero (mem : IRList IRMemSlot) (a : Nat) (h : @Eq Bool (ir_nat_eqb ir_d0 a) Bool.false) : @Eq (IROption IRMemSlot) (ir_mem_lookup {G0_CONS} a) (ir_mem_lookup mem a) := @Eq.subst Bool (fun (b : Bool) => @Eq (IROption IRMemSlot) (@Bool.rec (fun (_ : Bool) => IROption IRMemSlot) (ir_mem_lookup mem a) (@IROption.some IRMemSlot ir_lzc_g0_cell) b) (ir_mem_lookup mem a)) Bool.false (ir_nat_eqb ir_d0 a) (@Eq.symm Bool (ir_nat_eqb ir_d0 a) Bool.false h) (@Eq.refl (IROption IRMemSlot) (ir_mem_lookup mem a))"),
            "ir_lzc_global_shadows_only_cell_zero: and NOTHING ELSE is shadowed -- at every address the machine decides is not 0, the lookup passes straight through to the caller's heap, for every mem. The other half of `exactly {0}`. Not an Eq.refl: `a` is abstract, so ir_mem_lookup is stuck at the @Bool.rec on ir_nat_eqb 0 a, and the hypothesis is substituted INTO that scrutinee position -- @Eq.subst at the Bool motive, with the refl at the false minor. Together with ir_lzc_global_shadows_cell_zero this is what licenses the restated heaps below: put the receiver anywhere but 0 and the global is invisible to it. DerivedProved, zero axiom_deps.",
        )?;

        for (name, binder, heap, out, doc) in [
            ("ir_lzc_on_zero", "", HEAP_ZERO, RET_TRUE, "ir_lzc_on_zero: Zero is true, with the receiver at cell 40 and the message occupying cell 0. The constant arms never reach a call, so they answer the same over all three modules (ir_lz, ir_lzb, ir_lzc); this witness is what says the global and the moved heap did not disturb them. DerivedProved, zero axiom_deps."),
            ("ir_lzc_on_succ", "", HEAP_SUCC, RET_FALSE, "ir_lzc_on_succ: Succ(Zero) is false. The edge is present in the heap -- at the field cell 48 and inline -- and is still not followed, so a semantics that wrongly recursed would return true here and fail to typecheck. DerivedProved, zero axiom_deps."),
            ("ir_lzc_on_param", "(n : Nat) ", HEAP_PARAM, RET_FALSE, "ir_lzc_on_param: Param n is false for EVERY n, through the emitted body's own b3. DerivedProved, zero axiom_deps."),
            ("ir_lzc_on_max_stuck_in_deref", "", HEAP_MAXZZ, STUCK_NO_FUNC, "ir_lzc_on_max_stuck_in_deref: *** SAME FAULT AS ir_lz_on_max_stuck, ONE CALL DEEPER. *** Max(Zero, Zero) halts IROutcome.stuck IRFault.no_func -- but not at the same place, and the name says which. Over ir_lz_module the machine dies at b4's `call 1`, the deref itself (eval_ir_level_minted.rs:142: eight steps). Here that call RESOLVES: ir_func_find returns ir_lad_func, the frame is pushed, and the machine dies at the FIRST NODE OF THAT FRAME, `call 2` to std::option::Option::<T>::as_deref -- a declaration with no body. The outcome is identical and the state is not; ir_lzc_max_running_at_8 and ir_lzc_max_stuck_at_9 are what tell them apart, by computation. DerivedProved, zero axiom_deps."),
            ("ir_lzc_on_imax_stuck_in_deref", "(n : Nat) ", HEAP_IMAXPZ, STUCK_NO_FUNC, "ir_lzc_on_imax_stuck_in_deref: IMax(Param n, Zero) likewise, for every n, through the switch DEFAULT edge to b5 -- which geps to offset 16 only and calls the deref on it. Stuck inside the deref frame, at call 2, exactly as the Max arm is. DerivedProved, zero axiom_deps."),
        ] {
            self.add_recursive_def(&witness(name, binder, "ir_d0", ARGS0, heap, out), doc)?;
        }

        Ok(())
    }

    /// The two configuration equations that locate the stuck site. A separate
    /// stage for the same reason as `add_eval_ir_lzb_steps`: they are the only
    /// `ir_lzc` declarations that name `ir_steps`, which `add_eval_ir_steps`
    /// registers — and that stage runs AFTER `add_eval_ir`, inside which
    /// `add_eval_ir_lzc_module` is called. Registered together with the module,
    /// the missing head surfaces as a bogus arity error rather than an unknown
    /// identifier.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check. A wrong step count fails HERE, by computation.
    pub(super) fn add_eval_ir_lzc_steps(&mut self) -> Result<(), SpecError> {
        let running = "IROutcome.fuel_out";
        self.add_recursive_def(
            &format!("def ir_lzc_max_running_at_8 : @Eq IROutcome (ir_config_outcome (ir_steps ir_d8 ir_lzc_module {})) {running} := @Eq.refl IROutcome {running}", init(HEAP_MAXZZ)),
            "ir_lzc_max_running_at_8: *** STILL RUNNING WHERE ir_lz HAD ALREADY HALTED. *** ir_config_outcome reads fuel_out off a RUNNING configuration and the real outcome off a halted one, so this equation says the machine has not halted after eight steps. Eight is where ir_lz_on_max_stuck dies (eval_ir_level_minted.rs:142). Registered because ir_lzc_max_stuck_at_9 alone would NOT pin the depth: a halted configuration is a fixed point of ir_steps, so an `= halted` equation at 9 is implied by halting at 8, at 7, at anything below. This is the direction that makes the pair exact. DerivedProved, zero axiom_deps.",
        )?;
        let tgt = "(IRConfig.halted (IROutcome.stuck IRFault.no_func))";
        self.add_recursive_def(
            &format!("def ir_lzc_max_stuck_at_9 : @Eq IRConfig (ir_steps ir_d9 ir_lzc_module {}) {tgt} := @Eq.refl IRConfig {tgt}", init(HEAP_MAXZZ)),
            "ir_lzc_max_stuck_at_9: *** AND HALTED AT NINE. *** The ninth step is the deref frame's first instruction, `call 2`, and it goes stuck no_func. With ir_lzc_max_running_at_8 above, the pair pins THIS module's stuck site exactly: running at 8, halted at 9 -- step 8 is the call that now resolves and pushes the frame, step 9 is the call inside it that does not. BOTH of those numbers are computed by the kernel, not asserted; an off-by-one is a build failure. The COMPARISON to ir_lz is only half computed, and is stated that way on purpose: ir_lz's 8 is a PROSE figure in ir_lz_on_max_stuck's rationale (eval_ir_level_minted.rs:142, `the kernel executed eight steps`) -- no ir_lz_*_at_8 declaration exists anywhere in core_spec, so nothing kernel-checks it. It is re-derivable by counting the emitted body: b0's load/extractfield/switch are steps 1-3, and b4's const/gep/const/gep put `call 1` at step 8 (generated/ir_lz.defs.txt, ir_lz_b0 and ir_lz_b4). Registering ir_lz_max_stuck_at_8 beside this pair would make `one step deeper` computed end to end, but it would add a stage to the FROZEN ir_lz chain, so it is an owner call rather than a Phase-A edit. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The script registered here is exactly the one the A2 gate regenerates.
    #[test]
    fn test_minted_lzc_script_is_the_registered_one() {
        assert_eq!(MINTED_IR_LZC, crate::ir_mint::IR_LZC_DEFS);
        assert_eq!(
            MINTED_IR_LZC
                .lines()
                .filter(|l| !l.trim().is_empty())
                .count(),
            MINTED_IR_LZC_DOCS.len()
        );
    }

    /// The two things that make this chain different from `ir_lz`: a second
    /// DEFINED function, and a non-empty globals list.
    #[test]
    fn test_minted_lzc_script_defines_the_deref_and_a_global() {
        let s = MINTED_IR_LZC;
        assert!(
            s.contains("def ir_lad_func : IRFunc :="),
            "the deref is a body"
        );
        assert!(
            s.contains("IRInst.call ir_d2 (ir_nl1 ir_d0)")
                && s.contains("IRInst.call ir_d3 (ir_nl2 ir_d1 ir_d4)"),
            "its two callees are the declarations 2 and 3"
        );
        assert!(
            s.contains("IRInst.globaladdr ir_d0"),
            "it addresses the global"
        );
        assert!(
            s.contains("(@IRList.cons IRGlobal ir_lzc_g0 (@IRList.nil IRGlobal))"),
            "and the module declares it"
        );
        assert!(
            !s.contains("IRInst.assert") && !s.contains("IRConst.null_"),
            "nothing authored: the ir_lzb model's null check is not in an emitted body"
        );
    }

    /// Every witness heap stays off cell 0, which the module's global owns.
    #[test]
    fn test_witness_heaps_avoid_the_shadowed_cell() {
        for heap in [HEAP_ZERO, HEAP_SUCC, HEAP_PARAM, HEAP_MAXZZ, HEAP_IMAXPZ] {
            assert!(
                heap.starts_with("(ir_cell ir_d40 "),
                "the receiver must sit at cell 40: {heap}"
            );
            assert!(
                !heap.contains("(ir_cell ir_d0 "),
                "no witness heap may claim the cell the global shadows: {heap}"
            );
        }
        assert!(ARGS0.contains("ir_d40"));
    }

    #[test]
    fn test_sources_balanced_ascii() {
        let generated = [
            witness("w", "", "ir_d0", ARGS0, HEAP_MAXZZ, STUCK_NO_FUNC),
            init(HEAP_IMAXPZ),
        ];
        for src in [MINTED_IR_LZC, ARGS0, G0_CONS]
            .into_iter()
            .chain(generated.iter().map(String::as_str))
        {
            assert!(src.is_ascii(), "spec sources stay ASCII");
            assert_eq!(src.matches('(').count(), src.matches(')').count());
        }
    }
}
