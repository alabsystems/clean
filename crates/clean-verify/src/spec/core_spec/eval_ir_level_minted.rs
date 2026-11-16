// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The designated target's MINTED module, registered under the chain's
//! name — and the kernel-checked fact that A4 is FALSE over it.**
//!
//! Until 2026-08-22 `ir_lz_module` named a HAND-AUTHORED module: the semantic
//! model of `Level::is_zero` with `<LevelArc as Deref>::deref` inlined as an
//! `extractfield` + null-check + `assert`. The mint
//! (`tests/crystal_a2_mint_lz.rs`, `src/ir_mint`) derived the emitted body
//! mechanically and the two DIFFERED in four classes — the switch table and
//! its exhaustive flag, per-arm `ret` vs join-block `br`, the inlined deref vs
//! `gep` + `call`, and three emitted-only blocks. So the A4/A5 theorems were
//! about a module the compiler does not emit. The decision memo
//! (`designs/2026-08-22-is-zero-model-vs-minted-decision.md`) resolves that by
//! NAMING things for what they are:
//!
//! * the hand model is now `ir_lzm_module` (`eval_ir_crystal.rs`), and
//!   `ir_lzm_correct` / `ir_lzm_machine_sound` are theorems about it;
//! * `ir_lz_module` — THIS file — is the minted module, replayed line for line
//!   from `generated/ir_lz.defs.txt` exactly as every other chain replays its
//!   script, so reader C (`ir_mint::decode`) can check the registered term
//!   against the artifact projection (M4) for the designated target too.
//!
//! ## What is proved about the minted module, and what is refuted
//!
//! The module defines ONE function, `is_zero` (id 0), and CALLS a second —
//! `<LevelArc as Deref>::deref`, canonical index 1 — that is not in the
//! module. `ir_call_exec` resolves a callee through `ir_func_find`, which
//! matches a candidate on its OWN id, so the call halts
//! `IROutcome.stuck IRFault.no_func`: fail-closed, never a misroute (the
//! 2026-08-20 namespace collision that made the deref resolve to `is_zero`
//! itself is closed; `tests/crystal_a2_mint/callee_identity.rs`).
//!
//! | witness | input | outcome, computed by the kernel |
//! |---|---|---|
//! | `ir_lz_on_zero` | `Level::Zero` | `ret [bool true]` |
//! | `ir_lz_on_succ` | `Level::Succ(0)` | `ret [bool false]` |
//! | `ir_lz_on_param` | `Level::Param n`, ∀ n | `ret [bool false]` |
//! | `ir_lz_on_max_stuck` | `Level::Max(0, 0)` | **`stuck no_func`** |
//! | `ir_lz_on_imax_stuck` | `Level::IMax(Param n, 0)`, ∀ n | **`stuck no_func`** |
//!
//! Three of five arms return what `Level::is_zero` returns; the two recursive
//! arms go stuck at the first `call 1`. `ir_lz_minted_refutes_a4_on_max` then
//! states the consequence as a theorem rather than a comment: the A4 sentence
//! (`ir_lzm_correct`'s statement with `ir_lz_module` in place of the model)
//! implies every `C : Type` — it is FALSE — instantiated at the very heap the
//! model's A2 relation accepts for `Max(Zero, Zero)` and at the model's own
//! cost as fuel. Link 4 for the designated target is therefore OPEN, and the
//! page says so; the route that can close it is scoped in the memo (a deref
//! model in the module and a re-derivation over the emitted CFG), and its
//! residual assumption — what `Option::as_deref` + `Option::expect` do — is
//! architectural (rustc has no cross-crate THIR), not a build item.
//!
//! `DerivedProved`, empty axiom closures. Census stays 11: every definition
//! here is either a literal, an `Eq.refl` the kernel discharges by running the
//! machine, or an application of `bool_true_ne_false`.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// The minted script, byte for byte what `ir_mint::mint` produces from the
/// committed core under the committed tag table (M3 of
/// `tests/crystal_a2_mint_lz.rs`).
const MINTED_IR_LZ: &str = include_str!("generated/ir_lz.defs.txt");

/// One rationale per `def` line, in registration order; the count is asserted
/// against the script so a regenerated script with a different shape fails
/// rather than silently reusing the wrong doc.
const MINTED_IR_LZ_DOCS: &[&str] = &[
    "ir_lz_tlevel: the Level enum type, enum id 3 (2 before the 2026-10-07 rebaseline) -- the id the emitted body names in `%3 = load enum.3, ptr %0`, minted out of the committed tag table generated/ir_lz.tags.json. The same Rust type the hand model's ir_tLevel names; the mint spells its own alias. DerivedProved, zero axiom_deps.",
    "ir_lz_b0: entry block, MINTED FROM THE EMITTED ARTIFACT. load the Level, extractfield the u8 discriminant, then a FOUR-case switch {0 -> b1, 1 -> b2, 4 -> b3, 2 -> b4} with IMax (tag 3) on the DEFAULT edge to b5 and exhaustive_enum_unreachable FALSE -- the measured flag, where the hand model carried a five-case table, an unreachable default and TRUE. The flagship's wrong-exhaustive-flag class, on the designated target itself. DerivedProved, zero axiom_deps.",
    "ir_lz_b1: Zero => true, then br to the join b6 with the answer as a block argument. The hand model RETURNS from each arm; the emitted body has no per-arm ret. DerivedProved, zero axiom_deps.",
    "ir_lz_b2: Succ => false, br b6. DerivedProved, zero axiom_deps.",
    "ir_lz_b3: Param => false, br b6. Its own block as emitted, not shared with Succ's as the hand model shared it. DerivedProved, zero axiom_deps.",
    "ir_lz_b4: the Max arm. gep the receiver to byte offsets 8 and 16 (the two LevelArc fields), CALL 1 (= <LevelArc as Deref>::deref, NOT in this module) on the first, CALL 0 (self) on its result, condbr on the answer to b7 (right operand) or b8 (short-circuit false). The hand model inlined the deref as extractfield + null-check + assert; the emitted body calls out. THIS is the arm on which ir_call_exec goes stuck no_func over this module. DerivedProved, zero axiom_deps.",
    "ir_lz_b5: the IMax arm, reached through the switch DEFAULT. gep to offset 16 only -- the first operand is never read, the impredicative collapse -- call 1 (deref), call 0 (self), br b6. Stuck at the deref call over this module, as b4 is. DerivedProved, zero axiom_deps.",
    "ir_lz_b6: the return join, taking a bool block parameter and returning it. The hand model has no join blocks at all. DerivedProved, zero axiom_deps.",
    "ir_lz_b7: Max, right operand: call 1 (deref) on the offset-16 pointer, call 0 (self), br b9 with the answer. EMITTED-ONLY: the hand model routed both of Max's recursions through one block. DerivedProved, zero axiom_deps.",
    "ir_lz_b8: Max, short-circuit: the left operand was not zero, so the answer is false without reading the right. EMITTED-ONLY. DerivedProved, zero axiom_deps.",
    "ir_lz_b9: the inner join for the && -- a bool block parameter forwarded to b6. EMITTED-ONLY. DerivedProved, zero axiom_deps.",
    "ir_lz_func: Level::is_zero as EvalIR, id 0, one ptr parameter, entry b0, TEN blocks -- the emitted body's control-flow graph exactly, against the hand model's seven. DerivedProved, zero axiom_deps.",
    "ir_lz_module: the MINTED module for the designated target level::Level::is_zero, one function and no globals. Generated from the emitted artifact rather than transcribed, and checked by three independent readers in tests/crystal_a2_mint_lz.rs (the artifact binary, the emitted text, and this elaborated term). It CALLS a function it does not define, so it is representation-equal to the artifact and NOT a module the A4 theorem holds over -- see ir_lz_minted_refutes_a4_on_max. DerivedProved, zero axiom_deps.",
];

const HEAP_ZERO: &str = "(ir_cell ir_d0 (ir_var ir_d0 ir_sp0) ir_mem0)";
const HEAP_SUCC: &str = "(ir_cell ir_d0 (ir_var ir_d1 (ir_sp1 (IRScalar.ptr_ ir_d1))) (ir_cell ir_d1 (ir_var ir_d0 ir_sp0) ir_mem0))";
const HEAP_PARAM: &str = "(ir_cell ir_d0 (ir_var ir_d4 (ir_sp1 (IRScalar.int_ n))) ir_mem0)";
const HEAP_MAXZZ: &str = "(ir_cell ir_d0 (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ ir_d1) (IRScalar.ptr_ ir_d2))) (ir_cell ir_d1 (ir_var ir_d0 ir_sp0) (ir_cell ir_d2 (ir_var ir_d0 ir_sp0) ir_mem0)))";
const HEAP_IMAXPZ: &str = "(ir_cell ir_d0 (ir_var ir_d3 (ir_sp2 (IRScalar.ptr_ ir_d1) (IRScalar.ptr_ ir_d2))) (ir_cell ir_d1 (ir_var ir_d4 (ir_sp1 (IRScalar.int_ n))) (ir_cell ir_d2 (ir_var ir_d0 ir_sp0) ir_mem0)))";

/// `ir_eval` of the minted module at the standard entry shape.
fn run(heap: &str, na: &str) -> String {
    format!("(ir_eval ir_fuel ir_lz_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) {heap} {na})")
}

/// A witness proved by `Eq.refl`: the kernel runs the machine and compares.
fn witness(name: &str, binder: &str, heap: &str, na: &str, outcome: &str) -> String {
    format!(
        "def {name} {binder}: Eq IROutcome {} {outcome} := @Eq.refl IROutcome {outcome}",
        run(heap, na)
    )
}

const RET_TRUE: &str = "(IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true)))";
const RET_FALSE: &str = "(IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.false)))";
const STUCK_NO_FUNC: &str = "(IROutcome.stuck IRFault.no_func)";

/// The A4 sentence, verbatim from `ir_lzm_correct`'s statement with
/// `ir_lz_module` in place of the model, as the TYPE of a hypothesis.
const A4_OVER_MINTED: &str = "forall (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (r : IRScalar) (l : Level) (href : EncodesLiveLevelRef mem r l), Le (ir_lzm_cost l) fuel -> Eq IROutcome (ir_eval fuel ir_lz_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (level_is_zero l))))";

/// The representation derivation the model's A2 relation gives the
/// `Max(Zero, Zero)` heap — every premise an `Eq.refl` on a concrete lookup.
const SRC_MAXZZ_REF: &str = "def encodes_live_ref_maxzz_witness : EncodesLiveLevelRef (ir_cell ir_d0 (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ ir_d1) (IRScalar.ptr_ ir_d2))) (ir_cell ir_d1 (ir_var ir_d0 ir_sp0) (ir_cell ir_d2 (ir_var ir_d0 ir_sp0) ir_mem0))) (IRScalar.ptr_ ir_d0) (Level.max Level.zero Level.zero) := EncodesLiveLevelRef.mk (ir_cell ir_d0 (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ ir_d1) (IRScalar.ptr_ ir_d2))) (ir_cell ir_d1 (ir_var ir_d0 ir_sp0) (ir_cell ir_d2 (ir_var ir_d0 ir_sp0) ir_mem0))) ir_d0 (Level.max Level.zero Level.zero) (EncodesLevelArc.max (ir_cell ir_d0 (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ ir_d1) (IRScalar.ptr_ ir_d2))) (ir_cell ir_d1 (ir_var ir_d0 ir_sp0) (ir_cell ir_d2 (ir_var ir_d0 ir_sp0) ir_mem0))) ir_d0 ir_d1 ir_d2 Level.zero Level.zero (@Eq.refl (IROption IRMemSlot) (@IROption.some IRMemSlot (IRMemSlot.mk ir_d0 (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ ir_d1) (IRScalar.ptr_ ir_d2))) Bool.true))) (EncodesLevelArc.zero (ir_cell ir_d0 (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ ir_d1) (IRScalar.ptr_ ir_d2))) (ir_cell ir_d1 (ir_var ir_d0 ir_sp0) (ir_cell ir_d2 (ir_var ir_d0 ir_sp0) ir_mem0))) ir_d1 (@Eq.refl (IROption IRMemSlot) (@IROption.some IRMemSlot (IRMemSlot.mk ir_d1 (ir_var ir_d0 ir_sp0) Bool.true)))) (EncodesLevelArc.zero (ir_cell ir_d0 (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ ir_d1) (IRScalar.ptr_ ir_d2))) (ir_cell ir_d1 (ir_var ir_d0 ir_sp0) (ir_cell ir_d2 (ir_var ir_d0 ir_sp0) ir_mem0))) ir_d2 (@Eq.refl (IROption IRMemSlot) (@IROption.some IRMemSlot (IRMemSlot.mk ir_d2 (ir_var ir_d0 ir_sp0) Bool.true)))))";

impl Specification {
    /// The minted module and its five computed witnesses. Needs only the IR
    /// types, the numerals, the builders and `ir_fuel`, so it belongs to the
    /// EvalIr bundle and is called from `add_eval_ir_crystal`.
    pub(super) fn add_eval_ir_level_minted_module(&mut self) -> Result<(), SpecError> {
        let minted: Vec<&str> = MINTED_IR_LZ
            .lines()
            .map(str::trim)
            .filter(|l| !l.is_empty())
            .collect();
        if minted.len() != MINTED_IR_LZ_DOCS.len() {
            return Err(SpecError::EnvError(format!(
                "the minted ir_lz script has {} definitions but {} rationales are declared; \
                 regenerate the docs table with the script rather than reusing it",
                minted.len(),
                MINTED_IR_LZ_DOCS.len()
            )));
        }
        for (line, doc) in minted.iter().zip(MINTED_IR_LZ_DOCS) {
            self.add_recursive_def(line, doc)?;
        }
        self.add_recursive_def(&witness("ir_lz_on_zero", "", HEAP_ZERO, "ir_d1", RET_TRUE), "ir_lz_on_zero: the MINTED module on Level::Zero returns true -- b0, then b1, then the join b6 with the block argument bound. Eq.refl: the kernel runs the machine. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(&witness("ir_lz_on_succ", "", HEAP_SUCC, "ir_d2", RET_FALSE), "ir_lz_on_succ: Succ(Zero) is false on the minted module; the inner Zero is in the heap so a semantics that wrongly recursed would return true and fail to typecheck. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(&witness("ir_lz_on_param", "(n : Nat) ", HEAP_PARAM, "ir_d1", RET_FALSE), "ir_lz_on_param: Param n is false on the minted module for EVERY n, through the emitted body's own b3 rather than a block shared with Succ. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(&witness("ir_lz_on_max_stuck", "", HEAP_MAXZZ, "ir_d3", STUCK_NO_FUNC), "ir_lz_on_max_stuck: *** THE MINTED MODULE GOES STUCK ON Max. *** Max(Zero, Zero) -- which Level::is_zero answers TRUE and the hand model's ir_is_zero_on_max_zero_zero returns TRUE -- halts IROutcome.stuck IRFault.no_func on the minted module: b4 geps to offsets 8 and 16 and then calls function 1, <LevelArc as Deref>::deref, which this module does not define. ir_func_find finds no function carrying id 1 and ir_call_exec halts stuck. Fail-closed, no misroute: the self-call is interned at 0 and the deref at 1 (callee_identity.rs). Eq.refl: the kernel executed eight steps and compared. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(&witness("ir_lz_on_imax_stuck", "(n : Nat) ", HEAP_IMAXPZ, "ir_d3", STUCK_NO_FUNC), "ir_lz_on_imax_stuck: IMax(Param n, Zero) -- TRUE under Level::is_zero, the impredicative collapse -- also halts stuck no_func on the minted module, for every n: the default edge carries the arm to b5, which geps to offset 16 and calls the deref. Together with ir_lz_on_max_stuck this is the arm split level_is_zero_callee_identity.rs pins from the fixture: constant arms return, recursive arms call out. DerivedProved, zero axiom_deps.")?;
        Ok(())
    }

    /// The refutation, as a theorem. Full-bundle only: it names `Level`,
    /// `level_is_zero`, `EncodesLiveLevelRef`, `ir_lzm_cost` and
    /// `ir_outcome_is_ret`, so it is staged after `add_eval_ir_correct`.
    pub(super) fn add_eval_ir_level_minted_refutation(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(SRC_MAXZZ_REF, "encodes_live_ref_maxzz_witness: the model's A2 relation ACCEPTS the three-cell Max(Zero, Zero) heap at address 0 -- EncodesLevelArc.max over two EncodesLevelArc.zero leaves, every lookup premise an @Eq.refl on the concrete heap. This is the heap ir_lz_minted_refutes_a4_on_max instantiates A4 at, so the refutation is at a represented input, not at junk. DerivedProved, zero axiom_deps.")?;
        let run_maxzz = "(ir_eval (ir_lzm_cost (Level.max Level.zero Level.zero)) ir_lz_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d0)) (ir_cell ir_d0 (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ ir_d1) (IRScalar.ptr_ ir_d2))) (ir_cell ir_d1 (ir_var ir_d0 ir_sp0) (ir_cell ir_d2 (ir_var ir_d0 ir_sp0) ir_mem0))) ir_d3)";
        let ret_a4 = "(IROutcome.ret (ir_vl1 (IRScalar.bool_ (level_is_zero (Level.max Level.zero Level.zero)))))";
        let src = format!(
            "def ir_lz_minted_refutes_a4_on_max (C : Type) (a4 : {A4_OVER_MINTED}) : C := \
             bool_true_ne_false C (Eq.cong IROutcome Bool ir_outcome_is_ret {ret_a4} {run_maxzz} \
             (@Eq.symm IROutcome {run_maxzz} {ret_a4} \
             (a4 (ir_cell ir_d0 (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ ir_d1) (IRScalar.ptr_ ir_d2))) (ir_cell ir_d1 (ir_var ir_d0 ir_sp0) (ir_cell ir_d2 (ir_var ir_d0 ir_sp0) ir_mem0))) \
             (ir_lzm_cost (Level.max Level.zero Level.zero)) ir_d3 (IRScalar.ptr_ ir_d0) (Level.max Level.zero Level.zero) \
             encodes_live_ref_maxzz_witness (Le.refl (ir_lzm_cost (Level.max Level.zero Level.zero))))))"
        );
        self.add_recursive_def(&src, "ir_lz_minted_refutes_a4_on_max: *** A4 OVER THE MINTED MODULE IS FALSE, KERNEL-CHECKED. *** The hypothesis a4 is ir_lzm_correct's statement VERBATIM with ir_lz_module (the minted module) in place of ir_lzm_module (the hand model): for every heap, fuel, counter, pointer and Level, representation plus enough fuel gives ret [bool (level_is_zero l)]. From it, every C : Type follows -- so it is refutable, which is the strongest negative the calculus states. \
\
The instantiation is at a REPRESENTED input, not junk: the heap is the three-cell Max(Zero, Zero) the model's A2 relation accepts (encodes_live_ref_maxzz_witness), and the fuel is the model's own cost ir_lzm_cost (Max Zero Zero) = 25, with Le.refl. On that input a4 promises ret [bool true] (level_is_zero (max zero zero) computes to true); the machine computes stuck no_func at step 8 (ir_lz_on_max_stuck). Applying ir_outcome_is_ret to both sides by Eq.cong yields Eq Bool true false, and bool_true_ne_false finishes. \
\
WHAT THIS MEANS FOR THE PAGE: link 4 of the designated target is OPEN. ir_lzm_correct is a theorem about the model; this is the theorem that says the model's statement does not transfer to the emitted body as it stands. The route that can close it -- a deref model in the module and a re-derivation over the emitted CFG -- is scoped in designs/2026-08-22-is-zero-model-vs-minted-decision.md, and its residual assumption (the bodies of Option::as_deref and Option::expect, which the artifact carries as declarations only) is architectural. DerivedProved, zero axiom_deps.")?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The script registered here is exactly the one the A2 gate regenerates.
    #[test]
    fn test_minted_script_is_the_registered_one() {
        assert_eq!(MINTED_IR_LZ, crate::ir_mint::IR_LZ_DEFS);
        assert_eq!(
            MINTED_IR_LZ
                .lines()
                .filter(|l| !l.trim().is_empty())
                .count(),
            MINTED_IR_LZ_DOCS.len()
        );
    }

    /// The four recorded divergence classes are visible in the registered
    /// text: the four-case switch with a FALSE flag, the join parameter, the
    /// gep + call pair, and the three emitted-only blocks.
    #[test]
    fn test_minted_script_carries_the_four_divergence_classes() {
        let s = MINTED_IR_LZ;
        assert!(s.contains("(ir_sc ir_d0 ir_d1 (ir_sc ir_d1 ir_d2 (ir_sc ir_d4 ir_d3 (ir_sc ir_d2 ir_d4 ir_sc0)))) Bool.false"));
        assert!(s.contains("def ir_lz_b6 : IRBlock := IRBlock.mk ir_d6 (ir_nl1 ir_d1)"));
        assert!(s.contains("IRInst.gep (IRTy.int_ ir_d8) ir_d0 (ir_nl1 ir_d8) Bool.true"));
        assert!(
            s.contains("IRInst.call ir_d1 (ir_nl1 ir_d9)")
                && s.contains("IRInst.call ir_d0 (ir_nl1 ir_d12)")
        );
        for b in ["ir_lz_b7", "ir_lz_b8", "ir_lz_b9"] {
            assert!(
                s.contains(&format!("def {b} : IRBlock")),
                "{b} is emitted-only"
            );
        }
        assert!(
            !s.contains("IRInst.assert")
                && !s.contains("IRInst.unreachable")
                && !s.contains("IRConst.null_")
        );
    }

    /// The refutation's hypothesis is A4's statement, not a weakening of it.
    #[test]
    fn test_refutation_hypothesis_is_the_a4_statement() {
        assert!(A4_OVER_MINTED.contains("(href : EncodesLiveLevelRef mem r l)"));
        assert!(A4_OVER_MINTED.contains("Le (ir_lzm_cost l) fuel ->"));
        assert!(A4_OVER_MINTED.contains("ir_eval fuel ir_lz_module ir_d0 (ir_vl1 r) mem na"));
        assert!(A4_OVER_MINTED.contains("(level_is_zero l)"));
        assert!(!A4_OVER_MINTED.contains("ir_lzm_module"));
    }

    #[test]
    fn test_sources_balanced_ascii() {
        for src in [SRC_MAXZZ_REF, A4_OVER_MINTED, MINTED_IR_LZ] {
            assert!(src.is_ascii(), "spec sources stay ASCII");
            assert_eq!(src.matches('(').count(), src.matches(')').count());
        }
    }
}
