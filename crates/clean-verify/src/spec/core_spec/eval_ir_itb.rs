// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **`ir_itb` — the designated target running its WHOLE DISPATCH, over an
//! AUTHORED heartbeat model.**
//!
//! This is the `ir_lzb` posture applied to `infer_type`: the module NAMES the
//! minted `ir_it_func` rather than transcribing it, and supplies beside it an
//! authored stand-in for the one callee whose real body cannot be carried.
//!
//! ```text
//!   ir_itb_module = IRModule.mk [ ir_it_func ; ir_itb_hb ] []
//! ```
//!
//! # Why an authored model here, when `ir_itc` has the real body
//!
//! `ir_itc` defines the REAL `tick_heartbeat` and the machine walks into it —
//! and halts at ITS first call, because `tick_heartbeat`'s own closure is **313
//! functions, 55,122 instructions, max SSA id 8,285**. Carrying that closure is
//! not a smaller problem than the one it solves. So this chain does what the
//! crystal already did for `<LevelArc as Deref>::deref`: models the callee's
//! ANSWER and lets the caller run.
//!
//! The two chains are complementary and neither replaces the other. `ir_itc`
//! shows the cut is real against the compiler's own body; `ir_itb` shows what
//! `infer_type` DOES once the heartbeat answers.
//!
//! # The model, and exactly what it assumes
//!
//! Two nodes: an aggregate CONSTANT and a return. It answers the no-error case —
//! tag 0, payload undef — which is what a heartbeat that has not expired returns.
//!
//! It is a constant rather than an `undef` + `insertfield` build ON PURPOSE:
//! `ir_undef_then_insertfield_faults` pins that the machine cannot execute the
//! producer's construction idiom, and `ir_cf_returns` pins that it CAN
//! materialise an aggregate constant. The model is written in the fragment the
//! machine has, not the one the producer uses.
//!
//! **THE RESIDUAL, stated as `ir_lzb`'s is.** `ir_itb_hb` is authored. It is not
//! `tick_heartbeat`, it is a model of one of its two answers, and this chain
//! proves nothing about whether the real body returns that answer under any
//! condition. What it establishes is what `infer_type` does GIVEN that answer.
//! Retiring it means either the 313-function closure or a compositional call
//! rule the machine does not have — both named in `eval_ir_itc.rs`.
//!
//! # What the machine then does, which is the point
//!
//! It runs the target's whole dispatch: allocas the `Result` slot, calls the
//! model, reads the tag with `extractfield`, takes the SWITCH, and reaches
//! `call 2` — `infer_type_fast`, the body that does the actual inference. That
//! is every instruction of `infer_type`'s control flow except the two calls
//! themselves, and no earlier chain has executed a `switch` in this target.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// The authored heartbeat model's block: an aggregate constant, and a return.
const SRC_ITB_HB_B0: &str = "def ir_itb_hb_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_bd2 (ir_nd1 (IRInst.const_ ir_it_tresult (IRConst.aggv (IRConst.vcons (IRConst.int_ ir_d0) (IRConst.vcons IRConst.undef_ (IRConst.vcons IRConst.undef_ IRConst.vnil))))) ir_d1) (ir_nd (IRInst.ret (ir_nl1 ir_d1))))";

/// The authored model itself — id 1, the canonical index `infer_type` calls.
const SRC_ITB_HB: &str =
    "def ir_itb_hb : IRFunc := IRFunc.mk ir_d1 (ir_nl1 ir_d0) ir_d0 (ir_blk ir_itb_hb_b0 ir_blk0)";

/// The module: the MINTED target, and the authored model beside it.
const SRC_ITB_MODULE: &str = "def ir_itb_module : IRModule := IRModule.mk (IRList.cons IRFunc ir_it_func (IRList.cons IRFunc ir_itb_hb (IRList.nil IRFunc))) (IRList.nil IRGlobal)";

const SRC_ITB_MACH0: &str = "def ir_itb_mach0 (mem : IRList IRMemSlot) (p : Nat) (q : Nat) (na : Nat) : IRMachine := IRMachine.mk (IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 Nat.zero (ir_bind_params (ir_nl2 ir_d0 ir_d1) (ir_vl2 (IRScalar.ptr_ p) (IRScalar.ptr_ q)) (IRList.nil IRBinding)) (IRList.nil Nat)) (IRList.nil IRFrame)) mem na";

const SRC_ITB_INIT: &str = "def ir_itb_init_is_mach0 (mem : IRList IRMemSlot) (p : Nat) (q : Nat) (na : Nat) : Eq IRConfig (ir_init ir_itb_module ir_d0 (ir_vl2 (IRScalar.ptr_ p) (IRScalar.ptr_ q)) mem na) (IRConfig.running (ir_itb_mach0 mem p q na)) := Eq.refl IRConfig (IRConfig.running (ir_itb_mach0 mem p q na))";

const SRC_ITB_REACHES: &str = "def ir_itb_reaches_the_inference_call (mem : IRList IRMemSlot) (p : Nat) (q : Nat) (na : Nat) : Eq IROutcome (ir_eval ir_d16 ir_itb_module ir_d0 (ir_vl2 (IRScalar.ptr_ p) (IRScalar.ptr_ q)) mem na) (IROutcome.stuck IRFault.no_func) := Eq.refl IROutcome (IROutcome.stuck IRFault.no_func)";

const SRC_ITB_STILL_RUNNING: &str = "def ir_itb_takes_the_switch (mem : IRList IRMemSlot) (p : Nat) (q : Nat) (na : Nat) : Eq IROutcome (ir_eval ir_d6 ir_itb_module ir_d0 (ir_vl2 (IRScalar.ptr_ p) (IRScalar.ptr_ q)) mem na) IROutcome.fuel_out := Eq.refl IROutcome IROutcome.fuel_out";

impl Specification {
    /// `ir_itb` — the target's whole dispatch, over an authored heartbeat.
    pub(super) fn add_eval_ir_itb(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(SRC_ITB_HB_B0, "ir_itb_hb_b0: the authored heartbeat model's only block -- an aggregate CONSTANT (tag 0, two undef payload slots) and a return. A constant and not an `undef` + `insertfield` build ON PURPOSE: ir_undef_then_insertfield_faults pins that the machine cannot execute the producer's construction idiom, and ir_cf_returns pins that it CAN materialise an aggregate constant, so the model is written in the fragment the machine has rather than the one the producer uses. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ITB_HB, "ir_itb_hb: the AUTHORED stand-in for tc::heartbeat::tick_heartbeat, at id 1 -- the canonical index infer_type's `call 1` names. Two nodes against the real body's 159 across twenty blocks. It models ONE of the two answers (the heartbeat has not expired) and is this chain's RESIDUAL, exactly as ir_lzb_deref is for the width-one chain. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ITB_MODULE, "ir_itb_module: the designated target and the authored model. It NAMES ir_it_func rather than transcribing it -- the ir_lzb posture -- so the body under execution here is byte-identical to the one ir_it and ir_itc carry, and a change to the mint moves all three together. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ITB_MACH0, "ir_itb_mach0: the machine ir_init produces, the same two pointer parameters. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ITB_INIT, "ir_itb_init_is_mach0: the hand-written initial machine IS the one ir_init builds, by computation. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ITB_STILL_RUNNING, "ir_itb_takes_the_switch: at SIX steps the machine is still running, where ir_it_module halted at TWO and ir_itc_module at six-and-into-the-heartbeat. Six steps is past the alloca, the call, the model's constant and return, the `br` into block 1, and the extractfield that reads the tag -- the SWITCH is the next node and has not fired yet. (An earlier wording of this sentence listed six items and omitted the `br`, which made it read as though the branch had already been taken at six steps. The theorem was true either way; the prose was off by one node, and a later chain in this family duly inherited the mis-count and asserted a false fuel. One node is one step -- ir_slot_cost_is_4 pins that arithmetic.) The branch actually firing is what ir_itb_reaches_the_inference_call records, at step 8. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ITB_REACHES, "*** THE TARGET RUNS ITS WHOLE DISPATCH AND REACHES THE INFERENCE CALL. *** For every heap, both arguments and every counter, the machine allocas the Result slot, calls the heartbeat model, reads its tag, TAKES THE SWITCH, and halts at `call 2` -- infer_type_fast, the body that does the actual inference. That is every instruction of infer_type's control flow except the two calls themselves, and no earlier chain has executed a switch in this target. \\n\\nThe halt is at STEP 8 and is `stuck no_func` because infer_type_fast is a declaration here; what is NEW is WHERE. (The fuel stated is 16, a comfortable over-approximation rather than the exact cost -- read the step, not the fuel.) ir_it halts at the first call, ir_itc one frame into the real heartbeat, and this chain past the heartbeat entirely, on the ok branch. \\n\\nWhat it does NOT establish: that the real tick_heartbeat returns the answer the model gives. ir_itb_hb is authored and is this chain's residual. DerivedProved, zero axiom_deps.")?;
        Ok(())
    }
}
