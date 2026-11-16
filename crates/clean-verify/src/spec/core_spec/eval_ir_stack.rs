// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **`ir_stk` — the frame-stacking family: a frame's execution does not depend
//! on the frames beneath it until it returns.**
//!
//! This is the COMPOSITIONAL CALL RULE the machine has lacked. Every chain so
//! far runs a callee only by placing its body in the same module; the
//! `has_loose_bvars` chain composes ONE concrete callee's activation with its
//! caller's resume by `Eq.refl` at an abstract `rest`, which works exactly
//! because the machine is frame-local. This file states that locality once, as
//! a lemma over an ABSTRACT module, so a callee's standalone behaviour can
//! stand in for its inline execution under ANY caller.
//!
//! # Why it is provable — the machine is frame-local except at `ret`
//!
//! Every `IRList.rec IRFrame` on the step path (`ir_step`, `ir_frames_get`,
//! `ir_cur_func`, `ir_bind`, `ir_bind2`, `ir_advance`, `ir_alloca_k`,
//! `ir_goto`, `ir_push`, `ir_ret_vals`) binds the tail as `_` or re-conses it
//! verbatim and DISCARDS its induction hypothesis. The one definition whose
//! major premise is the tail itself is `ir_ret_to`: a non-empty caller list
//! pops and continues `running`, an empty one halts with `IROutcome.ret`. So
//! at an abstract `rest` every iota on the frame list still fires, and
//! `ir_ret_to` is stuck identically on both sides of a stacking equation.
//!
//! # What this stage carries (build order — each step a bundle build)
//!
//! 1. the four definitions and their `Eq.refl` vacuity pins (THIS FILE, now);
//! 2. `ir_step_cons_fetch` — the cheapest measurement: does the elaborator
//!    unfold `ir_step` at an ABSTRACT module and frame? Every later convoy is
//!    syntactic if so, and this is the wall if not;
//! 3. head-only read pins, writer lemmas, branching helpers, the thirty
//!    per-arm lemmas (minted), then `ir_stk_step` / `ir_stk_steps` /
//!    `ir_stk_ret_step` / `ir_stk_activation`.
//!
//! The corrected statement, from the reconciliation of four independent reads:
//! the informal "standalone reaches `IROutcome.ret vals` with final heap" is
//! NOT statable — `IROutcome.ret` carries no heap, and `ir_ret_to` at a nil
//! tail halts for EVERY heap. The honest premise is the RUNNING pre-return
//! configuration plus the fetched `ret` node, and the cost is `1 + k`.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

// ── A. definitions ────────────────────────────────────────────────────────
const SRC_FRAMES_APP: &str = "def ir_frames_app (a : IRList IRFrame) (b : IRList IRFrame) : IRList IRFrame := @IRList.rec IRFrame (fun (_ : IRList IRFrame) => IRList IRFrame) b (fun (x : IRFrame) (_ : IRList IRFrame) (ih : IRList IRFrame) => @IRList.cons IRFrame x ih) a";
const SRC_MACH_STACK: &str = "def ir_mach_stack (s : IRMachine) (rest : IRList IRFrame) : IRMachine := @IRMachine.rec (fun (_ : IRMachine) => IRMachine) (fun (fs : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) => IRMachine.mk (ir_frames_app fs rest) mem na) s";
const SRC_CONFIG_STACK: &str = "def ir_config_stack (c : IRConfig) (rest : IRList IRFrame) : IRConfig := @IRConfig.rec (fun (_ : IRConfig) => IRConfig) (fun (s : IRMachine) => IRConfig.running (ir_mach_stack s rest)) (fun (o : IROutcome) => IRConfig.halted o) c";
const SRC_STK_RUNNING: &str = "def ir_stk_running (c : IRConfig) : Bool := @IRConfig.rec (fun (_ : IRConfig) => Bool) (fun (_ : IRMachine) => Bool.true) (fun (_ : IROutcome) => Bool.false) c";

// ── B. shape / vacuity pins (an undeclared id in a TYPE becomes a silent
//       free variable, so every definition gets a companion spelling its body)
const SRC_APP_NIL: &str = "def ir_frames_app_nil (b : IRList IRFrame) : @Eq (IRList IRFrame) (ir_frames_app (@IRList.nil IRFrame) b) b := @Eq.refl (IRList IRFrame) b";
const SRC_APP_CONS: &str = "def ir_frames_app_cons (x : IRFrame) (a : IRList IRFrame) (b : IRList IRFrame) : @Eq (IRList IRFrame) (ir_frames_app (@IRList.cons IRFrame x a) b) (@IRList.cons IRFrame x (ir_frames_app a b)) := @Eq.refl (IRList IRFrame) (@IRList.cons IRFrame x (ir_frames_app a b))";
const SRC_MACH_STACK_MK: &str = "def ir_mach_stack_mk (fs : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) (rest : IRList IRFrame) : @Eq IRMachine (ir_mach_stack (IRMachine.mk fs mem na) rest) (IRMachine.mk (ir_frames_app fs rest) mem na) := @Eq.refl IRMachine (IRMachine.mk (ir_frames_app fs rest) mem na)";
const SRC_CFG_RUNNING: &str = "def ir_config_stack_running (s : IRMachine) (rest : IRList IRFrame) : @Eq IRConfig (ir_config_stack (IRConfig.running s) rest) (IRConfig.running (ir_mach_stack s rest)) := @Eq.refl IRConfig (IRConfig.running (ir_mach_stack s rest))";
const SRC_CFG_HALTED: &str = "def ir_config_stack_halted (o : IROutcome) (rest : IRList IRFrame) : @Eq IRConfig (ir_config_stack (IRConfig.halted o) rest) (IRConfig.halted o) := @Eq.refl IRConfig (IRConfig.halted o)";
const SRC_RET_NIL: &str = "def ir_ret_to_nil_halts (ds : IRList Nat) (mem : IRList IRMemSlot) (na : Nat) (vs : IRList IRScalar) : @Eq IRConfig (ir_ret_to ds (@IRList.nil IRFrame) mem na vs) (IRConfig.halted (IROutcome.ret vs)) := @Eq.refl IRConfig (IRConfig.halted (IROutcome.ret vs))";

// ── the measurement: does ir_step unfold at an ABSTRACT module and frame? ──
const SRC_STEP_CONS_FETCH: &str = "def ir_step_cons_fetch (m : IRModule) (f : IRFrame) (t : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) : @Eq IRConfig (ir_step m (IRMachine.mk (@IRList.cons IRFrame f t) mem na)) (ir_step_f m (IRMachine.mk (@IRList.cons IRFrame f t) mem na) (ir_frame_block f) (ir_frame_pc f) (ir_func_find (ir_mod_funcs m) (ir_frame_func f))) := @Eq.refl IRConfig (ir_step_f m (IRMachine.mk (@IRList.cons IRFrame f t) mem na) (ir_frame_block f) (ir_frame_pc f) (ir_func_find (ir_mod_funcs m) (ir_frame_func f)))";

// ── S2 / S4: hand-authored theorems that depend only on the foundation ──
const SRC_STK_RUNNING_BACK: &str = "def ir_stk_running_back (m : IRModule) (k : Nat) (c : IRConfig) (h : @Eq Bool (ir_stk_running (ir_steps k m c)) Bool.true) : @Eq Bool (ir_stk_running c) Bool.true := @IRConfig.rec (fun (c0 : IRConfig) => @Eq Bool (ir_stk_running (ir_steps k m c0)) Bool.true -> @Eq Bool (ir_stk_running c0) Bool.true) (fun (s : IRMachine) (_ : @Eq Bool (ir_stk_running (ir_steps k m (IRConfig.running s))) Bool.true) => @Eq.refl Bool Bool.true) (fun (o : IROutcome) (h0 : @Eq Bool (ir_stk_running (ir_steps k m (IRConfig.halted o))) Bool.true) => ir_bool_false_ne_true (@Eq Bool (ir_stk_running (IRConfig.halted o)) Bool.true) (@Eq.subst IRConfig (fun (c1 : IRConfig) => @Eq Bool (ir_stk_running c1) Bool.true) (ir_steps k m (IRConfig.halted o)) (IRConfig.halted o) (ir_steps_halted m o k) h0)) c h";
const SRC_STK_RET_STEP: &str = "def ir_stk_ret_step (m : IRModule) (f : IRFrame) (rest : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) (fn : IRFunc) (b : IRBlock) (ids : IRList Nat) (rs : IRList Nat) (hf : @Eq (IROption IRFunc) (ir_func_find (ir_mod_funcs m) (ir_frame_func f)) (@IROption.some IRFunc fn)) (hb : @Eq (IROption IRBlock) (ir_block_find (ir_func_blocks fn) (ir_frame_block f)) (@IROption.some IRBlock b)) (hn : @Eq (IROption IRNode) (ir_nodes_get (ir_block_nodes b) (ir_frame_pc f)) (@IROption.some IRNode (IRNode.mk (IRInst.ret ids) rs))) : @Eq IRConfig (ir_step m (IRMachine.mk (@IRList.cons IRFrame f rest) mem na)) (ir_ret_to (ir_frame_dests f) rest mem na (ir_resolve (IRMachine.mk (@IRList.cons IRFrame f rest) mem na) ids)) := @Eq.subst (IROption IRFunc) (fun (o : IROption IRFunc) => @Eq IRConfig (ir_step_f m (IRMachine.mk (@IRList.cons IRFrame f rest) mem na) (ir_frame_block f) (ir_frame_pc f) o) (ir_ret_to (ir_frame_dests f) rest mem na (ir_resolve (IRMachine.mk (@IRList.cons IRFrame f rest) mem na) ids))) (@IROption.some IRFunc fn) (ir_func_find (ir_mod_funcs m) (ir_frame_func f)) (@Eq.symm (IROption IRFunc) (ir_func_find (ir_mod_funcs m) (ir_frame_func f)) (@IROption.some IRFunc fn) hf) (@Eq.subst (IROption IRBlock) (fun (ob : IROption IRBlock) => @Eq IRConfig (ir_step_b m (IRMachine.mk (@IRList.cons IRFrame f rest) mem na) (ir_frame_pc f) ob) (ir_ret_to (ir_frame_dests f) rest mem na (ir_resolve (IRMachine.mk (@IRList.cons IRFrame f rest) mem na) ids))) (@IROption.some IRBlock b) (ir_block_find (ir_func_blocks fn) (ir_frame_block f)) (@Eq.symm (IROption IRBlock) (ir_block_find (ir_func_blocks fn) (ir_frame_block f)) (@IROption.some IRBlock b) hb) (@Eq.subst (IROption IRNode) (fun (on : IROption IRNode) => @Eq IRConfig (ir_step_n m (IRMachine.mk (@IRList.cons IRFrame f rest) mem na) on) (ir_ret_to (ir_frame_dests f) rest mem na (ir_resolve (IRMachine.mk (@IRList.cons IRFrame f rest) mem na) ids))) (@IROption.some IRNode (IRNode.mk (IRInst.ret ids) rs)) (ir_nodes_get (ir_block_nodes b) (ir_frame_pc f)) (@Eq.symm (IROption IRNode) (ir_nodes_get (ir_block_nodes b) (ir_frame_pc f)) (@IROption.some IRNode (IRNode.mk (IRInst.ret ids) rs)) hn) (@Eq.refl IRConfig (ir_ret_to (ir_frame_dests f) rest mem na (ir_resolve (IRMachine.mk (@IRList.cons IRFrame f rest) mem na) ids)))))";

impl Specification {
    /// `ir_stk` — frame stacking: definitions, vacuity pins, and the
    /// abstract-module shape witness.
    pub(super) fn add_eval_ir_stack(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(SRC_FRAMES_APP, "ir_frames_app: list append on frame lists, by @IRList.rec on the first argument. Used to place an arbitrary caller stack `rest` BENEATH a running frame list. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_MACH_STACK, "ir_mach_stack: the machine with `rest` appended beneath its frames; heap and counter untouched. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_CONFIG_STACK, "ir_config_stack: lift ir_mach_stack over a configuration -- a running machine gets the stack, a halted outcome is UNCHANGED. That asymmetry is the content: a halted leaf of the stacking lemma is Eq.refl, and the premise is consumed only where the tail is observable (the empty frame list, and ir_ret_to at an empty tail). DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_STK_RUNNING, "ir_stk_running: Bool test for `running`. A stage-local twin of the Full-only ir_config_is_running, so this family can live in the EvalIr bundle. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_APP_NIL, "ir_frames_app_nil: vacuity pin -- the definition's nil case, by computation. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_APP_CONS, "ir_frames_app_cons: vacuity pin -- the definition's cons case, by computation. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_MACH_STACK_MK, "ir_mach_stack_mk: vacuity pin -- ir_mach_stack on a constructor, by computation. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_CFG_RUNNING, "ir_config_stack_running: vacuity pin -- the running arm, by computation. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_CFG_HALTED, "ir_config_stack_halted: vacuity pin -- the halted arm is the identity, by computation. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_RET_NIL, "ir_ret_to_nil_halts: ir_ret_to at an EMPTY caller list halts with IROutcome.ret for every heap and counter -- the fact that makes the naive 'standalone reaches ret vals with final heap' statement unstatable, pinned so the corrected statement's reason is in the spec and not only in prose. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_STEP_CONS_FETCH, "*** THE MEASUREMENT. *** ir_step on a cons-headed frame list IS the fetch through ir_step_f, at an ABSTRACT module and an ABSTRACT frame, by Eq.refl. The elaborator must unfold ir_step, ir_step_frame and the @IRList.rec iota on a constructor head with neutral fields for this to register. If it does, every later convoy in the stacking family is syntactic; if it does not, this is the wall and it is found in one 40-second build rather than after a 30-arm term. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_STK_RUNNING_BACK, "ir_stk_running_back (S2): a run still running after k steps was running before them. @IRConfig.rec on the configuration: the running arm is Eq.refl; the halted arm is REFUTED -- ir_steps_halted says a halted config stays halted for every fuel, so the hypothesis reduces to @Eq Bool Bool.false Bool.true, and ir_bool_false_ne_true discharges it. This is the lemma that lets ir_stk_steps feed the per-step running premise to ir_stk_step at every level of the fuel induction. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_STK_RET_STEP, "ir_stk_ret_step (S4): THE RET STEP, keyed on the FETCHED NODE. Given that the head frame's function, block and node resolve (three premises, each an @Eq on an IROption), one ir_step from any caller stack `rest` IS ir_ret_to (ir_frame_dests f) rest mem na <resolved ids> -- pops into `rest`, dests read off the head frame, operands resolved from the head only. Three suspended-lookup @Eq.subst + @Eq.symm (the eval_ir_activation.rs:100-108 idiom), then Eq.refl. Keyed on the fetched node rather than on `halted (ret vs)` because in the 18 ir_bind_result arms the fault outcome is abstract and `halted o = halted (ret vs)` is irrefutable without a per-evaluator never-returns-ret family that does not exist. DerivedProved, zero axiom_deps.")?;
        Ok(())
    }
}
