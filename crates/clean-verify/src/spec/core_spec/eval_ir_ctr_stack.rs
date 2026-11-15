// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//! **E2's open item: the three-way reading of a contract at an ARBITRARY
//! caller stack** (decision memo §11 item 8; statements settled in
//! `designs/2026-09-25-e1-axes.md` §5).
//!
//! `ir_ctr_tri` reads a contract only at the EMPTY caller stack, where a return
//! halts. At an arbitrary caller stack `r` the run does not stop at the return
//! -- it goes on into the caller -- so the reading has to say where the stacked
//! run is while the callee still owns it, and what the callee handed back when
//! it stopped owning it. `ir_stk_tri Q r c cs` is that reading, over the run at
//! the empty stack (`c`) and the run at `r` (`cs`) after the same `k` steps:
//!
//! * the callee is still RUNNING -- and the stacked run is exactly the callee's
//!   machine with `r` beneath it, untouched;
//! * the callee HALTED with a sanctioned panic -- and the stacked run halted
//!   identically (and the vacuous `fuel_out` halt the type admits, likewise);
//! * the callee RETURNED values `vs` -- and some final heap and counter satisfy
//!   the post for them (`ir_ret_post`);
//!
//! and nothing else. `ir_ctr_tri_stack` proves it from the contract for every
//! entry that is its empty-stack entry with the caller stack appended
//! (`hE`, `Eq.refl` for every single-frame entry). It rests on E1's split:
//! `ir_stk_clear_of_mid` shows a run that halts in the middle of the commuting
//! class was clear at every running prefix, through the minted classifier
//! converse `ir_stk_botret_ret`.
//!
//! **What the continuation form does NOT give, stated rather than weakened
//! silently.** The return case reads the post at SOME heap, not at the heap the
//! stacked machine holds when it returns into `r`: a contract only ever observes
//! the callee through continuations written in the module's own code, and a
//! module whose code cannot read the heap cannot tell two heaps apart, so the
//! heap-exact reading does not follow from `ir_ctr_at` --
//! `ir_ctr_heap_exact_refuted` derives any proposition from it, at a one-line
//! `ret []` body. What IS exact is the return CONFIGURATION: at the
//! first return, `ir_stk_activation_dests_gen` gives `ir_ret_to d r mem2 na2 vs`
//! with the machine's own heap, and `ir_ctr_ret_post_stack` says the post holds
//! for those values.
//!
//! Registered in BOTH the Full stage list and the EvalIr bundle, after
//! `add_eval_ir_lzd_sctr` (the deref contract the witness instantiates). Every
//! declaration kernel-checked, empty axiom closure, by name.

use super::{SpecError, Specification};

const SRC_STEP_OF_NIL: &str = "def ir_step_of_nil (m : IRModule) (s : IRMachine) (he : Eq Bool (ir_frames_is_nil (ir_mach_frames s)) Bool.true) : Eq IRConfig (ir_step m s) (IRConfig.halted (IROutcome.stuck IRFault.no_frame)) := IRMachine.rec (fun (s0 : IRMachine) => Eq Bool (ir_frames_is_nil (ir_mach_frames s0)) Bool.true -> Eq IRConfig (ir_step m s0) (IRConfig.halted (IROutcome.stuck IRFault.no_frame))) (fun (fs : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) => IRList.rec IRFrame (fun (fs0 : IRList IRFrame) => Eq Bool (ir_frames_is_nil fs0) Bool.true -> Eq IRConfig (ir_step m (IRMachine.mk fs0 mem na)) (IRConfig.halted (IROutcome.stuck IRFault.no_frame))) (fun (_ : Eq Bool (ir_frames_is_nil (IRList.nil IRFrame)) Bool.true) => Eq.refl IRConfig (IRConfig.halted (IROutcome.stuck IRFault.no_frame))) (fun (f : IRFrame) (t : IRList IRFrame) (_ : Eq Bool (ir_frames_is_nil t) Bool.true -> Eq IRConfig (ir_step m (IRMachine.mk t mem na)) (IRConfig.halted (IROutcome.stuck IRFault.no_frame))) (h0 : Eq Bool (ir_frames_is_nil (IRList.cons IRFrame f t)) Bool.true) => ir_bool_false_ne_true (Eq IRConfig (ir_step m (IRMachine.mk (IRList.cons IRFrame f t) mem na)) (IRConfig.halted (IROutcome.stuck IRFault.no_frame))) h0) fs) s he";
const SRC_HALT_MID_OF_RET: &str = "def ir_halt_mid_of_ret (m : IRModule) (k : Nat) (c : IRConfig) (hr : Eq Bool (ir_is_ret_halt c) Bool.true) : Eq Bool (ir_halt_mid (ir_steps k m c)) Bool.false := IRConfig.rec (fun (c0 : IRConfig) => Eq Bool (ir_is_ret_halt c0) Bool.true -> Eq Bool (ir_halt_mid (ir_steps k m c0)) Bool.false) (fun (s : IRMachine) (h0 : Eq Bool (ir_is_ret_halt (IRConfig.running s)) Bool.true) => ir_bool_false_ne_true (Eq Bool (ir_halt_mid (ir_steps k m (IRConfig.running s))) Bool.false) h0) (fun (o : IROutcome) (h0 : Eq Bool (ir_is_ret_halt (IRConfig.halted o)) Bool.true) => Eq.subst IRConfig (fun (c1 : IRConfig) => Eq Bool (ir_halt_mid c1) Bool.false) (IRConfig.halted o) (ir_steps k m (IRConfig.halted o)) (Eq.symm IRConfig (ir_steps k m (IRConfig.halted o)) (IRConfig.halted o) (ir_steps_halted m o k)) (IROutcome.rec (fun (o0 : IROutcome) => Eq Bool (ir_is_ret_halt (IRConfig.halted o0)) Bool.true -> Eq Bool (ir_halt_mid (IRConfig.halted o0)) Bool.false) (fun (vs : IRList IRScalar) (_ : Eq Bool (ir_is_ret_halt (IRConfig.halted (IROutcome.ret vs))) Bool.true) => Eq.refl Bool Bool.false) (fun (f : IRFault) (h1 : Eq Bool (ir_is_ret_halt (IRConfig.halted (IROutcome.ub f))) Bool.true) => ir_bool_false_ne_true (Eq Bool (ir_halt_mid (IRConfig.halted (IROutcome.ub f))) Bool.false) h1) (fun (f : IRFault) (h1 : Eq Bool (ir_is_ret_halt (IRConfig.halted (IROutcome.type_error f))) Bool.true) => ir_bool_false_ne_true (Eq Bool (ir_halt_mid (IRConfig.halted (IROutcome.type_error f))) Bool.false) h1) (fun (f : IRFault) (h1 : Eq Bool (ir_is_ret_halt (IRConfig.halted (IROutcome.unmodelled f))) Bool.true) => ir_bool_false_ne_true (Eq Bool (ir_halt_mid (IRConfig.halted (IROutcome.unmodelled f))) Bool.false) h1) (fun (f : IRFault) (h1 : Eq Bool (ir_is_ret_halt (IRConfig.halted (IROutcome.stuck f))) Bool.true) => ir_bool_false_ne_true (Eq Bool (ir_halt_mid (IRConfig.halted (IROutcome.stuck f))) Bool.false) h1) (fun (h1 : Eq Bool (ir_is_ret_halt (IRConfig.halted IROutcome.fuel_out)) Bool.true) => ir_bool_false_ne_true (Eq Bool (ir_halt_mid (IRConfig.halted IROutcome.fuel_out)) Bool.false) h1) o h0)) c hr";
const SRC_STK_NONNIL_OF_MID: &str = "def ir_stk_nonnil_of_mid (m : IRModule) (k : Nat) (s : IRMachine) (h : Eq Bool (ir_halt_mid (ir_steps k m (ir_step m s))) Bool.true) : Eq Bool (ir_frames_is_nil (ir_mach_frames s)) Bool.false := Bool.rec (fun (b : Bool) => Eq Bool (ir_frames_is_nil (ir_mach_frames s)) b -> Eq Bool (ir_frames_is_nil (ir_mach_frames s)) Bool.false) (fun (he : Eq Bool (ir_frames_is_nil (ir_mach_frames s)) Bool.false) => he) (fun (he : Eq Bool (ir_frames_is_nil (ir_mach_frames s)) Bool.true) => ir_bool_false_ne_true (Eq Bool (ir_frames_is_nil (ir_mach_frames s)) Bool.false) (Eq.subst IRConfig (fun (c1 : IRConfig) => Eq Bool (ir_halt_mid c1) Bool.true) (ir_steps k m (IRConfig.halted (IROutcome.stuck IRFault.no_frame))) (IRConfig.halted (IROutcome.stuck IRFault.no_frame)) (ir_steps_halted m (IROutcome.stuck IRFault.no_frame) k) (Eq.subst IRConfig (fun (c1 : IRConfig) => Eq Bool (ir_halt_mid (ir_steps k m c1)) Bool.true) (ir_step m s) (IRConfig.halted (IROutcome.stuck IRFault.no_frame)) (ir_step_of_nil m s he) h))) (ir_frames_is_nil (ir_mach_frames s)) (Eq.refl Bool (ir_frames_is_nil (ir_mach_frames s)))";
const SRC_STK_NOTBOT_OF_MID: &str = "def ir_stk_notbot_of_mid (m : IRModule) (k : Nat) (s : IRMachine) (h : Eq Bool (ir_halt_mid (ir_steps k m (ir_step m s))) Bool.true) : Eq Bool (ir_stk_botret m s) Bool.false := Bool.rec (fun (b : Bool) => Eq Bool (ir_stk_botret m s) b -> Eq Bool (ir_stk_botret m s) Bool.false) (fun (he : Eq Bool (ir_stk_botret m s) Bool.false) => he) (fun (he : Eq Bool (ir_stk_botret m s) Bool.true) => ir_bool_false_ne_true (Eq Bool (ir_stk_botret m s) Bool.false) (Eq.trans Bool Bool.false (ir_halt_mid (ir_steps k m (ir_step m s))) Bool.true (Eq.symm Bool (ir_halt_mid (ir_steps k m (ir_step m s))) Bool.false (ir_halt_mid_of_ret m k (ir_step m s) (ir_stk_botret_ret m s he))) h)) (ir_stk_botret m s) (Eq.refl Bool (ir_stk_botret m s))";
const SRC_STK_CLEAR_OF_MID: &str = "def ir_stk_clear_of_mid (m : IRModule) (n : Nat) : forall (c : IRConfig), Eq Bool (ir_halt_mid (ir_steps n m c)) Bool.true -> Eq Bool (ir_stk_clear n m c) Bool.true := Nat.rec (fun (k : Nat) => forall (c : IRConfig), Eq Bool (ir_halt_mid (ir_steps k m c)) Bool.true -> Eq Bool (ir_stk_clear k m c) Bool.true) (fun (c : IRConfig) (_ : Eq Bool (ir_halt_mid (ir_steps Nat.zero m c)) Bool.true) => Eq.refl Bool Bool.true) (fun (k : Nat) (ih : forall (c : IRConfig), Eq Bool (ir_halt_mid (ir_steps k m c)) Bool.true -> Eq Bool (ir_stk_clear k m c) Bool.true) => fun (c : IRConfig) => IRConfig.rec (fun (c0 : IRConfig) => Eq Bool (ir_halt_mid (ir_steps (Nat.succ k) m c0)) Bool.true -> Eq Bool (ir_stk_clear (Nat.succ k) m c0) Bool.true) (fun (s : IRMachine) (h : Eq Bool (ir_halt_mid (ir_steps (Nat.succ k) m (IRConfig.running s))) Bool.true) => ir_bool_guard_intro (ir_frames_is_nil (ir_mach_frames s)) (Bool.rec (fun (_ : Bool) => Bool) (ir_stk_clear k m (ir_step m s)) Bool.false (ir_stk_botret m s)) (ir_stk_nonnil_of_mid m k s h) (ir_bool_guard_intro (ir_stk_botret m s) (ir_stk_clear k m (ir_step m s)) (ir_stk_notbot_of_mid m k s h) (ih (ir_step m s) h))) (fun (o : IROutcome) (_ : Eq Bool (ir_halt_mid (ir_steps (Nat.succ k) m (IRConfig.halted o))) Bool.true) => Eq.refl Bool Bool.true) c) n";
const SRC_STK_TRI: &str = "def ir_stk_tri (Q : IRList IRMemSlot -> Nat -> IRList IRScalar -> Prop) (r : IRList IRFrame) (c : IRConfig) (cs : IRConfig) : Prop := IRConfig.rec (fun (_ : IRConfig) => Prop) (fun (s : IRMachine) => Eq IRConfig cs (IRConfig.running (ir_mach_stack s r))) (fun (o : IROutcome) => IROutcome.rec (fun (_ : IROutcome) => Prop) (fun (vs : IRList IRScalar) => ir_ret_post Q (IROutcome.ret vs)) (fun (f : IRFault) => ir_bprop (forall (C : Prop), C) (Eq IRConfig cs (IRConfig.halted (IROutcome.ub f))) (ir_fault_is_assert f)) (fun (_ : IRFault) => forall (C : Prop), C) (fun (_ : IRFault) => forall (C : Prop), C) (fun (_ : IRFault) => forall (C : Prop), C) (Eq IRConfig cs (IRConfig.halted IROutcome.fuel_out)) o) c";
const SRC_STK_TRI_OF_RUN: &str = "def ir_stk_tri_of_run (m : IRModule) (Q : IRList IRMemSlot -> Nat -> IRList IRScalar -> Prop) (r : IRList IRFrame) (k : Nat) (c : IRConfig) (hro : ir_run_ok (ir_ret_post Q) (ir_config_outcome (ir_steps k m c))) : ir_stk_tri Q r (ir_steps k m c) (ir_steps k m (ir_config_stack c r)) := IRConfig.rec (fun (c0 : IRConfig) => Eq IRConfig (ir_steps k m c) c0 -> ir_run_ok (ir_ret_post Q) (ir_config_outcome c0) -> ir_stk_tri Q r c0 (ir_steps k m (ir_config_stack c r))) (fun (s : IRMachine) (he : Eq IRConfig (ir_steps k m c) (IRConfig.running s)) (_ : ir_run_ok (ir_ret_post Q) (ir_config_outcome (IRConfig.running s))) => ir_stk_split_running m r k c s (ir_stk_clear_of_running m k c (Eq.subst IRConfig (fun (c1 : IRConfig) => Eq Bool (ir_stk_running c1) Bool.true) (IRConfig.running s) (ir_steps k m c) (Eq.symm IRConfig (ir_steps k m c) (IRConfig.running s) he) (Eq.refl Bool Bool.true))) he) (fun (o : IROutcome) => IROutcome.rec (fun (o0 : IROutcome) => Eq IRConfig (ir_steps k m c) (IRConfig.halted o0) -> ir_run_ok (ir_ret_post Q) (ir_config_outcome (IRConfig.halted o0)) -> ir_stk_tri Q r (IRConfig.halted o0) (ir_steps k m (ir_config_stack c r))) (fun (vs : IRList IRScalar) (_ : Eq IRConfig (ir_steps k m c) (IRConfig.halted (IROutcome.ret vs))) (h : ir_run_ok (ir_ret_post Q) (ir_config_outcome (IRConfig.halted (IROutcome.ret vs)))) => h) (fun (f : IRFault) (he : Eq IRConfig (ir_steps k m c) (IRConfig.halted (IROutcome.ub f))) (h : ir_run_ok (ir_ret_post Q) (ir_config_outcome (IRConfig.halted (IROutcome.ub f)))) => Bool.rec (fun (b : Bool) => ir_bprop (ir_ret_post Q (IROutcome.ub f)) (Eq Bool Bool.true Bool.true) b -> ir_bprop (forall (C : Prop), C) (Eq IRConfig (ir_steps k m (ir_config_stack c r)) (IRConfig.halted (IROutcome.ub f))) b) (fun (h0 : ir_ret_post Q (IROutcome.ub f)) => h0) (fun (_ : Eq Bool Bool.true Bool.true) => ir_stk_split_halted m r k c (IROutcome.ub f) (ir_stk_clear_of_mid m k c (Eq.subst IRConfig (fun (c1 : IRConfig) => Eq Bool (ir_halt_mid c1) Bool.true) (IRConfig.halted (IROutcome.ub f)) (ir_steps k m c) (Eq.symm IRConfig (ir_steps k m c) (IRConfig.halted (IROutcome.ub f)) he) (Eq.refl Bool Bool.true))) he) (ir_fault_is_assert f) h) (fun (f : IRFault) (_ : Eq IRConfig (ir_steps k m c) (IRConfig.halted (IROutcome.type_error f))) (h : ir_run_ok (ir_ret_post Q) (ir_config_outcome (IRConfig.halted (IROutcome.type_error f)))) => h) (fun (f : IRFault) (_ : Eq IRConfig (ir_steps k m c) (IRConfig.halted (IROutcome.unmodelled f))) (h : ir_run_ok (ir_ret_post Q) (ir_config_outcome (IRConfig.halted (IROutcome.unmodelled f)))) => h) (fun (f : IRFault) (_ : Eq IRConfig (ir_steps k m c) (IRConfig.halted (IROutcome.stuck f))) (h : ir_run_ok (ir_ret_post Q) (ir_config_outcome (IRConfig.halted (IROutcome.stuck f)))) => h) (fun (he : Eq IRConfig (ir_steps k m c) (IRConfig.halted IROutcome.fuel_out)) (_ : ir_run_ok (ir_ret_post Q) (ir_config_outcome (IRConfig.halted IROutcome.fuel_out))) => ir_stk_split_halted m r k c IROutcome.fuel_out (ir_stk_clear_of_mid m k c (Eq.subst IRConfig (fun (c1 : IRConfig) => Eq Bool (ir_halt_mid c1) Bool.true) (IRConfig.halted IROutcome.fuel_out) (ir_steps k m c) (Eq.symm IRConfig (ir_steps k m c) (IRConfig.halted IROutcome.fuel_out) he) (Eq.refl Bool Bool.true))) he) o) (ir_steps k m c) (Eq.refl IRConfig (ir_steps k m c)) hro";
const SRC_CTR_TRI_STACK: &str = "def ir_ctr_tri_stack (m : IRModule) (E : IRList Nat -> IRList IRFrame -> IRMachine) (Q : IRList IRMemSlot -> Nat -> IRList IRScalar -> Prop) (n : Nat) (hc : ir_ctr_at m E Q n) (hE : forall (d : IRList Nat) (r : IRList IRFrame), Eq IRMachine (E d r) (ir_mach_stack (E d (IRList.nil IRFrame)) r)) (d : IRList Nat) (r : IRList IRFrame) (k : Nat) (j : Nat) (hk : Eq Nat (Nat.add k j) n) : ir_stk_tri Q r (ir_steps k m (IRConfig.running (E d (IRList.nil IRFrame)))) (ir_steps k m (IRConfig.running (E d r))) := Eq.subst IRMachine (fun (x : IRMachine) => ir_stk_tri Q r (ir_steps k m (IRConfig.running (E d (IRList.nil IRFrame)))) (ir_steps k m (IRConfig.running x))) (ir_mach_stack (E d (IRList.nil IRFrame)) r) (E d r) (Eq.symm IRMachine (E d r) (ir_mach_stack (E d (IRList.nil IRFrame)) r) (hE d r)) (ir_stk_tri_of_run m Q r k (IRConfig.running (E d (IRList.nil IRFrame))) (ir_ctr_tri m E Q n hc d k j hk))";
const SRC_CTR_RET_POST_STACK: &str = "def ir_ctr_ret_post_stack (m : IRModule) (E : IRList Nat -> IRList IRFrame -> IRMachine) (Q : IRList IRMemSlot -> Nat -> IRList IRScalar -> Prop) (n : Nat) (hc : ir_ctr_at m E Q n) (d : IRList Nat) (j : Nat) (i : Nat) (hk : Eq Nat (Nat.add (Nat.add ir_d1 j) i) n) (fk : IRFrame) (mem2 : IRList IRMemSlot) (na2 : Nat) (fn : IRFunc) (b : IRBlock) (ids : IRList Nat) (rs : IRList Nat) (hr : Eq IRConfig (ir_steps j m (IRConfig.running (E d (IRList.nil IRFrame)))) (IRConfig.running (IRMachine.mk (IRList.cons IRFrame fk (IRList.nil IRFrame)) mem2 na2))) (hf : Eq (IROption IRFunc) (ir_func_find (ir_mod_funcs m) (ir_frame_func fk)) (IROption.some IRFunc fn)) (hb : Eq (IROption IRBlock) (ir_block_find (ir_func_blocks fn) (ir_frame_block fk)) (IROption.some IRBlock b)) (hn : Eq (IROption IRNode) (ir_nodes_get (ir_block_nodes b) (ir_frame_pc fk)) (IROption.some IRNode (IRNode.mk (IRInst.ret ids) rs))) : ir_ret_post Q (IROutcome.ret (ir_resolve (IRMachine.mk (IRList.cons IRFrame fk (IRList.nil IRFrame)) mem2 na2) ids)) := Eq.subst IRConfig (fun (c1 : IRConfig) => ir_run_ok (ir_ret_post Q) (ir_config_outcome c1)) (ir_steps (Nat.add ir_d1 j) m (IRConfig.running (E d (IRList.nil IRFrame)))) (IRConfig.halted (IROutcome.ret (ir_resolve (IRMachine.mk (IRList.cons IRFrame fk (IRList.nil IRFrame)) mem2 na2) ids))) (ir_stk_split_ret_standalone m j (IRConfig.running (E d (IRList.nil IRFrame))) fk mem2 na2 fn b ids rs hr hf hb hn) (ir_ctr_tri m E Q n hc d (Nat.add ir_d1 j) i hk)";
const SRC_CTR_TRI_STACK_LZD_DEREF: &str = "def ir_ctr_tri_stack_lzd_deref (mem : IRList IRMemSlot) (p : Nat) (b : Nat) (na : Nat) (hlt : Eq Bool (ir_nat_ltb p na) Bool.true) (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem p) (IROption.some IRMemSlot (IRMemSlot.mk p (IRScalar.ptr_ (Nat.succ b)) Bool.true))) (hcb : Eq IRStepResult (ir_borrow_eval (ir_cell na IRScalar.undef_ mem) (IRScalar.ptr_ (Nat.add (Nat.succ b) ir_d16))) (IRStepResult.value (IRScalar.ptr_ (Nat.add (Nat.succ b) ir_d16)))) (n : Nat) (d : IRList Nat) (r : IRList IRFrame) (k : Nat) (j : Nat) (hk : Eq Nat (Nat.add k j) n) : ir_stk_tri {POST} r (ir_steps k ir_lzd_module (IRConfig.running (ir_lzd_dmach mem p na d (IRList.nil IRFrame)))) (ir_steps k ir_lzd_module (IRConfig.running (ir_lzd_dmach mem p na d r))) := ir_ctr_tri_stack ir_lzd_module (ir_lzd_dmach mem p na) {POST} n (ir_lzd_deref_ctr mem p b na hlt h hcb n) (fun (d0 : IRList Nat) (r0 : IRList IRFrame) => Eq.refl IRMachine (ir_lzd_dmach mem p na d0 r0)) d r k j hk";
const SRC_CTR_HEAP_EXACT_REFUTED: &str = "def ir_ctr_heap_exact_refuted (C : Prop) (H : forall (m : IRModule) (E : IRList Nat -> IRList IRFrame -> IRMachine) (Q : IRList IRMemSlot -> Nat -> IRList IRScalar -> Prop) (n : Nat), ir_ctr_at m E Q n -> forall (d : IRList Nat) (j : Nat) (i : Nat), Eq Nat (Nat.add (Nat.add ir_d1 j) i) n -> forall (fk : IRFrame) (mem2 : IRList IRMemSlot) (na2 : Nat) (fn : IRFunc) (b : IRBlock) (ids : IRList Nat) (rs : IRList Nat), Eq IRConfig (ir_steps j m (IRConfig.running (E d (IRList.nil IRFrame)))) (IRConfig.running (IRMachine.mk (IRList.cons IRFrame fk (IRList.nil IRFrame)) mem2 na2)) -> Eq (IROption IRFunc) (ir_func_find (ir_mod_funcs m) (ir_frame_func fk)) (IROption.some IRFunc fn) -> Eq (IROption IRBlock) (ir_block_find (ir_func_blocks fn) (ir_frame_block fk)) (IROption.some IRBlock b) -> Eq (IROption IRNode) (ir_nodes_get (ir_block_nodes b) (ir_frame_pc fk)) (IROption.some IRNode (IRNode.mk (IRInst.ret ids) rs)) -> Q mem2 na2 (ir_resolve (IRMachine.mk (IRList.cons IRFrame fk (IRList.nil IRFrame)) mem2 na2) ids)) : C := ir_bool_false_ne_true C (H (IRModule.mk (IRList.cons IRFunc (IRFunc.mk ir_d0 ir_nl0 ir_d0 (ir_blk (IRBlock.mk ir_d0 ir_nl0 (IRList.cons IRNode (IRNode.mk (IRInst.ret ir_nl0) ir_nl0) (IRList.nil IRNode))) ir_blk0)) (IRList.nil IRFunc)) (IRList.nil IRGlobal)) (fun (d0 : IRList Nat) (r0 : IRList IRFrame) => IRMachine.mk (IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 Nat.zero (IRList.nil IRBinding) d0) r0) (IRList.nil IRMemSlot) Nat.zero) (fun (mem2 : IRList IRMemSlot) (na2 : Nat) (vs : IRList IRScalar) => ir_post_exact (IRList.cons IRMemSlot (IRMemSlot.mk Nat.zero IRScalar.undef_ Bool.true) (IRList.nil IRMemSlot)) Nat.zero (IRList.nil IRScalar) mem2 na2 vs) ir_d1 (fun (G : IROutcome -> Prop) (d : IRList Nat) (r : IRList IRFrame) (K : (forall (mem2 : IRList IRMemSlot) (na2 : Nat) (vs : IRList IRScalar), (fun (mem2 : IRList IRMemSlot) (na2 : Nat) (vs : IRList IRScalar) => ir_post_exact (IRList.cons IRMemSlot (IRMemSlot.mk Nat.zero IRScalar.undef_ Bool.true) (IRList.nil IRMemSlot)) Nat.zero (IRList.nil IRScalar) mem2 na2 vs) mem2 na2 vs -> ir_safe G (IRModule.mk (IRList.cons IRFunc (IRFunc.mk ir_d0 ir_nl0 ir_d0 (ir_blk (IRBlock.mk ir_d0 ir_nl0 (IRList.cons IRNode (IRNode.mk (IRInst.ret ir_nl0) ir_nl0) (IRList.nil IRNode))) ir_blk0)) (IRList.nil IRFunc)) (IRList.nil IRGlobal)) ir_d1 (ir_ret_to d r mem2 na2 vs))) => IRList.rec IRFrame (fun (r0 : IRList IRFrame) => (forall (mem2 : IRList IRMemSlot) (na2 : Nat) (vs : IRList IRScalar), (fun (mem2 : IRList IRMemSlot) (na2 : Nat) (vs : IRList IRScalar) => ir_post_exact (IRList.cons IRMemSlot (IRMemSlot.mk Nat.zero IRScalar.undef_ Bool.true) (IRList.nil IRMemSlot)) Nat.zero (IRList.nil IRScalar) mem2 na2 vs) mem2 na2 vs -> ir_safe G (IRModule.mk (IRList.cons IRFunc (IRFunc.mk ir_d0 ir_nl0 ir_d0 (ir_blk (IRBlock.mk ir_d0 ir_nl0 (IRList.cons IRNode (IRNode.mk (IRInst.ret ir_nl0) ir_nl0) (IRList.nil IRNode))) ir_blk0)) (IRList.nil IRFunc)) (IRList.nil IRGlobal)) ir_d1 (ir_ret_to d r0 mem2 na2 vs)) -> ir_safe G (IRModule.mk (IRList.cons IRFunc (IRFunc.mk ir_d0 ir_nl0 ir_d0 (ir_blk (IRBlock.mk ir_d0 ir_nl0 (IRList.cons IRNode (IRNode.mk (IRInst.ret ir_nl0) ir_nl0) (IRList.nil IRNode))) ir_blk0)) (IRList.nil IRFunc)) (IRList.nil IRGlobal)) ir_d1 (IRConfig.running (IRMachine.mk (IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 Nat.zero (IRList.nil IRBinding) d) r0) (IRList.nil IRMemSlot) Nat.zero))) (fun (K0 : (forall (mem2 : IRList IRMemSlot) (na2 : Nat) (vs : IRList IRScalar), (fun (mem2 : IRList IRMemSlot) (na2 : Nat) (vs : IRList IRScalar) => ir_post_exact (IRList.cons IRMemSlot (IRMemSlot.mk Nat.zero IRScalar.undef_ Bool.true) (IRList.nil IRMemSlot)) Nat.zero (IRList.nil IRScalar) mem2 na2 vs) mem2 na2 vs -> ir_safe G (IRModule.mk (IRList.cons IRFunc (IRFunc.mk ir_d0 ir_nl0 ir_d0 (ir_blk (IRBlock.mk ir_d0 ir_nl0 (IRList.cons IRNode (IRNode.mk (IRInst.ret ir_nl0) ir_nl0) (IRList.nil IRNode))) ir_blk0)) (IRList.nil IRFunc)) (IRList.nil IRGlobal)) ir_d1 (ir_ret_to d (IRList.nil IRFrame) mem2 na2 vs))) => K0 (IRList.cons IRMemSlot (IRMemSlot.mk Nat.zero IRScalar.undef_ Bool.true) (IRList.nil IRMemSlot)) Nat.zero (IRList.nil IRScalar) (ir_post_exact_refl (IRList.cons IRMemSlot (IRMemSlot.mk Nat.zero IRScalar.undef_ Bool.true) (IRList.nil IRMemSlot)) Nat.zero (IRList.nil IRScalar))) (fun (g : IRFrame) (r2 : IRList IRFrame) (_ : (forall (mem2 : IRList IRMemSlot) (na2 : Nat) (vs : IRList IRScalar), (fun (mem2 : IRList IRMemSlot) (na2 : Nat) (vs : IRList IRScalar) => ir_post_exact (IRList.cons IRMemSlot (IRMemSlot.mk Nat.zero IRScalar.undef_ Bool.true) (IRList.nil IRMemSlot)) Nat.zero (IRList.nil IRScalar) mem2 na2 vs) mem2 na2 vs -> ir_safe G (IRModule.mk (IRList.cons IRFunc (IRFunc.mk ir_d0 ir_nl0 ir_d0 (ir_blk (IRBlock.mk ir_d0 ir_nl0 (IRList.cons IRNode (IRNode.mk (IRInst.ret ir_nl0) ir_nl0) (IRList.nil IRNode))) ir_blk0)) (IRList.nil IRFunc)) (IRList.nil IRGlobal)) ir_d1 (ir_ret_to d r2 mem2 na2 vs)) -> ir_safe G (IRModule.mk (IRList.cons IRFunc (IRFunc.mk ir_d0 ir_nl0 ir_d0 (ir_blk (IRBlock.mk ir_d0 ir_nl0 (IRList.cons IRNode (IRNode.mk (IRInst.ret ir_nl0) ir_nl0) (IRList.nil IRNode))) ir_blk0)) (IRList.nil IRFunc)) (IRList.nil IRGlobal)) ir_d1 (IRConfig.running (IRMachine.mk (IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 Nat.zero (IRList.nil IRBinding) d) r2) (IRList.nil IRMemSlot) Nat.zero))) (_ : (forall (mem2 : IRList IRMemSlot) (na2 : Nat) (vs : IRList IRScalar), (fun (mem2 : IRList IRMemSlot) (na2 : Nat) (vs : IRList IRScalar) => ir_post_exact (IRList.cons IRMemSlot (IRMemSlot.mk Nat.zero IRScalar.undef_ Bool.true) (IRList.nil IRMemSlot)) Nat.zero (IRList.nil IRScalar) mem2 na2 vs) mem2 na2 vs -> ir_safe G (IRModule.mk (IRList.cons IRFunc (IRFunc.mk ir_d0 ir_nl0 ir_d0 (ir_blk (IRBlock.mk ir_d0 ir_nl0 (IRList.cons IRNode (IRNode.mk (IRInst.ret ir_nl0) ir_nl0) (IRList.nil IRNode))) ir_blk0)) (IRList.nil IRFunc)) (IRList.nil IRGlobal)) ir_d1 (ir_ret_to d (IRList.cons IRFrame g r2) mem2 na2 vs))) => Eq.refl Bool Bool.true) r K) (IRList.nil Nat) Nat.zero Nat.zero (Eq.refl Nat ir_d1) (IRFrame.mk ir_d0 ir_d0 Nat.zero (IRList.nil IRBinding) (IRList.nil Nat)) (IRList.nil IRMemSlot) Nat.zero (IRFunc.mk ir_d0 ir_nl0 ir_d0 (ir_blk (IRBlock.mk ir_d0 ir_nl0 (IRList.cons IRNode (IRNode.mk (IRInst.ret ir_nl0) ir_nl0) (IRList.nil IRNode))) ir_blk0)) (IRBlock.mk ir_d0 ir_nl0 (IRList.cons IRNode (IRNode.mk (IRInst.ret ir_nl0) ir_nl0) (IRList.nil IRNode))) ir_nl0 ir_nl0 (Eq.refl IRConfig (IRConfig.running (IRMachine.mk (IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 Nat.zero (IRList.nil IRBinding) (IRList.nil Nat)) (IRList.nil IRFrame)) (IRList.nil IRMemSlot) Nat.zero))) (Eq.refl (IROption IRFunc) (IROption.some IRFunc (IRFunc.mk ir_d0 ir_nl0 ir_d0 (ir_blk (IRBlock.mk ir_d0 ir_nl0 (IRList.cons IRNode (IRNode.mk (IRInst.ret ir_nl0) ir_nl0) (IRList.nil IRNode))) ir_blk0)))) (Eq.refl (IROption IRBlock) (IROption.some IRBlock (IRBlock.mk ir_d0 ir_nl0 (IRList.cons IRNode (IRNode.mk (IRInst.ret ir_nl0) ir_nl0) (IRList.nil IRNode))))) (Eq.refl (IROption IRNode) (IROption.some IRNode (IRNode.mk (IRInst.ret ir_nl0) ir_nl0))) (fun (m0 : IRList IRMemSlot) (_ : Nat) (_ : IRList IRScalar) => Eq Bool (IRList.rec IRMemSlot (fun (_ : IRList IRMemSlot) => Bool) Bool.false (fun (_ : IRMemSlot) (_ : IRList IRMemSlot) (_ : Bool) => Bool.true) m0) Bool.true) (Eq.refl Bool Bool.true))";
const DEREF_POST: &str = "(ir_post_exact (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) (ir_vl1 (IRScalar.ptr_ (Nat.add (Nat.succ b) ir_d16))))";

/// The names this stage registers, in registration order.
pub const CTR_STACK_NAMES: &[&str] = &[
    "ir_step_of_nil",
    "ir_halt_mid_of_ret",
    "ir_stk_nonnil_of_mid",
    "ir_stk_notbot_of_mid",
    "ir_stk_clear_of_mid",
    "ir_stk_tri",
    "ir_stk_tri_of_run",
    "ir_ctr_tri_stack",
    "ir_ctr_ret_post_stack",
    "ir_ctr_tri_stack_lzd_deref",
    "ir_ctr_heap_exact_refuted",
];

/// `(source, description)`, positionally paired with [`CTR_STACK_NAMES`].
const DECLS: &[(&str, &str)] = &[
    (
        SRC_STEP_OF_NIL,
        "ir_step_of_nil: a machine whose frame list the Bool test calls empty steps to stuck no_frame -- IRMachine.rec, IRList.rec on the frames, the cons case refuted from the premise. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_HALT_MID_OF_RET,
        "ir_halt_mid_of_ret: a configuration that has halted with a return is never a mid halt, however many steps later it is read -- a halted configuration is its own successor (ir_steps_halted) and IROutcome.rec refutes every non-ret outcome from the premise. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_STK_NONNIL_OF_MID,
        "ir_stk_nonnil_of_mid: if the run from a machine's first step ends in a mid halt, the machine's frame list is not empty -- an empty one steps to stuck no_frame (ir_step_of_nil), a halt that persists and that ir_halt_mid refuses. A Bool equation convoy on ir_frames_is_nil. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_STK_NOTBOT_OF_MID,
        "ir_stk_notbot_of_mid: and the machine is not a bottom ret -- a bottom ret's step halts with a return (ir_stk_botret_ret, the minted classifier converse), which ir_halt_mid_of_ret refuses. A Bool equation convoy on ir_stk_botret. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_STK_CLEAR_OF_MID,
        "ir_stk_clear_of_mid: *** A RUN THAT HALTS IN THE MIDDLE OF THE COMMUTING CLASS WAS CLEAR ALL ALONG. *** If n steps from c end in a halt that is neither a return nor stuck no_frame, then ir_stk_clear n m c -- every running prefix had a nonempty frame list and was not a bottom ret. Nat.rec on n generalised over the configuration, the two guards built by ir_bool_guard_intro from the two lemmas above and the rest from the induction hypothesis. The converse direction of ir_stk_clear_of_running for halted runs, and what lets E1's F case carry a panicking callee to every caller stack without the caller knowing in advance that it was clear. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_STK_TRI,
        "ir_stk_tri: *** THE THREE-WAY READING AT A CALLER STACK r. *** Over the callee's run at the empty caller stack (c) and at r (cs) after the same number of steps: if the callee is still RUNNING, cs is exactly its machine with r beneath the frames; if it HALTED with ub f, f is assert_failed (a sanctioned panic) and cs halted identically; if it RETURNED vs, some final heap and counter satisfy the post for vs (ir_ret_post); every other halt is impossible (forall C, C), except the fuel_out halt the type admits and the machine never produces, where cs halts identically too. No Or / Exists: the cases are the recursors on the configuration and the outcome. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_STK_TRI_OF_RUN,
        "ir_stk_tri_of_run: the reading at r follows from the OUTCOME reading at the empty stack -- for any configuration c, if the run from c satisfies ir_run_ok (ir_ret_post Q) after k steps, then ir_stk_tri Q r holds of the run from c and the run from c stacked over r. An equation convoy on the k-step configuration: running is E1's R (ir_stk_split_running through ir_stk_clear_of_running); a sanctioned panic and fuel_out are E1's F (ir_stk_split_halted through ir_stk_clear_of_mid); a return and every refused halt are the outcome reading itself. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_CTR_TRI_STACK,
        "ir_ctr_tri_stack: *** E2's OPEN ITEM -- A CONTRACT READ THREE WAYS AT AN ARBITRARY CALLER STACK. *** For a contract at budget n and an entry that is its empty-stack entry with the caller stack appended (hE; Eq.refl for every single-frame entry), for every dests d, every caller stack r and every k with k + j = n: the run entered over r is inside the callee with r untouched, or has halted with a sanctioned panic, or the callee has returned values the post admits (ir_stk_tri). ir_ctr_tri at the empty stack, lifted by ir_stk_tri_of_run, transported along hE. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_CTR_RET_POST_STACK,
        "ir_ctr_ret_post_stack: the return case made exact at the FIRST return -- if the callee's run at the empty stack is running at a single frame that fetches ret after j steps (E1's T premises) and 1 + j fits in the budget, the values it returns satisfy the post. With ir_stk_activation_dests_gen, which says the run entered over ANY caller stack r returns into r through ir_ret_to with exactly those values and the machine's own heap, this is the exact return configuration together with its post. ir_ctr_tri at 1 + j, rewritten along ir_stk_split_ret_standalone. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_CTR_TRI_STACK_LZD_DEREF,
        "ir_ctr_tri_stack_lzd_deref: *** WITNESS. *** The derived deref chain's contract (ir_lzd_deref_ctr, E2's exact forty-step run through the adapter) read three ways at an ARBITRARY caller stack, at every budget, under exactly the premises ir_lzd_deref_ctr takes. The entry premise is Eq.refl: ir_lzd_dmach is a single frame over its caller stack. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_CTR_HEAP_EXACT_REFUTED,
        "ir_ctr_heap_exact_refuted: *** THE HEAP-EXACT READING DOES NOT FOLLOW FROM A CONTRACT, kernel-checked. *** Assume the return case of the reading with the post at the heap the machine ACTUALLY holds when it returns (ir_ctr_ret_post_stack with Q mem2 na2 in place of ir_ret_post Q); instantiate it at a one-function module whose body is `ret []`, entered at an empty heap, with the post `the final heap is a one-cell heap`. The contract holds at budget 1 for every G, d and caller stack -- at the empty stack the return halts with values only and the heap is never observed, over a caller it is running -- yet the heap-exact reading would put a cell in the empty heap. So the value-level reading ir_stk_tri states (some heap satisfies the post) is exactly what the continuation form gives, and the exact return CONFIGURATION comes from ir_stk_activation_dests_gen instead. DerivedProved, zero axiom_deps.",
    ),
];

fn expand(source: &str) -> String {
    source.replace("{POST}", DEREF_POST)
}

impl Specification {
    /// The three-way reading at an arbitrary caller stack. MUST follow
    /// `add_eval_ir_lzd_sctr` (`ir_lzd_deref_ctr`), `add_eval_ir_ctr`
    /// (`ir_ctr_at`, `ir_ctr_tri`, `ir_ret_post`), `add_eval_ir_stack_axes_minted`
    /// (`ir_stk_botret_ret`, `ir_halt_mid`) and `add_eval_ir_stack_split`.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check -- by name.
    pub(super) fn add_eval_ir_ctr_stack(&mut self) -> Result<(), SpecError> {
        for (source, description) in DECLS {
            self.add_recursive_def(&expand(source), description)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sources_balanced_ascii_and_named() {
        assert_eq!(DECLS.len(), CTR_STACK_NAMES.len());
        for ((src, _), name) in DECLS.iter().zip(CTR_STACK_NAMES) {
            let src = expand(src);
            assert!(src.is_ascii(), "spec sources stay ASCII");
            assert_eq!(src.matches('(').count(), src.matches(')').count(), "{name}");
            assert!(src.starts_with(&format!("def {name} ")), "{name}");
            assert!(!src.contains('{'), "{name}: an unexpanded placeholder");
        }
    }

    /// The reading is at an ARBITRARY caller stack -- `r` is a binder of the
    /// theorem, never the empty list -- and it is proved from the contract.
    #[test]
    fn test_the_reading_quantifies_the_caller_stack() {
        let header = SRC_CTR_TRI_STACK.split(" := ").next().unwrap_or_default();
        assert!(header.contains("(r : IRList IRFrame)"));
        assert!(header.contains("(hc : ir_ctr_at m E Q n)"));
        assert!(header.contains("(IRConfig.running (E d r))"));
        assert!(SRC_CTR_TRI_STACK.contains("ir_ctr_tri m E Q n hc"));
    }
}
