// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//! **`TypeChecker::infer_type`'s local obligation in STEP-INDEXED form** -- the
//! SECOND instance of the E2 contract device (`eval_ir_ctr.rs`;
//! `designs/2026-09-24-e2-contract-soundness.md` §7-§8).
//!
//! The first instance (`eval_ir_lzd_sctr.rs`) is `Level::is_zero`: a body that
//! calls ITSELF, over a concrete five-function module. This one is chosen to
//! differ on every axis the D5 cost question is about:
//!
//! * the body is the designated target's own minted body (`ir_it_func`: six
//!   blocks, 36 nodes, two call sites), over an ABSTRACT module
//!   `IRModule.mk fs gs` -- every step is a rewrite through `h0` / `h1` / `h2`
//!   (the step lemmas of `eval_ir_itf.rs`), never a computation;
//! * it calls two OTHER functions (tick_heartbeat, infer_type_fast) and itself
//!   not at all;
//! * its recursion group is MUTUAL -- `eval_ir_it_pc.rs` puts it in a
//!   three-member table with its two callees.
//!
//! `ir_it_top_sseg` is the body's LOCAL obligation: from the heartbeat's
//! contract at budget `n` and the inference call's contract at `n` (for every
//! return the heartbeat's post admits), the body meets its contract at
//! `Nat.succ n`, whose post `ir_it_tpost` is the TRANSPORT property: the value
//! infer_type returns is a value infer_type_fast returned. The budget pays for
//! the alloca; the heartbeat call's push, the dispatch, the inference call's push
//! and the transport tail are padded through the same step lemmas
//! `ir_it_ag_activation` splices. MINTED by `scripts/gen_it_sctr.py`, ONE
//! LEMMA PER CALL (D5's re-decided remedy; design section 9):
//! `ir_it_top_sseg_r1` is the safety of the configuration the body resumes at
//! after the heartbeat returned OK (the dispatch and the inference call, whose
//! continuation applies `_r2`), and `ir_it_top_sseg_r2` that after the inference
//! call returned (the transport tail and the `ret`). The obligation's statement
//! is unchanged; no term nests one call's continuation inside another's.
//!
//! Two premises on the callees' posts are not conveniences, and the pins here
//! say why: `hq1` (the heartbeat answers OK) because the Err arm FAULTS on this
//! machine (`ir_it_err_arm_refutes`: the producer's undef-then-insertfield
//! idiom, `ir_undef_then_insertfield_faults`), and `hq2` (the inference call
//! returns an aggregate and the Result slot is still live) because the store
//! and load of the transport tail read exactly those.
//!
//! Full-only: the step lemmas it cites are registered by `add_eval_ir_itf`.

use super::{SpecError, Specification};

const SRC_HB_ENTRY: &str = "def ir_it_hb_entry (g1 : IRFunc) (p : Nat) (mem : IRList IRMemSlot) (na : Nat) (d : IRList Nat) (r : IRList IRFrame) : IRMachine := IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk (ir_func_id g1) (ir_func_entry g1) Nat.zero (ir_bind_params (ir_func_params g1) (ir_vl1 (IRScalar.ptr_ p)) (@IRList.nil IRBinding)) d) r) mem na";

const SRC_FAST_ENTRY: &str = "def ir_it_fast_entry (g2 : IRFunc) (p : Nat) (q : Nat) (mem : IRList IRMemSlot) (na : Nat) (d : IRList Nat) (r : IRList IRFrame) : IRMachine := IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk (ir_func_id g2) (ir_func_entry g2) Nat.zero (ir_bind_params (ir_func_params g2) (ir_vl2 (IRScalar.ptr_ p) (IRScalar.ptr_ q)) (@IRList.nil IRBinding)) d) r) mem na";

const SRC_TPOST: &str = "def ir_it_tpost (QH : Nat -> IRList IRMemSlot -> Nat -> IRList IRMemSlot -> Nat -> IRList IRScalar -> Prop) (QF : Nat -> Nat -> IRList IRMemSlot -> Nat -> IRList IRMemSlot -> Nat -> IRList IRScalar -> Prop) (p : Nat) (q : Nat) (mem : IRList IRMemSlot) (na : Nat) (mem3 : IRList IRMemSlot) (na3 : Nat) (vs : IRList IRScalar) : Prop := forall (C : Prop), (forall (mem1 : IRList IRMemSlot) (na1 : Nat) (vs1 : IRList IRScalar) (mem2 : IRList IRMemSlot), QH p (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na) mem1 na1 vs1 -> QF p q mem1 na1 mem2 na3 vs -> C) -> C";

// ── minted by scripts/gen_it_sctr.py -- do not edit by hand ──────────────
const SRC_IR_IT_TOP_SSEG_R2: &str = "def ir_it_top_sseg_r2 (fs : IRList IRFunc) (gs : IRList IRGlobal) (QH : Nat -> IRList IRMemSlot -> Nat -> IRList IRMemSlot -> Nat -> IRList IRScalar -> Prop) (QF : Nat -> Nat -> IRList IRMemSlot -> Nat -> IRList IRMemSlot -> Nat -> IRList IRScalar -> Prop) (p : Nat) (q : Nat) (mem : IRList IRMemSlot) (na : Nat) (n : Nat) (h0 : @Eq (IROption IRFunc) (ir_func_find fs ir_d0) (@IROption.some IRFunc ir_it_func)) (G : IROutcome -> Prop) (ds : IRList Nat) (rest : IRList IRFrame) (hK : forall (mem3 : IRList IRMemSlot) (na3 : Nat) (vs : IRList IRScalar), ir_it_tpost QH QF p q mem na mem3 na3 vs -> ir_safe G (IRModule.mk fs gs) (Nat.succ n) (ir_ret_to ds rest mem3 na3 vs)) (mem1 : IRList IRMemSlot) (na1 : Nat) (vs1 : IRList IRScalar) (hqh : QH p (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na) mem1 na1 vs1) (sp : IRScalar) (mem2 : IRList IRMemSlot) (na2 : Nat) (vs2 : IRList IRScalar) (hqf : QF p q mem1 na1 mem2 na2 vs2) (spv : IRScalar) (v0 : IRScalar) (hv2 : @Eq (IRList IRScalar) vs2 (ir_vl1 (IRScalar.aggv spv))) (hslot : @Eq (IROption IRMemSlot) (ir_mem_lookup mem2 na) (@IROption.some IRMemSlot (IRMemSlot.mk na v0 Bool.true))) : ir_safe G (IRModule.mk fs gs) n (ir_ret_to (ir_nl1 ir_d29) (@IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d5 ir_d1 (@IRList.cons IRBinding (IRBinding.mk ir_d4 (IRScalar.int_ ir_d0)) (@IRList.cons IRBinding (IRBinding.mk ir_d3 (ir_it_hb_answer sp)) (@IRList.cons IRBinding (IRBinding.mk ir_d2 (IRScalar.ptr_ na)) (@IRList.cons IRBinding (IRBinding.mk ir_d0 (IRScalar.ptr_ p)) (@IRList.cons IRBinding (IRBinding.mk ir_d1 (IRScalar.ptr_ q)) (@IRList.nil IRBinding)))))) ds) rest) mem2 na2 (ir_vl1 (IRScalar.aggv spv))) := (ir_safe_pad G (IRModule.mk fs gs) n ir_d3 (IRConfig.running (ir_it3_smach p q na sp spv ds rest mem2 na2)) (Eq.subst IRConfig (fun (c : IRConfig) => ir_safe G (IRModule.mk fs gs) n c) (IRConfig.running (ir_it3_lmach p q na sp spv ds rest mem2 na2)) (ir_steps ir_d3 (IRModule.mk fs gs) (IRConfig.running (ir_it3_smach p q na sp spv ds rest mem2 na2))) (Eq.symm IRConfig (ir_steps ir_d3 (IRModule.mk fs gs) (IRConfig.running (ir_it3_smach p q na sp spv ds rest mem2 na2))) (IRConfig.running (ir_it3_lmach p q na sp spv ds rest mem2 na2)) (ir_it_seam3_ext fs gs h0 (IRConfig.running (ir_it3_smach p q na sp spv ds rest mem2 na2)) (ir_it3_lmach p q na sp spv ds rest mem2 na2) (ir_it_transport3_at p q na sp spv ds rest mem2 na2 v0 hslot))) (ir_safe_pad G (IRModule.mk fs gs) n ir_d1 (IRConfig.running (ir_it3_lmach p q na sp spv ds rest mem2 na2)) (Eq.subst IRConfig (fun (c : IRConfig) => ir_safe G (IRModule.mk fs gs) n c) (ir_ret_to ds rest (ir_mem_update mem2 na (IRScalar.aggv spv)) na2 (ir_vl1 (IRScalar.aggv spv))) (ir_steps ir_d1 (IRModule.mk fs gs) (IRConfig.running (ir_it3_lmach p q na sp spv ds rest mem2 na2))) (Eq.symm IRConfig (ir_steps ir_d1 (IRModule.mk fs gs) (IRConfig.running (ir_it3_lmach p q na sp spv ds rest mem2 na2))) (ir_ret_to ds rest (ir_mem_update mem2 na (IRScalar.aggv spv)) na2 (ir_vl1 (IRScalar.aggv spv))) (ir_it_ag_ret_steps1 fs gs p q na sp spv ds rest mem2 na2 h0)) (ir_safe_down G (IRModule.mk fs gs) n (ir_ret_to ds rest (ir_mem_update mem2 na (IRScalar.aggv spv)) na2 (ir_vl1 (IRScalar.aggv spv))) (hK (ir_mem_update mem2 na (IRScalar.aggv spv)) na2 (ir_vl1 (IRScalar.aggv spv)) (fun (C : Prop) (k : forall (m1 : IRList IRMemSlot) (k1 : Nat) (w1 : IRList IRScalar) (m2 : IRList IRMemSlot), QH p (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na) m1 k1 w1 -> QF p q m1 k1 m2 na2 (ir_vl1 (IRScalar.aggv spv)) -> C) => k mem1 na1 vs1 mem2 hqh (Eq.subst (IRList IRScalar) (fun (v : IRList IRScalar) => QF p q mem1 na1 mem2 na2 v) vs2 (ir_vl1 (IRScalar.aggv spv)) hv2 hqf))))))))";
const SRC_IR_IT_TOP_SSEG_R1: &str = "def ir_it_top_sseg_r1 (fs : IRList IRFunc) (gs : IRList IRGlobal) (g2 : IRFunc) (QH : Nat -> IRList IRMemSlot -> Nat -> IRList IRMemSlot -> Nat -> IRList IRScalar -> Prop) (QF : Nat -> Nat -> IRList IRMemSlot -> Nat -> IRList IRMemSlot -> Nat -> IRList IRScalar -> Prop) (p : Nat) (q : Nat) (mem : IRList IRMemSlot) (na : Nat) (n : Nat) (h0 : @Eq (IROption IRFunc) (ir_func_find fs ir_d0) (@IROption.some IRFunc ir_it_func)) (h2 : @Eq (IROption IRFunc) (ir_func_find fs ir_d2) (@IROption.some IRFunc g2)) (hq2 : forall (mem1 : IRList IRMemSlot) (na1 : Nat) (vs1 : IRList IRScalar) (mem2 : IRList IRMemSlot) (na2 : Nat) (vs : IRList IRScalar), QH p (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na) mem1 na1 vs1 -> QF p q mem1 na1 mem2 na2 vs -> forall (C : Prop), (forall (spv : IRScalar) (v0 : IRScalar), @Eq (IRList IRScalar) vs (ir_vl1 (IRScalar.aggv spv)) -> @Eq (IROption IRMemSlot) (ir_mem_lookup mem2 na) (@IROption.some IRMemSlot (IRMemSlot.mk na v0 Bool.true)) -> C) -> C) (ihf : forall (mem1 : IRList IRMemSlot) (na1 : Nat) (vs1 : IRList IRScalar), QH p (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na) mem1 na1 vs1 -> ir_ctr_at (IRModule.mk fs gs) (ir_it_fast_entry g2 p q mem1 na1) (QF p q mem1 na1) n) (G : IROutcome -> Prop) (ds : IRList Nat) (rest : IRList IRFrame) (hK : forall (mem3 : IRList IRMemSlot) (na3 : Nat) (vs : IRList IRScalar), ir_it_tpost QH QF p q mem na mem3 na3 vs -> ir_safe G (IRModule.mk fs gs) (Nat.succ n) (ir_ret_to ds rest mem3 na3 vs)) (mem1 : IRList IRMemSlot) (na1 : Nat) (vs1 : IRList IRScalar) (hqh : QH p (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na) mem1 na1 vs1) (sp : IRScalar) : ir_safe G (IRModule.mk fs gs) n (ir_ret_to (ir_nl1 ir_d3) (@IRList.cons IRFrame (ir_it_dframe (@IRList.cons IRBinding (IRBinding.mk ir_d2 (IRScalar.ptr_ na)) (@IRList.cons IRBinding (IRBinding.mk ir_d0 (IRScalar.ptr_ p)) (@IRList.cons IRBinding (IRBinding.mk ir_d1 (IRScalar.ptr_ q)) (@IRList.nil IRBinding)))) ds) rest) mem1 na1 (ir_vl1 (ir_it_hb_answer sp))) := (ir_safe_pad G (IRModule.mk fs gs) n ir_d3 (ir_ret_to (ir_nl1 ir_d3) (@IRList.cons IRFrame (ir_it_dframe (@IRList.cons IRBinding (IRBinding.mk ir_d2 (IRScalar.ptr_ na)) (@IRList.cons IRBinding (IRBinding.mk ir_d0 (IRScalar.ptr_ p)) (@IRList.cons IRBinding (IRBinding.mk ir_d1 (IRScalar.ptr_ q)) (@IRList.nil IRBinding)))) ds) rest) mem1 na1 (ir_vl1 (ir_it_hb_answer sp))) (Eq.subst IRConfig (fun (c : IRConfig) => ir_safe G (IRModule.mk fs gs) n c) (IRConfig.running (ir_it_dispatch_end sp (@IRList.cons IRBinding (IRBinding.mk ir_d2 (IRScalar.ptr_ na)) (@IRList.cons IRBinding (IRBinding.mk ir_d0 (IRScalar.ptr_ p)) (@IRList.cons IRBinding (IRBinding.mk ir_d1 (IRScalar.ptr_ q)) (@IRList.nil IRBinding)))) ds rest mem1 na1)) (ir_steps ir_d3 (IRModule.mk fs gs) (ir_ret_to (ir_nl1 ir_d3) (@IRList.cons IRFrame (ir_it_dframe (@IRList.cons IRBinding (IRBinding.mk ir_d2 (IRScalar.ptr_ na)) (@IRList.cons IRBinding (IRBinding.mk ir_d0 (IRScalar.ptr_ p)) (@IRList.cons IRBinding (IRBinding.mk ir_d1 (IRScalar.ptr_ q)) (@IRList.nil IRBinding)))) ds) rest) mem1 na1 (ir_vl1 (ir_it_hb_answer sp)))) (Eq.symm IRConfig (ir_steps ir_d3 (IRModule.mk fs gs) (ir_ret_to (ir_nl1 ir_d3) (@IRList.cons IRFrame (ir_it_dframe (@IRList.cons IRBinding (IRBinding.mk ir_d2 (IRScalar.ptr_ na)) (@IRList.cons IRBinding (IRBinding.mk ir_d0 (IRScalar.ptr_ p)) (@IRList.cons IRBinding (IRBinding.mk ir_d1 (IRScalar.ptr_ q)) (@IRList.nil IRBinding)))) ds) rest) mem1 na1 (ir_vl1 (ir_it_hb_answer sp)))) (IRConfig.running (ir_it_dispatch_end sp (@IRList.cons IRBinding (IRBinding.mk ir_d2 (IRScalar.ptr_ na)) (@IRList.cons IRBinding (IRBinding.mk ir_d0 (IRScalar.ptr_ p)) (@IRList.cons IRBinding (IRBinding.mk ir_d1 (IRScalar.ptr_ q)) (@IRList.nil IRBinding)))) ds rest mem1 na1)) (ir_it_dispatch_seg_ext fs gs h0 sp (@IRList.cons IRBinding (IRBinding.mk ir_d2 (IRScalar.ptr_ na)) (@IRList.cons IRBinding (IRBinding.mk ir_d0 (IRScalar.ptr_ p)) (@IRList.cons IRBinding (IRBinding.mk ir_d1 (IRScalar.ptr_ q)) (@IRList.nil IRBinding)))) ds rest mem1 na1)) (ir_safe_pad G (IRModule.mk fs gs) n ir_d1 (IRConfig.running (ir_it_dispatch_end sp (@IRList.cons IRBinding (IRBinding.mk ir_d2 (IRScalar.ptr_ na)) (@IRList.cons IRBinding (IRBinding.mk ir_d0 (IRScalar.ptr_ p)) (@IRList.cons IRBinding (IRBinding.mk ir_d1 (IRScalar.ptr_ q)) (@IRList.nil IRBinding)))) ds rest mem1 na1)) (Eq.subst IRConfig (fun (c : IRConfig) => ir_safe G (IRModule.mk fs gs) n c) (IRConfig.running (ir_it_ag_push2_m g2 sp p q na ds rest mem1 na1)) (ir_steps ir_d1 (IRModule.mk fs gs) (IRConfig.running (ir_it_dispatch_end sp (@IRList.cons IRBinding (IRBinding.mk ir_d2 (IRScalar.ptr_ na)) (@IRList.cons IRBinding (IRBinding.mk ir_d0 (IRScalar.ptr_ p)) (@IRList.cons IRBinding (IRBinding.mk ir_d1 (IRScalar.ptr_ q)) (@IRList.nil IRBinding)))) ds rest mem1 na1))) (Eq.symm IRConfig (ir_steps ir_d1 (IRModule.mk fs gs) (IRConfig.running (ir_it_dispatch_end sp (@IRList.cons IRBinding (IRBinding.mk ir_d2 (IRScalar.ptr_ na)) (@IRList.cons IRBinding (IRBinding.mk ir_d0 (IRScalar.ptr_ p)) (@IRList.cons IRBinding (IRBinding.mk ir_d1 (IRScalar.ptr_ q)) (@IRList.nil IRBinding)))) ds rest mem1 na1))) (IRConfig.running (ir_it_ag_push2_m g2 sp p q na ds rest mem1 na1)) (ir_it_ag_call2_steps1 fs gs g2 sp p q na ds rest mem1 na1 h0 h2)) (ihf mem1 na1 vs1 hqh G (ir_nl1 ir_d29) (@IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d5 ir_d1 (@IRList.cons IRBinding (IRBinding.mk ir_d4 (IRScalar.int_ ir_d0)) (@IRList.cons IRBinding (IRBinding.mk ir_d3 (ir_it_hb_answer sp)) (@IRList.cons IRBinding (IRBinding.mk ir_d2 (IRScalar.ptr_ na)) (@IRList.cons IRBinding (IRBinding.mk ir_d0 (IRScalar.ptr_ p)) (@IRList.cons IRBinding (IRBinding.mk ir_d1 (IRScalar.ptr_ q)) (@IRList.nil IRBinding)))))) ds) rest) (fun (mem2 : IRList IRMemSlot) (na2 : Nat) (vs2 : IRList IRScalar) (hqf : QF p q mem1 na1 mem2 na2 vs2) => hq2 mem1 na1 vs1 mem2 na2 vs2 hqh hqf (ir_safe G (IRModule.mk fs gs) n (ir_ret_to (ir_nl1 ir_d29) (@IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d5 ir_d1 (@IRList.cons IRBinding (IRBinding.mk ir_d4 (IRScalar.int_ ir_d0)) (@IRList.cons IRBinding (IRBinding.mk ir_d3 (ir_it_hb_answer sp)) (@IRList.cons IRBinding (IRBinding.mk ir_d2 (IRScalar.ptr_ na)) (@IRList.cons IRBinding (IRBinding.mk ir_d0 (IRScalar.ptr_ p)) (@IRList.cons IRBinding (IRBinding.mk ir_d1 (IRScalar.ptr_ q)) (@IRList.nil IRBinding)))))) ds) rest) mem2 na2 vs2)) (fun (spv : IRScalar) (v0 : IRScalar) (hv2 : @Eq (IRList IRScalar) vs2 (ir_vl1 (IRScalar.aggv spv))) (hslot : @Eq (IROption IRMemSlot) (ir_mem_lookup mem2 na) (@IROption.some IRMemSlot (IRMemSlot.mk na v0 Bool.true))) => Eq.subst (IRList IRScalar) (fun (v : IRList IRScalar) => ir_safe G (IRModule.mk fs gs) n (ir_ret_to (ir_nl1 ir_d29) (@IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d5 ir_d1 (@IRList.cons IRBinding (IRBinding.mk ir_d4 (IRScalar.int_ ir_d0)) (@IRList.cons IRBinding (IRBinding.mk ir_d3 (ir_it_hb_answer sp)) (@IRList.cons IRBinding (IRBinding.mk ir_d2 (IRScalar.ptr_ na)) (@IRList.cons IRBinding (IRBinding.mk ir_d0 (IRScalar.ptr_ p)) (@IRList.cons IRBinding (IRBinding.mk ir_d1 (IRScalar.ptr_ q)) (@IRList.nil IRBinding)))))) ds) rest) mem2 na2 v)) (ir_vl1 (IRScalar.aggv spv)) vs2 (Eq.symm (IRList IRScalar) vs2 (ir_vl1 (IRScalar.aggv spv)) hv2) (ir_it_top_sseg_r2 fs gs QH QF p q mem na n h0 G ds rest hK mem1 na1 vs1 hqh sp mem2 na2 vs2 hqf spv v0 hv2 hslot))))))))";
const SRC_IR_IT_TOP_SSEG: &str = "def ir_it_top_sseg (fs : IRList IRFunc) (gs : IRList IRGlobal) (g1 : IRFunc) (g2 : IRFunc) (QH : Nat -> IRList IRMemSlot -> Nat -> IRList IRMemSlot -> Nat -> IRList IRScalar -> Prop) (QF : Nat -> Nat -> IRList IRMemSlot -> Nat -> IRList IRMemSlot -> Nat -> IRList IRScalar -> Prop) (p : Nat) (q : Nat) (mem : IRList IRMemSlot) (na : Nat) (n : Nat) (h0 : @Eq (IROption IRFunc) (ir_func_find fs ir_d0) (@IROption.some IRFunc ir_it_func)) (h1 : @Eq (IROption IRFunc) (ir_func_find fs ir_d1) (@IROption.some IRFunc g1)) (h2 : @Eq (IROption IRFunc) (ir_func_find fs ir_d2) (@IROption.some IRFunc g2)) (hq1 : forall (mem1 : IRList IRMemSlot) (na1 : Nat) (vs : IRList IRScalar), QH p (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na) mem1 na1 vs -> forall (C : Prop), (forall (sp : IRScalar), @Eq (IRList IRScalar) vs (ir_vl1 (ir_it_hb_answer sp)) -> C) -> C) (hq2 : forall (mem1 : IRList IRMemSlot) (na1 : Nat) (vs1 : IRList IRScalar) (mem2 : IRList IRMemSlot) (na2 : Nat) (vs : IRList IRScalar), QH p (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na) mem1 na1 vs1 -> QF p q mem1 na1 mem2 na2 vs -> forall (C : Prop), (forall (spv : IRScalar) (v0 : IRScalar), @Eq (IRList IRScalar) vs (ir_vl1 (IRScalar.aggv spv)) -> @Eq (IROption IRMemSlot) (ir_mem_lookup mem2 na) (@IROption.some IRMemSlot (IRMemSlot.mk na v0 Bool.true)) -> C) -> C) (ihh : ir_ctr_at (IRModule.mk fs gs) (ir_it_hb_entry g1 p (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na)) (QH p (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na)) n) (ihf : forall (mem1 : IRList IRMemSlot) (na1 : Nat) (vs1 : IRList IRScalar), QH p (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na) mem1 na1 vs1 -> ir_ctr_at (IRModule.mk fs gs) (ir_it_fast_entry g2 p q mem1 na1) (QF p q mem1 na1) n) : ir_ctr_at (IRModule.mk fs gs) (ir_it_ag_entry p q mem na) (ir_it_tpost QH QF p q mem na) (Nat.succ n) := fun (G : IROutcome -> Prop) (ds : IRList Nat) (rest : IRList IRFrame) (hK : forall (mem3 : IRList IRMemSlot) (na3 : Nat) (vs : IRList IRScalar), ir_it_tpost QH QF p q mem na mem3 na3 vs -> ir_safe G (IRModule.mk fs gs) (Nat.succ n) (ir_ret_to ds rest mem3 na3 vs)) => (Eq.subst IRConfig (fun (c : IRConfig) => ir_safe G (IRModule.mk fs gs) n c) (IRConfig.running (ir_it_ag_alloca_m p q mem na ds rest)) (ir_step (IRModule.mk fs gs) (ir_it_ag_entry p q mem na ds rest)) (Eq.symm IRConfig (ir_step (IRModule.mk fs gs) (ir_it_ag_entry p q mem na ds rest)) (IRConfig.running (ir_it_ag_alloca_m p q mem na ds rest)) (ir_it_ag_step_alloca fs gs p q mem na ds rest h0)) (ir_safe_pad G (IRModule.mk fs gs) n ir_d1 (IRConfig.running (ir_it_ag_alloca_m p q mem na ds rest)) (Eq.subst IRConfig (fun (c : IRConfig) => ir_safe G (IRModule.mk fs gs) n c) (IRConfig.running (ir_it_ag_push1_m g1 p q mem na ds rest)) (ir_steps ir_d1 (IRModule.mk fs gs) (IRConfig.running (ir_it_ag_alloca_m p q mem na ds rest))) (Eq.symm IRConfig (ir_steps ir_d1 (IRModule.mk fs gs) (IRConfig.running (ir_it_ag_alloca_m p q mem na ds rest))) (IRConfig.running (ir_it_ag_push1_m g1 p q mem na ds rest)) (ir_it_ag_step_call fs gs g1 p q mem na ds rest h0 h1)) (ihh G (ir_nl1 ir_d3) (@IRList.cons IRFrame (ir_it_dframe (@IRList.cons IRBinding (IRBinding.mk ir_d2 (IRScalar.ptr_ na)) (@IRList.cons IRBinding (IRBinding.mk ir_d0 (IRScalar.ptr_ p)) (@IRList.cons IRBinding (IRBinding.mk ir_d1 (IRScalar.ptr_ q)) (@IRList.nil IRBinding)))) ds) rest) (fun (mem1 : IRList IRMemSlot) (na1 : Nat) (vs1 : IRList IRScalar) (hqh : QH p (@IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem) (Nat.succ na) mem1 na1 vs1) => hq1 mem1 na1 vs1 hqh (ir_safe G (IRModule.mk fs gs) n (ir_ret_to (ir_nl1 ir_d3) (@IRList.cons IRFrame (ir_it_dframe (@IRList.cons IRBinding (IRBinding.mk ir_d2 (IRScalar.ptr_ na)) (@IRList.cons IRBinding (IRBinding.mk ir_d0 (IRScalar.ptr_ p)) (@IRList.cons IRBinding (IRBinding.mk ir_d1 (IRScalar.ptr_ q)) (@IRList.nil IRBinding)))) ds) rest) mem1 na1 vs1)) (fun (sp : IRScalar) (hv : @Eq (IRList IRScalar) vs1 (ir_vl1 (ir_it_hb_answer sp))) => Eq.subst (IRList IRScalar) (fun (v : IRList IRScalar) => ir_safe G (IRModule.mk fs gs) n (ir_ret_to (ir_nl1 ir_d3) (@IRList.cons IRFrame (ir_it_dframe (@IRList.cons IRBinding (IRBinding.mk ir_d2 (IRScalar.ptr_ na)) (@IRList.cons IRBinding (IRBinding.mk ir_d0 (IRScalar.ptr_ p)) (@IRList.cons IRBinding (IRBinding.mk ir_d1 (IRScalar.ptr_ q)) (@IRList.nil IRBinding)))) ds) rest) mem1 na1 v)) (ir_vl1 (ir_it_hb_answer sp)) vs1 (Eq.symm (IRList IRScalar) vs1 (ir_vl1 (ir_it_hb_answer sp)) hv) (ir_it_top_sseg_r1 fs gs g2 QH QF p q mem na n h0 h2 hq2 ihf G ds rest hK mem1 na1 vs1 hqh sp)))))))";
// ──────────────────────────────────────────────────────────────────────────

// ── the device at the real body: what it refuses ──────────────────────────
const SRC_UNREACHABLE_REFUTES: &str = "def ir_it_unreachable_refutes (mem : IRList IRMemSlot) (na : Nat) (loc : IRList IRBinding) (Q : IRList IRMemSlot -> Nat -> IRList IRScalar -> Prop) (hc : ir_ctr_at ir_it_module (fun (d : IRList Nat) (r : IRList IRFrame) => IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d2 Nat.zero loc d) r) mem na) Q ir_d1) (C : Prop) : C := ir_ctr_refutes_bad ir_it_module (fun (d : IRList Nat) (r : IRList IRFrame) => IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d2 Nat.zero loc d) r) mem na) Q ir_d1 (@IRList.nil Nat) (IROutcome.ub IRFault.unreachable) (@Eq.refl IRConfig (IRConfig.halted (IROutcome.ub IRFault.unreachable))) (@Eq.refl Bool Bool.true) hc C";

const SRC_ERR_ARM_REFUTES: &str = "def ir_it_err_arm_refutes (mem : IRList IRMemSlot) (na : Nat) (loc : IRList IRBinding) (e1 : IRScalar) (e2 : IRScalar) (Q : IRList IRMemSlot -> Nat -> IRList IRScalar -> Prop) (hc : ir_ctr_at ir_it_module (fun (d : IRList Nat) (r : IRList IRFrame) => IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 ir_d2 (@IRList.cons IRBinding (IRBinding.mk ir_d3 (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons e1 (IRScalar.vcons e2 IRScalar.vnil))))) loc) d) r) mem na) Q ir_d9) (C : Prop) : C := ir_ctr_refutes_bad ir_it_module (fun (d : IRList Nat) (r : IRList IRFrame) => IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 ir_d2 (@IRList.cons IRBinding (IRBinding.mk ir_d3 (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons e1 (IRScalar.vcons e2 IRScalar.vnil))))) loc) d) r) mem na) Q ir_d9 (@IRList.nil Nat) (IROutcome.type_error IRFault.not_agg) (@Eq.refl IRConfig (IRConfig.halted (IROutcome.type_error IRFault.not_agg))) (@Eq.refl Bool Bool.true) hc C";

// ── the acceptance predicate: ret with the post, fuel_out, or a sanctioned panic
const SRC_PC_OK: &str = "def ir_it_pc_ok (Q : IRList IRMemSlot -> Nat -> IRList IRScalar -> Prop) (o : IROutcome) : Prop := ir_run_ok (ir_ret_post Q) o";

const SRC_PC_OK_FUEL_OUT: &str = "def ir_it_pc_ok_fuel_out (Q : IRList IRMemSlot -> Nat -> IRList IRScalar -> Prop) : ir_it_pc_ok Q IROutcome.fuel_out := @Eq.refl Bool Bool.true";

const SRC_PC_OK_PANIC: &str = "def ir_it_pc_ok_panic (Q : IRList IRMemSlot -> Nat -> IRList IRScalar -> Prop) : ir_it_pc_ok Q (IROutcome.ub IRFault.assert_failed) := @Eq.refl Bool Bool.true";

const SRC_PC_OK_RET: &str = "def ir_it_pc_ok_ret (Q : IRList IRMemSlot -> Nat -> IRList IRScalar -> Prop) (mem2 : IRList IRMemSlot) (na2 : Nat) (vs : IRList IRScalar) (h : Q mem2 na2 vs) : ir_it_pc_ok Q (IROutcome.ret vs) := fun (C : Prop) (k : forall (m3 : IRList IRMemSlot) (n3 : Nat), Q m3 n3 vs -> C) => k mem2 na2 h";

const SRC_PC_OK_BAD: &str = "def ir_it_pc_ok_bad (Q : IRList IRMemSlot -> Nat -> IRList IRScalar -> Prop) (o : IROutcome) (hbad : @Eq Bool (ir_bad_halt o) Bool.true) (h : ir_it_pc_ok Q o) (C : Prop) : C := @IROutcome.rec (fun (o0 : IROutcome) => @Eq Bool (ir_bad_halt o0) Bool.true -> ir_it_pc_ok Q o0 -> C) (fun (vs : IRList IRScalar) (hb : @Eq Bool (ir_bad_halt (IROutcome.ret vs)) Bool.true) (_ : ir_it_pc_ok Q (IROutcome.ret vs)) => ir_bool_false_ne_true C hb) (fun (f : IRFault) (hb : @Eq Bool (ir_bad_halt (IROutcome.ub f)) Bool.true) (hk : ir_it_pc_ok Q (IROutcome.ub f)) => @Bool.rec (fun (b : Bool) => @Eq Bool (@Bool.rec (fun (_ : Bool) => Bool) Bool.true Bool.false b) Bool.true -> ir_bprop (forall (C2 : Prop), C2) (@Eq Bool Bool.true Bool.true) b -> C) (fun (_ : @Eq Bool Bool.true Bool.true) (he : forall (C2 : Prop), C2) => he C) (fun (hb2 : @Eq Bool Bool.false Bool.true) (_ : @Eq Bool Bool.true Bool.true) => ir_bool_false_ne_true C hb2) (ir_fault_is_assert f) hb hk) (fun (f : IRFault) (_ : @Eq Bool (ir_bad_halt (IROutcome.type_error f)) Bool.true) (he : ir_it_pc_ok Q (IROutcome.type_error f)) => he C) (fun (f : IRFault) (_ : @Eq Bool (ir_bad_halt (IROutcome.unmodelled f)) Bool.true) (he : ir_it_pc_ok Q (IROutcome.unmodelled f)) => he C) (fun (f : IRFault) (_ : @Eq Bool (ir_bad_halt (IROutcome.stuck f)) Bool.true) (he : ir_it_pc_ok Q (IROutcome.stuck f)) => he C) (fun (hb : @Eq Bool (ir_bad_halt IROutcome.fuel_out) Bool.true) (_ : ir_it_pc_ok Q IROutcome.fuel_out) => ir_bool_false_ne_true C hb) o hbad h";

const SRC_PC_OK_IS_RET: &str = "def ir_it_pc_ok_is_ret (Q : IRList IRMemSlot -> Nat -> IRList IRScalar -> Prop) (o : IROutcome) (hok : ir_it_pc_ok Q o) (hr : @Eq Bool (ir_outcome_is_ret o) Bool.true) : forall (C : Prop), (forall (vs : IRList IRScalar) (mem2 : IRList IRMemSlot) (na2 : Nat), @Eq IROutcome o (IROutcome.ret vs) -> Q mem2 na2 vs -> C) -> C := @IROutcome.rec (fun (o0 : IROutcome) => ir_it_pc_ok Q o0 -> @Eq Bool (ir_outcome_is_ret o0) Bool.true -> forall (C : Prop), (forall (vs : IRList IRScalar) (mem2 : IRList IRMemSlot) (na2 : Nat), @Eq IROutcome o0 (IROutcome.ret vs) -> Q mem2 na2 vs -> C) -> C) (fun (vs : IRList IRScalar) (h : ir_it_pc_ok Q (IROutcome.ret vs)) (_ : @Eq Bool (ir_outcome_is_ret (IROutcome.ret vs)) Bool.true) (C : Prop) (k : forall (vs0 : IRList IRScalar) (mem2 : IRList IRMemSlot) (na2 : Nat), @Eq IROutcome (IROutcome.ret vs) (IROutcome.ret vs0) -> Q mem2 na2 vs0 -> C) => h C (fun (mem2 : IRList IRMemSlot) (na2 : Nat) (hq : Q mem2 na2 vs) => k vs mem2 na2 (@Eq.refl IROutcome (IROutcome.ret vs)) hq)) (fun (f : IRFault) (_ : ir_it_pc_ok Q (IROutcome.ub f)) (hb : @Eq Bool (ir_outcome_is_ret (IROutcome.ub f)) Bool.true) (C : Prop) (_ : forall (vs0 : IRList IRScalar) (mem2 : IRList IRMemSlot) (na2 : Nat), @Eq IROutcome (IROutcome.ub f) (IROutcome.ret vs0) -> Q mem2 na2 vs0 -> C) => ir_bool_false_ne_true C hb) (fun (f : IRFault) (_ : ir_it_pc_ok Q (IROutcome.type_error f)) (hb : @Eq Bool (ir_outcome_is_ret (IROutcome.type_error f)) Bool.true) (C : Prop) (_ : forall (vs0 : IRList IRScalar) (mem2 : IRList IRMemSlot) (na2 : Nat), @Eq IROutcome (IROutcome.type_error f) (IROutcome.ret vs0) -> Q mem2 na2 vs0 -> C) => ir_bool_false_ne_true C hb) (fun (f : IRFault) (_ : ir_it_pc_ok Q (IROutcome.unmodelled f)) (hb : @Eq Bool (ir_outcome_is_ret (IROutcome.unmodelled f)) Bool.true) (C : Prop) (_ : forall (vs0 : IRList IRScalar) (mem2 : IRList IRMemSlot) (na2 : Nat), @Eq IROutcome (IROutcome.unmodelled f) (IROutcome.ret vs0) -> Q mem2 na2 vs0 -> C) => ir_bool_false_ne_true C hb) (fun (f : IRFault) (_ : ir_it_pc_ok Q (IROutcome.stuck f)) (hb : @Eq Bool (ir_outcome_is_ret (IROutcome.stuck f)) Bool.true) (C : Prop) (_ : forall (vs0 : IRList IRScalar) (mem2 : IRList IRMemSlot) (na2 : Nat), @Eq IROutcome (IROutcome.stuck f) (IROutcome.ret vs0) -> Q mem2 na2 vs0 -> C) => ir_bool_false_ne_true C hb) (fun (_ : ir_it_pc_ok Q IROutcome.fuel_out) (hb : @Eq Bool (ir_outcome_is_ret IROutcome.fuel_out) Bool.true) (C : Prop) (_ : forall (vs0 : IRList IRScalar) (mem2 : IRList IRMemSlot) (na2 : Nat), @Eq IROutcome IROutcome.fuel_out (IROutcome.ret vs0) -> Q mem2 na2 vs0 -> C) => ir_bool_false_ne_true C hb) o hok hr";

/// The names this stage registers, in registration order.
pub const IT_SCTR_NAMES: &[&str] = &[
    "ir_it_hb_entry",
    "ir_it_fast_entry",
    "ir_it_tpost",
    "ir_it_top_sseg_r2",
    "ir_it_top_sseg_r1",
    "ir_it_top_sseg",
    "ir_it_unreachable_refutes",
    "ir_it_err_arm_refutes",
    "ir_it_pc_ok",
    "ir_it_pc_ok_fuel_out",
    "ir_it_pc_ok_panic",
    "ir_it_pc_ok_ret",
    "ir_it_pc_ok_bad",
    "ir_it_pc_ok_is_ret",
];

/// `(source, description)`, positionally paired with [`IT_SCTR_NAMES`].
const DECLS: &[(&str, &str)] = &[
    (
        SRC_HB_ENTRY,
        "ir_it_hb_entry: tick_heartbeat's ENTRY machine at an abstract module -- g1's frame at pc 0 over its own entry block, its parameters bound to the one argument ptr_ p, returning to dests d over caller stack r, heap mem, counter na. VERBATIM the callee frame of ir_it_ag_push1_m and the premise configuration of ir_it_ag_activation's hc1, curried over the caller so it is an ir_ctr_at entry. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_FAST_ENTRY,
        "ir_it_fast_entry: infer_type_fast's ENTRY machine at an abstract module -- g2's frame at pc 0, its parameters bound to (ptr_ p, ptr_ q). VERBATIM the callee frame of ir_it_ag_push2_m and hc2's premise configuration, curried over the caller. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_TPOST,
        "ir_it_tpost: infer_type's POST, relative to its callees' posts -- the TRANSPORT property as a relation. The values the call returns (at counter na3) are values infer_type_fast returned under QF, entered at a heap the heartbeat left under QH, which was itself entered with the Result slot allocated at na. It does NOT constrain the returned heap: the structural A4 (ir_it_ag_correct) is an outcome-level statement and does not either. A Church-encoded existential, so the stage names no Exists. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_IR_IT_TOP_SSEG_R2,
        "ir_it_top_sseg_r2: resume segment 2 of ir_it_top_sseg -- the configuration infer_type resumes at after infer_type_fast returned an aggregate (hq2's case analysis: the value, the slot's contents): the store, br, load (the transport seam) and ret, where hK takes the transport post. One lemma per call (D5's re-decided remedy; designs/2026-09-24-e2-contract-soundness.md section 9): MINTED by scripts/gen_it_sctr.py. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_IR_IT_TOP_SSEG_R1,
        "ir_it_top_sseg_r1: resume segment 1 of ir_it_top_sseg -- the configuration infer_type resumes at after tick_heartbeat returned an OK answer (hq1's case analysis): br, extractfield, switch (the dispatch seam) and the call to infer_type_fast through its contract ihf at n; its continuation applies ir_it_top_sseg_r2. One lemma per call (D5's re-decided remedy; designs/2026-09-24-e2-contract-soundness.md section 9): MINTED by scripts/gen_it_sctr.py. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_IR_IT_TOP_SSEG,
        "ir_it_top_sseg: *** infer_type's LOCAL OBLIGATION, STEP-INDEXED. *** From tick_heartbeat's contract at budget n (ihh) and infer_type_fast's contract at n for every return the heartbeat's post admits (ihf), with the two post premises (hq1: the heartbeat answers OK; hq2: the inference returns an aggregate and the Result slot is still live), the body entered at an abstract module meets its contract at succ n with post ir_it_tpost. The budget pays for the alloca (ir_it_ag_step_alloca under h0); the heartbeat call's push, the dispatch seam, the inference call's push, the store/br/load transport seam and the ret are padded (ir_safe_pad) through the SAME step lemmas ir_it_ag_activation splices; both calls consume their contract at exactly n. MINTED by scripts/gen_it_sctr.py ONE LEMMA PER CALL: this proof walks the body through the heartbeat call and applies ir_it_top_sseg_r1; the statement is the nested form's, byte for byte. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_UNREACHABLE_REFUTES,
        "ir_it_unreachable_refutes: *** THE DEVICE REFUSES infer_type's SWITCH DEFAULT, AT THE MINTED MODULE. *** A machine standing at block 2 of ir_it_func -- the `unreachable` that b1's switch defaults to -- meets NO contract at budget one, whatever its locals, heap, counter or post: one step halts ub unreachable, which ir_sanctioned refuses (ir_ctr_refutes_bad). A contract that holds for the body is therefore itself the proof that its run never reaches that arm. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_ERR_ARM_REFUTES,
        "ir_it_err_arm_refutes: *** AND REFUSES THE ERR ARM, WHICH IS WHY THE OK-ANSWER PREMISE hq1 IS FORCED. *** A machine resumed after `call 1` (block 0, pc 2) holding an ERR heartbeat answer (tag 1) meets NO contract at budget nine, whatever its payload, locals, heap or post: br, the tag read and the switch send it to b4, whose sixth node inserts a field into a bare `undef` and halts type_error not_agg -- the producer's aggregate-construction idiom that ir_undef_then_insertfield_faults pins as unexecutable. So on today's machine infer_type meets no safety contract whose heartbeat post admits an Err answer; the E3 undef change is what would lift that, and until it lands the Err arm is out of this instance's scope by premise, not by omission. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_PC_OK,
        "ir_it_pc_ok: *** THE ACCEPTANCE PREDICATE, AT A POST. *** An outcome is acceptable when it is fuel_out (the run has not finished), a sanctioned panic (ub assert_failed), or ret vs with some final heap and counter satisfying Q -- ir_run_ok at the device's own acceptor ir_ret_post. Every other outcome is refused (ir_it_pc_ok_bad). DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_PC_OK_FUEL_OUT,
        "ir_it_pc_ok_fuel_out: vacuity pin -- fuel exhaustion is acceptable. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_PC_OK_PANIC,
        "ir_it_pc_ok_panic: vacuity pin -- a sanctioned panic is acceptable. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_PC_OK_RET,
        "ir_it_pc_ok_ret: vacuity pin -- a return whose values some heap and counter satisfy the post for is acceptable. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_PC_OK_BAD,
        "ir_it_pc_ok_bad: *** THE PREDICATE IS NOT VACUOUS. *** A BAD outcome -- ub other than assert_failed (unreachable included), and every type_error, unmodelled and stuck outcome -- is acceptable at NO post: it implies anything. IROutcome.rec with a Bool.rec convoy on ir_fault_is_assert in the ub arm. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_PC_OK_IS_RET,
        "ir_it_pc_ok_is_ret: an acceptable outcome that IS a return is a return whose values satisfy the post (at some heap and counter) -- every non-ret arm contradicts ir_outcome_is_ret. This is what lets the cross-check take ONLY termination from the structural chain. DerivedProved, zero axiom_deps.",
    ),
];

impl Specification {
    /// `infer_type`'s local obligation in step-indexed form. Full-only; MUST
    /// follow `add_eval_ir_itf` (the abstract-module step lemmas, the dispatch
    /// and transport seams) and `add_eval_ir_ctr` (the device), and
    /// `add_eval_ir_correct` (`ir_outcome_is_ret`).
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check -- by name.
    pub(super) fn add_eval_ir_it_sctr(&mut self) -> Result<(), SpecError> {
        for (source, description) in DECLS {
            self.add_recursive_def(source, description)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sources_balanced_ascii_and_named() {
        assert_eq!(DECLS.len(), IT_SCTR_NAMES.len());
        for ((src, _), name) in DECLS.iter().zip(IT_SCTR_NAMES) {
            assert!(src.is_ascii(), "spec sources stay ASCII");
            assert_eq!(src.matches('(').count(), src.matches(')').count(), "{name}");
            assert!(src.starts_with(&format!("def {name} ")), "{name}");
        }
    }

    /// The minted obligation consumes both callees through CONTRACTS at `n`,
    /// never an exact run, and concludes the body's contract at `succ n`.
    #[test]
    fn test_minted_obligation_goes_through_contracts() {
        let src = SRC_IR_IT_TOP_SSEG;
        assert!(src.contains("(ihh : ir_ctr_at (IRModule.mk fs gs) (ir_it_hb_entry g1 p"));
        assert!(src.contains("-> ir_ctr_at (IRModule.mk fs gs) (ir_it_fast_entry g2 p q mem1 na1)"));
        assert!(src.contains("ir_safe_pad"));
        assert!(!src.contains("hc1") && !src.contains("hc2"));
        assert!(src.contains(
            ": ir_ctr_at (IRModule.mk fs gs) (ir_it_ag_entry p q mem na) (ir_it_tpost QH QF p q mem na) (Nat.succ n) := fun (G : IROutcome -> Prop)"
        ));
    }

    /// ONE LEMMA PER CALL: the obligation discharges the heartbeat call and
    /// applies `_r1`; `_r1` discharges the inference call and applies `_r2`;
    /// `_r2` is the transport tail to the `ret`, which hands hK the post.
    #[test]
    fn test_obligation_is_minted_one_lemma_per_call() {
        let top = SRC_IR_IT_TOP_SSEG;
        let (r1, r2) = (SRC_IR_IT_TOP_SSEG_R1, SRC_IR_IT_TOP_SSEG_R2);
        assert_eq!(top.matches("(ihh G ").count(), 1);
        assert_eq!(top.matches("(ihf mem1 ").count(), 0);
        assert!(top.contains("(ir_it_top_sseg_r1 "));
        assert!(r1.starts_with("def ir_it_top_sseg_r1 "));
        assert_eq!(r1.matches("(ihh G ").count(), 0);
        assert_eq!(r1.matches("(ihf mem1 ").count(), 1);
        assert!(r1.contains("(ir_it_top_sseg_r2 "));
        assert!(r2.starts_with("def ir_it_top_sseg_r2 "));
        assert_eq!(
            r2.matches("(ihh G ").count() + r2.matches("(ihf mem1 ").count(),
            0
        );
        assert!(r2.contains("(hK "));
        for seg in [r1, r2] {
            assert!(seg.contains(": ir_safe G (IRModule.mk fs gs) n (ir_ret_to "));
            assert!(!seg.contains("hc1") && !seg.contains("hc2"));
        }
    }
}
