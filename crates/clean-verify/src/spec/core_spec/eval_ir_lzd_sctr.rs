// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//! **`Level::is_zero`'s local obligations in STEP-INDEXED form** -- the first
//! instance of the E2 contract device (`eval_ir_ctr.rs`;
//! `designs/2026-09-24-e2-contract-soundness.md`).
//!
//! The exact A4 (`ir_lzd_correct`) splices three segment lemmas whose recursive
//! calls are EXACT runs of an exact cost. Here the same three bodies, over the
//! same `ir_lzd_module` and the same heap/counter/`MemExt` state, meet the
//! body's CONTRACT at `Nat.succ n` from:
//!
//! * the deref chain's contract `ir_lzd_deref_ctr` -- `ir_lzd_deref_activation`
//!   (forty exact steps through four of the compiler's bodies) through the
//!   adapter `ir_ctr_exact`;
//! * the recursion group's own contract at the strictly smaller budget `n`
//!   (`ih1` / `ih2`), whose post `ir_lzd_zpost` says only that the heap grew
//!   and the answer is the given Bool.
//!
//! The leaves (Zero, Succ, Param) are exact runs, lifted by `ir_ctr_of_exact`.
//! Nothing here names `Level`: the Full-bundle assembly (`eval_ir_lzd_pc.rs`)
//! supplies the answers from `level_is_zero` and runs `ir_ctr_group_sound`.
//!
//! The three `*_sseg` terms are MINTED by `scripts/gen_lzd_sctr.py` from the
//! exact generator's own segment vocabulary; `--check` byte-compares them with
//! this file. Each is minted ONE LEMMA PER CALL (D5's re-decided remedy,
//! `designs/2026-09-24-e2-contract-soundness.md` section 9): `<obligation>_r<i>`
//! is the safety of the configuration the body resumes at after its `i`-th call,
//! and each lemma's proof walks one literal run and ONE call, whose continuation
//! applies the next. No term nests one call's continuation inside another's; the
//! obligations' statements are unchanged. The frame stack each call returns
//! into is NAMED (`<obligation>_st<i>`, one layer of history over the previous
//! stack's name) and the heap-extension witness is a binder the caller passes,
//! so no declaration's text grows with the calls before it -- spelled out, the
//! stacks kept the chain superlinear. Registered stacks, then segments, then
//! the obligation. Registered in both the Full stage list and the EvalIr bundle,
//! after `add_eval_ir_lzd_activation` and `add_eval_ir_ctr`.

use super::{SpecError, Specification};

const SRC_ZPOST: &str = "def ir_lzd_zpost (mem : IRList IRMemSlot) (na : Nat) (ans : Bool) (mem2 : IRList IRMemSlot) (na2 : Nat) (vs : IRList IRScalar) : Prop := forall (C : Prop), (MemExt mem na mem2 na2 -> Eq (IRList IRScalar) vs (ir_vl1 (IRScalar.bool_ ans)) -> C) -> C";
const SRC_ZPOST_INTRO: &str = "def ir_lzd_zpost_intro (mem : IRList IRMemSlot) (na : Nat) (ans : Bool) (mem2 : IRList IRMemSlot) (na2 : Nat) (e : MemExt mem na mem2 na2) : ir_lzd_zpost mem na ans mem2 na2 (ir_vl1 (IRScalar.bool_ ans)) := fun (C : Prop) (k : MemExt mem na mem2 na2 -> Eq (IRList IRScalar) (ir_vl1 (IRScalar.bool_ ans)) (ir_vl1 (IRScalar.bool_ ans)) -> C) => k e (Eq.refl (IRList IRScalar) (ir_vl1 (IRScalar.bool_ ans)))";
const SRC_DEREF_CTR: &str = "def ir_lzd_deref_ctr (mem : IRList IRMemSlot) (p : Nat) (b : Nat) (na : Nat) (hlt : Eq Bool (ir_nat_ltb p na) Bool.true) (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem p) (IROption.some IRMemSlot (IRMemSlot.mk p (IRScalar.ptr_ (Nat.succ b)) Bool.true))) (hcb : Eq IRStepResult (ir_borrow_eval (ir_cell na IRScalar.undef_ mem) (IRScalar.ptr_ (Nat.add (Nat.succ b) ir_d16))) (IRStepResult.value (IRScalar.ptr_ (Nat.add (Nat.succ b) ir_d16)))) (n : Nat) : ir_ctr_at ir_lzd_module (ir_lzd_dmach mem p na) (ir_post_exact (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) (ir_vl1 (IRScalar.ptr_ (Nat.add (Nat.succ b) ir_d16)))) n := ir_ctr_exact ir_lzd_module (ir_lzd_dmach mem p na) ir_d40 (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) (ir_vl1 (IRScalar.ptr_ (Nat.add (Nat.succ b) ir_d16))) (fun (d : IRList Nat) (r : IRList IRFrame) => ir_lzd_deref_activation mem p b na d r hlt h hcb) n";
const SRC_ZERO_CTR: &str = "def ir_lzd_zero_ctr (mem : IRList IRMemSlot) (a : Nat) (na : Nat) (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d0 ir_sp0) Bool.true))) (n : Nat) : ir_ctr_at ir_lzd_module (ir_lzd_mach0_s mem (IRScalar.ptr_ a) na) (ir_lzd_zpost mem na Bool.true) n := ir_ctr_of_exact ir_lzd_module (ir_lzd_mach0_s mem (IRScalar.ptr_ a) na) (ir_lzd_zpost mem na Bool.true) ir_d6 mem na (ir_vl1 (IRScalar.bool_ Bool.true)) (fun (d : IRList Nat) (r : IRList IRFrame) => ir_lzd_activation_zero mem a na d r h) (ir_lzd_zpost_intro mem na Bool.true mem na (MemExt.refl mem na)) n";
const SRC_SUCC_CTR: &str = "def ir_lzd_succ_ctr (mem : IRList IRMemSlot) (a : Nat) (na : Nat) (b : Nat) (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d1 (ir_sp1 (IRScalar.ptr_ (Nat.succ b)))) Bool.true))) (n : Nat) : ir_ctr_at ir_lzd_module (ir_lzd_mach0_s mem (IRScalar.ptr_ a) na) (ir_lzd_zpost mem na Bool.false) n := ir_ctr_of_exact ir_lzd_module (ir_lzd_mach0_s mem (IRScalar.ptr_ a) na) (ir_lzd_zpost mem na Bool.false) ir_d6 mem na (ir_vl1 (IRScalar.bool_ Bool.false)) (fun (d : IRList Nat) (r : IRList IRFrame) => ir_lzd_activation_succ mem a na d r b h) (ir_lzd_zpost_intro mem na Bool.false mem na (MemExt.refl mem na)) n";
const SRC_PARAM_CTR: &str = "def ir_lzd_param_ctr (mem : IRList IRMemSlot) (a : Nat) (na : Nat) (w : IRScalar) (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d4 (ir_sp1 w)) Bool.true))) (n : Nat) : ir_ctr_at ir_lzd_module (ir_lzd_mach0_s mem (IRScalar.ptr_ a) na) (ir_lzd_zpost mem na Bool.false) n := ir_ctr_of_exact ir_lzd_module (ir_lzd_mach0_s mem (IRScalar.ptr_ a) na) (ir_lzd_zpost mem na Bool.false) ir_d6 mem na (ir_vl1 (IRScalar.bool_ Bool.false)) (fun (d : IRList Nat) (r : IRList IRFrame) => ir_lzd_activation_param mem a na d r w h) (ir_lzd_zpost_intro mem na Bool.false mem na (MemExt.refl mem na)) n";
// ── minted by scripts/gen_lzd_sctr.py -- do not edit by hand ──────────────
const SRC_IR_LZD_IMAX_SSEG_ST1: &str = "def ir_lzd_imax_sseg_st1 (mem : (IRList IRMemSlot)) (a : Nat) (b1 : Nat) (b2 : Nat) (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame) : IRList IRFrame := ir_frames_tail (ir_config_frames (ir_steps ir_d5 ir_lzd_module (ir_lzd_after_load mem a na dests rest (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d3 (ir_sp2 (IRScalar.ptr_ (Nat.succ b1)) (IRScalar.ptr_ (Nat.succ b2)))) Bool.true)))))";
const SRC_IR_LZD_IMAX_SSEG_ST2: &str = "def ir_lzd_imax_sseg_st2 (mem : (IRList IRMemSlot)) (a : Nat) (b1 : Nat) (b2 : Nat) (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame) : IRList IRFrame := ir_frames_tail (ir_config_frames (ir_steps ir_d1 ir_lzd_module (ir_ret_to (ir_nl1 ir_d16) (ir_lzd_imax_sseg_st1 mem a b1 b2 na dests rest) (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) (ir_vl1 (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16))))))";
const SRC_IR_LZD_IMAX_SSEG_R2: &str = "def ir_lzd_imax_sseg_r2 (mem : (IRList IRMemSlot)) (a : Nat) (b1 : Nat) (b2 : Nat) (ans2 : Bool) (na : Nat) (n : Nat) (G : IROutcome -> Prop) (dests : IRList Nat) (rest : IRList IRFrame) (hK : forall (mem2 : (IRList IRMemSlot)) (na2 : Nat) (vs : IRList IRScalar), ir_lzd_zpost mem na ans2 mem2 na2 vs -> ir_safe G ir_lzd_module (Nat.succ n) (ir_ret_to dests rest mem2 na2 vs)) (mA : (IRList IRMemSlot)) (nA : Nat) (ex2 : MemExt mem na mA nA) : ir_safe G ir_lzd_module n (ir_ret_to (ir_nl1 ir_d17) (ir_lzd_imax_sseg_st2 mem a b1 b2 na dests rest) mA nA (ir_vl1 (IRScalar.bool_ ans2))) := (ir_safe_pad G ir_lzd_module n ir_d2 (ir_ret_to (ir_nl1 ir_d17) (ir_lzd_imax_sseg_st2 mem a b1 b2 na dests rest) mA nA (ir_vl1 (IRScalar.bool_ ans2))) (ir_safe_down G ir_lzd_module n (ir_ret_to dests rest mA nA (ir_vl1 (IRScalar.bool_ ans2))) (hK mA nA (ir_vl1 (IRScalar.bool_ ans2)) (ir_lzd_zpost_intro mem na ans2 mA nA ex2))))";
const SRC_IR_LZD_IMAX_SSEG_R1: &str = "def ir_lzd_imax_sseg_r1 (mem : (IRList IRMemSlot)) (a : Nat) (b1 : Nat) (b2 : Nat) (ans2 : Bool) (na : Nat) (n : Nat) (ih2 : ir_ctr_at ir_lzd_module (ir_lzd_mach0_s (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) IRScalar.vnil))) mem) (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) (Nat.succ na)) (ir_lzd_zpost (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) ans2) n) (G : IROutcome -> Prop) (dests : IRList Nat) (rest : IRList IRFrame) (hK : forall (mem2 : (IRList IRMemSlot)) (na2 : Nat) (vs : IRList IRScalar), ir_lzd_zpost mem na ans2 mem2 na2 vs -> ir_safe G ir_lzd_module (Nat.succ n) (ir_ret_to dests rest mem2 na2 vs)) (ex1 : MemExt mem na (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na)) : ir_safe G ir_lzd_module n (ir_ret_to (ir_nl1 ir_d16) (ir_lzd_imax_sseg_st1 mem a b1 b2 na dests rest) (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) (ir_vl1 (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)))) := (ir_safe_pad G ir_lzd_module n ir_d1 (ir_ret_to (ir_nl1 ir_d16) (ir_lzd_imax_sseg_st1 mem a b1 b2 na dests rest) (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) (ir_vl1 (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)))) (ih2 G (ir_nl1 ir_d17) (ir_lzd_imax_sseg_st2 mem a b1 b2 na dests rest) (fun (mA : (IRList IRMemSlot)) (nA : Nat) (vsA : IRList IRScalar) (hqA : ir_lzd_zpost (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) ans2 mA nA vsA) => hqA (ir_safe G ir_lzd_module n (ir_ret_to (ir_nl1 ir_d17) (ir_lzd_imax_sseg_st2 mem a b1 b2 na dests rest) mA nA vsA)) (fun (eA : MemExt (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) mA nA) (hvA : Eq (IRList IRScalar) vsA (ir_vl1 (IRScalar.bool_ ans2))) => Eq.subst (IRList IRScalar) (fun (v : IRList IRScalar) => ir_safe G ir_lzd_module n (ir_ret_to (ir_nl1 ir_d17) (ir_lzd_imax_sseg_st2 mem a b1 b2 na dests rest) mA nA v)) (ir_vl1 (IRScalar.bool_ ans2)) vsA (Eq.symm (IRList IRScalar) vsA (ir_vl1 (IRScalar.bool_ ans2)) hvA) (ir_lzd_imax_sseg_r2 mem a b1 b2 ans2 na n G dests rest hK mA nA (ir_mem_ext_trans mem na (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) ex1 mA nA eA))))))";
const SRC_IR_LZD_IMAX_SSEG: &str = "def ir_lzd_imax_sseg (mem : (IRList IRMemSlot)) (a : Nat) (b1 : Nat) (b2 : Nat) (ans2 : Bool) (na : Nat) (n : Nat) (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d3 (ir_sp2 (IRScalar.ptr_ (Nat.succ b1)) (IRScalar.ptr_ (Nat.succ b2)))) Bool.true))) (h16 : Eq (IROption IRMemSlot) (ir_mem_lookup mem (Nat.add a ir_d16)) (IROption.some IRMemSlot (IRMemSlot.mk (Nat.add a ir_d16) (IRScalar.ptr_ (Nat.succ b2)) Bool.true))) (hlt16 : Eq Bool (ir_nat_ltb (Nat.add a ir_d16) na) Bool.true) (hcb2 : forall (mx : IRList IRMemSlot) (nx : Nat), MemExt mem na mx nx -> Eq IRStepResult (ir_borrow_eval mx (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16))) (IRStepResult.value (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)))) (ih2 : ir_ctr_at ir_lzd_module (ir_lzd_mach0_s (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) IRScalar.vnil))) mem) (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) (Nat.succ na)) (ir_lzd_zpost (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) ans2) n) : ir_ctr_at ir_lzd_module (ir_lzd_mach0_s mem (IRScalar.ptr_ a) na) (ir_lzd_zpost mem na ans2) (Nat.succ n) := fun (G : IROutcome -> Prop) (dests : IRList Nat) (rest : IRList IRFrame) (hK : forall (mem2 : (IRList IRMemSlot)) (na2 : Nat) (vs : IRList IRScalar), ir_lzd_zpost mem na ans2 mem2 na2 vs -> ir_safe G ir_lzd_module (Nat.succ n) (ir_ret_to dests rest mem2 na2 vs)) => Eq.subst (IROption IRMemSlot) (fun (o : (IROption IRMemSlot)) => ir_safe G ir_lzd_module n (ir_lzd_after_load mem a na dests rest o)) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d3 (ir_sp2 (IRScalar.ptr_ (Nat.succ b1)) (IRScalar.ptr_ (Nat.succ b2)))) Bool.true)) (ir_mem_lookup mem a) (Eq.symm (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d3 (ir_sp2 (IRScalar.ptr_ (Nat.succ b1)) (IRScalar.ptr_ (Nat.succ b2)))) Bool.true)) h) (ir_safe_pad G ir_lzd_module n ir_d5 (ir_lzd_after_load mem a na dests rest (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d3 (ir_sp2 (IRScalar.ptr_ (Nat.succ b1)) (IRScalar.ptr_ (Nat.succ b2)))) Bool.true))) (ir_lzd_deref_ctr mem (Nat.add a ir_d16) b2 na (ir_lzd_ltb_ext mem na mem na (MemExt.refl mem na) (Nat.add a ir_d16) hlt16) (Eq.trans (IROption IRMemSlot) (ir_mem_lookup mem (Nat.add a ir_d16)) (ir_mem_lookup mem (Nat.add a ir_d16)) (IROption.some IRMemSlot (IRMemSlot.mk (Nat.add a ir_d16) (IRScalar.ptr_ (Nat.succ b2)) Bool.true)) (ir_lzd_lookup_ext mem na mem na (MemExt.refl mem na) (Nat.add a ir_d16) hlt16) h16) (hcb2 (ir_cell na IRScalar.undef_ mem) (Nat.succ na) (ir_mem_ext_trans mem na mem na (MemExt.refl mem na) (ir_cell na IRScalar.undef_ mem) (Nat.succ na) (ir_mem_ext_one mem na IRScalar.undef_))) n G (ir_nl1 ir_d16) (ir_lzd_imax_sseg_st1 mem a b1 b2 na dests rest) (fun (m2 : (IRList IRMemSlot)) (n2 : Nat) (v2 : IRList IRScalar) (hq2 : ir_post_exact (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) (ir_vl1 (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16))) m2 n2 v2) => hq2 (fun (m2 : (IRList IRMemSlot)) (n2 : Nat) (v2 : IRList IRScalar) => ir_safe G ir_lzd_module n (ir_ret_to (ir_nl1 ir_d16) (ir_lzd_imax_sseg_st1 mem a b1 b2 na dests rest) m2 n2 v2)) (ir_lzd_imax_sseg_r1 mem a b1 b2 ans2 na n ih2 G dests rest hK (ir_mem_ext_trans mem na mem na (MemExt.refl mem na) (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) (ir_mem_ext_one mem na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) IRScalar.vnil)))))))))";
const SRC_IR_LZD_MAX_FALSE_SSEG_ST1: &str = "def ir_lzd_max_false_sseg_st1 (mem : (IRList IRMemSlot)) (a : Nat) (b1 : Nat) (b2 : Nat) (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame) : IRList IRFrame := ir_frames_tail (ir_config_frames (ir_steps ir_d7 ir_lzd_module (ir_lzd_after_load mem a na dests rest (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ (Nat.succ b1)) (IRScalar.ptr_ (Nat.succ b2)))) Bool.true)))))";
const SRC_IR_LZD_MAX_FALSE_SSEG_ST2: &str = "def ir_lzd_max_false_sseg_st2 (mem : (IRList IRMemSlot)) (a : Nat) (b1 : Nat) (b2 : Nat) (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame) : IRList IRFrame := ir_frames_tail (ir_config_frames (ir_steps ir_d1 ir_lzd_module (ir_ret_to (ir_nl1 ir_d12) (ir_lzd_max_false_sseg_st1 mem a b1 b2 na dests rest) (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) (ir_vl1 (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16))))))";
const SRC_IR_LZD_MAX_FALSE_SSEG_R2: &str = "def ir_lzd_max_false_sseg_r2 (mem : (IRList IRMemSlot)) (a : Nat) (b1 : Nat) (b2 : Nat) (na : Nat) (n : Nat) (G : IROutcome -> Prop) (dests : IRList Nat) (rest : IRList IRFrame) (hK : forall (mem2 : (IRList IRMemSlot)) (na2 : Nat) (vs : IRList IRScalar), ir_lzd_zpost mem na Bool.false mem2 na2 vs -> ir_safe G ir_lzd_module (Nat.succ n) (ir_ret_to dests rest mem2 na2 vs)) (mA : (IRList IRMemSlot)) (nA : Nat) (ex2 : MemExt mem na mA nA) : ir_safe G ir_lzd_module n (ir_ret_to (ir_nl1 ir_d13) (ir_lzd_max_false_sseg_st2 mem a b1 b2 na dests rest) mA nA (ir_vl1 (IRScalar.bool_ Bool.false))) := (ir_safe_pad G ir_lzd_module n ir_d5 (ir_ret_to (ir_nl1 ir_d13) (ir_lzd_max_false_sseg_st2 mem a b1 b2 na dests rest) mA nA (ir_vl1 (IRScalar.bool_ Bool.false))) (ir_safe_down G ir_lzd_module n (ir_ret_to dests rest mA nA (ir_vl1 (IRScalar.bool_ Bool.false))) (hK mA nA (ir_vl1 (IRScalar.bool_ Bool.false)) (ir_lzd_zpost_intro mem na Bool.false mA nA ex2))))";
const SRC_IR_LZD_MAX_FALSE_SSEG_R1: &str = "def ir_lzd_max_false_sseg_r1 (mem : (IRList IRMemSlot)) (a : Nat) (b1 : Nat) (b2 : Nat) (na : Nat) (n : Nat) (ih1 : ir_ctr_at ir_lzd_module (ir_lzd_mach0_s (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) (Nat.succ na)) (ir_lzd_zpost (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) Bool.false) n) (G : IROutcome -> Prop) (dests : IRList Nat) (rest : IRList IRFrame) (hK : forall (mem2 : (IRList IRMemSlot)) (na2 : Nat) (vs : IRList IRScalar), ir_lzd_zpost mem na Bool.false mem2 na2 vs -> ir_safe G ir_lzd_module (Nat.succ n) (ir_ret_to dests rest mem2 na2 vs)) (ex1 : MemExt mem na (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na)) : ir_safe G ir_lzd_module n (ir_ret_to (ir_nl1 ir_d12) (ir_lzd_max_false_sseg_st1 mem a b1 b2 na dests rest) (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) (ir_vl1 (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)))) := (ir_safe_pad G ir_lzd_module n ir_d1 (ir_ret_to (ir_nl1 ir_d12) (ir_lzd_max_false_sseg_st1 mem a b1 b2 na dests rest) (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) (ir_vl1 (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)))) (ih1 G (ir_nl1 ir_d13) (ir_lzd_max_false_sseg_st2 mem a b1 b2 na dests rest) (fun (mA : (IRList IRMemSlot)) (nA : Nat) (vsA : IRList IRScalar) (hqA : ir_lzd_zpost (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) Bool.false mA nA vsA) => hqA (ir_safe G ir_lzd_module n (ir_ret_to (ir_nl1 ir_d13) (ir_lzd_max_false_sseg_st2 mem a b1 b2 na dests rest) mA nA vsA)) (fun (eA : MemExt (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) mA nA) (hvA : Eq (IRList IRScalar) vsA (ir_vl1 (IRScalar.bool_ Bool.false))) => Eq.subst (IRList IRScalar) (fun (v : IRList IRScalar) => ir_safe G ir_lzd_module n (ir_ret_to (ir_nl1 ir_d13) (ir_lzd_max_false_sseg_st2 mem a b1 b2 na dests rest) mA nA v)) (ir_vl1 (IRScalar.bool_ Bool.false)) vsA (Eq.symm (IRList IRScalar) vsA (ir_vl1 (IRScalar.bool_ Bool.false)) hvA) (ir_lzd_max_false_sseg_r2 mem a b1 b2 na n G dests rest hK mA nA (ir_mem_ext_trans mem na (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) ex1 mA nA eA))))))";
const SRC_IR_LZD_MAX_FALSE_SSEG: &str = "def ir_lzd_max_false_sseg (mem : (IRList IRMemSlot)) (a : Nat) (b1 : Nat) (b2 : Nat) (na : Nat) (n : Nat) (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ (Nat.succ b1)) (IRScalar.ptr_ (Nat.succ b2)))) Bool.true))) (h8 : Eq (IROption IRMemSlot) (ir_mem_lookup mem (Nat.add a ir_d8)) (IROption.some IRMemSlot (IRMemSlot.mk (Nat.add a ir_d8) (IRScalar.ptr_ (Nat.succ b1)) Bool.true))) (h16 : Eq (IROption IRMemSlot) (ir_mem_lookup mem (Nat.add a ir_d16)) (IROption.some IRMemSlot (IRMemSlot.mk (Nat.add a ir_d16) (IRScalar.ptr_ (Nat.succ b2)) Bool.true))) (hlt8 : Eq Bool (ir_nat_ltb (Nat.add a ir_d8) na) Bool.true) (hlt16 : Eq Bool (ir_nat_ltb (Nat.add a ir_d16) na) Bool.true) (hcb1 : forall (mx : IRList IRMemSlot) (nx : Nat), MemExt mem na mx nx -> Eq IRStepResult (ir_borrow_eval mx (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16))) (IRStepResult.value (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)))) (hcb2 : forall (mx : IRList IRMemSlot) (nx : Nat), MemExt mem na mx nx -> Eq IRStepResult (ir_borrow_eval mx (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16))) (IRStepResult.value (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)))) (ih1 : ir_ctr_at ir_lzd_module (ir_lzd_mach0_s (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) (Nat.succ na)) (ir_lzd_zpost (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) Bool.false) n) : ir_ctr_at ir_lzd_module (ir_lzd_mach0_s mem (IRScalar.ptr_ a) na) (ir_lzd_zpost mem na Bool.false) (Nat.succ n) := fun (G : IROutcome -> Prop) (dests : IRList Nat) (rest : IRList IRFrame) (hK : forall (mem2 : (IRList IRMemSlot)) (na2 : Nat) (vs : IRList IRScalar), ir_lzd_zpost mem na Bool.false mem2 na2 vs -> ir_safe G ir_lzd_module (Nat.succ n) (ir_ret_to dests rest mem2 na2 vs)) => Eq.subst (IROption IRMemSlot) (fun (o : (IROption IRMemSlot)) => ir_safe G ir_lzd_module n (ir_lzd_after_load mem a na dests rest o)) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ (Nat.succ b1)) (IRScalar.ptr_ (Nat.succ b2)))) Bool.true)) (ir_mem_lookup mem a) (Eq.symm (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ (Nat.succ b1)) (IRScalar.ptr_ (Nat.succ b2)))) Bool.true)) h) (ir_safe_pad G ir_lzd_module n ir_d7 (ir_lzd_after_load mem a na dests rest (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ (Nat.succ b1)) (IRScalar.ptr_ (Nat.succ b2)))) Bool.true))) (ir_lzd_deref_ctr mem (Nat.add a ir_d8) b1 na (ir_lzd_ltb_ext mem na mem na (MemExt.refl mem na) (Nat.add a ir_d8) hlt8) (Eq.trans (IROption IRMemSlot) (ir_mem_lookup mem (Nat.add a ir_d8)) (ir_mem_lookup mem (Nat.add a ir_d8)) (IROption.some IRMemSlot (IRMemSlot.mk (Nat.add a ir_d8) (IRScalar.ptr_ (Nat.succ b1)) Bool.true)) (ir_lzd_lookup_ext mem na mem na (MemExt.refl mem na) (Nat.add a ir_d8) hlt8) h8) (hcb1 (ir_cell na IRScalar.undef_ mem) (Nat.succ na) (ir_mem_ext_trans mem na mem na (MemExt.refl mem na) (ir_cell na IRScalar.undef_ mem) (Nat.succ na) (ir_mem_ext_one mem na IRScalar.undef_))) n G (ir_nl1 ir_d12) (ir_lzd_max_false_sseg_st1 mem a b1 b2 na dests rest) (fun (m1 : (IRList IRMemSlot)) (n1 : Nat) (v1 : IRList IRScalar) (hq1 : ir_post_exact (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) (ir_vl1 (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16))) m1 n1 v1) => hq1 (fun (m1 : (IRList IRMemSlot)) (n1 : Nat) (v1 : IRList IRScalar) => ir_safe G ir_lzd_module n (ir_ret_to (ir_nl1 ir_d12) (ir_lzd_max_false_sseg_st1 mem a b1 b2 na dests rest) m1 n1 v1)) (ir_lzd_max_false_sseg_r1 mem a b1 b2 na n ih1 G dests rest hK (ir_mem_ext_trans mem na mem na (MemExt.refl mem na) (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) (ir_mem_ext_one mem na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil)))))))))";
const SRC_IR_LZD_MAX_TRUE_SSEG_ST1: &str = "def ir_lzd_max_true_sseg_st1 (mem : (IRList IRMemSlot)) (a : Nat) (b1 : Nat) (b2 : Nat) (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame) : IRList IRFrame := ir_frames_tail (ir_config_frames (ir_steps ir_d7 ir_lzd_module (ir_lzd_after_load mem a na dests rest (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ (Nat.succ b1)) (IRScalar.ptr_ (Nat.succ b2)))) Bool.true)))))";
const SRC_IR_LZD_MAX_TRUE_SSEG_ST2: &str = "def ir_lzd_max_true_sseg_st2 (mem : (IRList IRMemSlot)) (a : Nat) (b1 : Nat) (b2 : Nat) (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame) : IRList IRFrame := ir_frames_tail (ir_config_frames (ir_steps ir_d1 ir_lzd_module (ir_ret_to (ir_nl1 ir_d12) (ir_lzd_max_true_sseg_st1 mem a b1 b2 na dests rest) (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) (ir_vl1 (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16))))))";
const SRC_IR_LZD_MAX_TRUE_SSEG_ST3: &str = "def ir_lzd_max_true_sseg_st3 (mem : (IRList IRMemSlot)) (a : Nat) (b1 : Nat) (b2 : Nat) (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame) (mA : (IRList IRMemSlot)) (nA : Nat) : IRList IRFrame := ir_frames_tail (ir_config_frames (ir_steps ir_d2 ir_lzd_module (ir_ret_to (ir_nl1 ir_d13) (ir_lzd_max_true_sseg_st2 mem a b1 b2 na dests rest) mA nA (ir_vl1 (IRScalar.bool_ Bool.true)))))";
const SRC_IR_LZD_MAX_TRUE_SSEG_ST4: &str = "def ir_lzd_max_true_sseg_st4 (mem : (IRList IRMemSlot)) (a : Nat) (b1 : Nat) (b2 : Nat) (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame) (mA : (IRList IRMemSlot)) (nA : Nat) : IRList IRFrame := ir_frames_tail (ir_config_frames (ir_steps ir_d1 ir_lzd_module (ir_ret_to (ir_nl1 ir_d18) (ir_lzd_max_true_sseg_st3 mem a b1 b2 na dests rest mA nA) (ir_cell nA (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) IRScalar.vnil))) mA) (Nat.succ nA) (ir_vl1 (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16))))))";
const SRC_IR_LZD_MAX_TRUE_SSEG_R4: &str = "def ir_lzd_max_true_sseg_r4 (mem : (IRList IRMemSlot)) (a : Nat) (b1 : Nat) (b2 : Nat) (ans2 : Bool) (na : Nat) (n : Nat) (G : IROutcome -> Prop) (dests : IRList Nat) (rest : IRList IRFrame) (hK : forall (mem2 : (IRList IRMemSlot)) (na2 : Nat) (vs : IRList IRScalar), ir_lzd_zpost mem na ans2 mem2 na2 vs -> ir_safe G ir_lzd_module (Nat.succ n) (ir_ret_to dests rest mem2 na2 vs)) (mA : (IRList IRMemSlot)) (nA : Nat) (mB : (IRList IRMemSlot)) (nB : Nat) (ex4 : MemExt mem na mB nB) : ir_safe G ir_lzd_module n (ir_ret_to (ir_nl1 ir_d19) (ir_lzd_max_true_sseg_st4 mem a b1 b2 na dests rest mA nA) mB nB (ir_vl1 (IRScalar.bool_ ans2))) := (ir_safe_pad G ir_lzd_module n ir_d3 (ir_ret_to (ir_nl1 ir_d19) (ir_lzd_max_true_sseg_st4 mem a b1 b2 na dests rest mA nA) mB nB (ir_vl1 (IRScalar.bool_ ans2))) (ir_safe_down G ir_lzd_module n (ir_ret_to dests rest mB nB (ir_vl1 (IRScalar.bool_ ans2))) (hK mB nB (ir_vl1 (IRScalar.bool_ ans2)) (ir_lzd_zpost_intro mem na ans2 mB nB ex4))))";
const SRC_IR_LZD_MAX_TRUE_SSEG_R3: &str = "def ir_lzd_max_true_sseg_r3 (mem : (IRList IRMemSlot)) (a : Nat) (b1 : Nat) (b2 : Nat) (ans2 : Bool) (na : Nat) (n : Nat) (ih2 : forall (mA : (IRList IRMemSlot)) (nA : Nat), MemExt (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) mA nA -> ir_ctr_at ir_lzd_module (ir_lzd_mach0_s (ir_cell nA (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) IRScalar.vnil))) mA) (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) (Nat.succ nA)) (ir_lzd_zpost (ir_cell nA (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) IRScalar.vnil))) mA) (Nat.succ nA) ans2) n) (G : IROutcome -> Prop) (dests : IRList Nat) (rest : IRList IRFrame) (hK : forall (mem2 : (IRList IRMemSlot)) (na2 : Nat) (vs : IRList IRScalar), ir_lzd_zpost mem na ans2 mem2 na2 vs -> ir_safe G ir_lzd_module (Nat.succ n) (ir_ret_to dests rest mem2 na2 vs)) (mA : (IRList IRMemSlot)) (nA : Nat) (eA : MemExt (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) mA nA) (ex3 : MemExt mem na (ir_cell nA (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) IRScalar.vnil))) mA) (Nat.succ nA)) : ir_safe G ir_lzd_module n (ir_ret_to (ir_nl1 ir_d18) (ir_lzd_max_true_sseg_st3 mem a b1 b2 na dests rest mA nA) (ir_cell nA (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) IRScalar.vnil))) mA) (Nat.succ nA) (ir_vl1 (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)))) := (ir_safe_pad G ir_lzd_module n ir_d1 (ir_ret_to (ir_nl1 ir_d18) (ir_lzd_max_true_sseg_st3 mem a b1 b2 na dests rest mA nA) (ir_cell nA (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) IRScalar.vnil))) mA) (Nat.succ nA) (ir_vl1 (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)))) ((ih2 mA nA eA) G (ir_nl1 ir_d19) (ir_lzd_max_true_sseg_st4 mem a b1 b2 na dests rest mA nA) (fun (mB : (IRList IRMemSlot)) (nB : Nat) (vsB : IRList IRScalar) (hqB : ir_lzd_zpost (ir_cell nA (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) IRScalar.vnil))) mA) (Nat.succ nA) ans2 mB nB vsB) => hqB (ir_safe G ir_lzd_module n (ir_ret_to (ir_nl1 ir_d19) (ir_lzd_max_true_sseg_st4 mem a b1 b2 na dests rest mA nA) mB nB vsB)) (fun (eB : MemExt (ir_cell nA (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) IRScalar.vnil))) mA) (Nat.succ nA) mB nB) (hvB : Eq (IRList IRScalar) vsB (ir_vl1 (IRScalar.bool_ ans2))) => Eq.subst (IRList IRScalar) (fun (v : IRList IRScalar) => ir_safe G ir_lzd_module n (ir_ret_to (ir_nl1 ir_d19) (ir_lzd_max_true_sseg_st4 mem a b1 b2 na dests rest mA nA) mB nB v)) (ir_vl1 (IRScalar.bool_ ans2)) vsB (Eq.symm (IRList IRScalar) vsB (ir_vl1 (IRScalar.bool_ ans2)) hvB) (ir_lzd_max_true_sseg_r4 mem a b1 b2 ans2 na n G dests rest hK mA nA mB nB (ir_mem_ext_trans mem na (ir_cell nA (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) IRScalar.vnil))) mA) (Nat.succ nA) ex3 mB nB eB))))))";
const SRC_IR_LZD_MAX_TRUE_SSEG_R2: &str = "def ir_lzd_max_true_sseg_r2 (mem : (IRList IRMemSlot)) (a : Nat) (b1 : Nat) (b2 : Nat) (ans2 : Bool) (na : Nat) (n : Nat) (h16 : Eq (IROption IRMemSlot) (ir_mem_lookup mem (Nat.add a ir_d16)) (IROption.some IRMemSlot (IRMemSlot.mk (Nat.add a ir_d16) (IRScalar.ptr_ (Nat.succ b2)) Bool.true))) (hlt16 : Eq Bool (ir_nat_ltb (Nat.add a ir_d16) na) Bool.true) (hcb2 : forall (mx : IRList IRMemSlot) (nx : Nat), MemExt mem na mx nx -> Eq IRStepResult (ir_borrow_eval mx (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16))) (IRStepResult.value (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)))) (ih2 : forall (mA : (IRList IRMemSlot)) (nA : Nat), MemExt (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) mA nA -> ir_ctr_at ir_lzd_module (ir_lzd_mach0_s (ir_cell nA (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) IRScalar.vnil))) mA) (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) (Nat.succ nA)) (ir_lzd_zpost (ir_cell nA (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) IRScalar.vnil))) mA) (Nat.succ nA) ans2) n) (G : IROutcome -> Prop) (dests : IRList Nat) (rest : IRList IRFrame) (hK : forall (mem2 : (IRList IRMemSlot)) (na2 : Nat) (vs : IRList IRScalar), ir_lzd_zpost mem na ans2 mem2 na2 vs -> ir_safe G ir_lzd_module (Nat.succ n) (ir_ret_to dests rest mem2 na2 vs)) (mA : (IRList IRMemSlot)) (nA : Nat) (eA : MemExt (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) mA nA) (ex2 : MemExt mem na mA nA) : ir_safe G ir_lzd_module n (ir_ret_to (ir_nl1 ir_d13) (ir_lzd_max_true_sseg_st2 mem a b1 b2 na dests rest) mA nA (ir_vl1 (IRScalar.bool_ Bool.true))) := (ir_safe_pad G ir_lzd_module n ir_d2 (ir_ret_to (ir_nl1 ir_d13) (ir_lzd_max_true_sseg_st2 mem a b1 b2 na dests rest) mA nA (ir_vl1 (IRScalar.bool_ Bool.true))) (ir_lzd_deref_ctr mA (Nat.add a ir_d16) b2 nA (ir_lzd_ltb_ext mem na mA nA ex2 (Nat.add a ir_d16) hlt16) (Eq.trans (IROption IRMemSlot) (ir_mem_lookup mA (Nat.add a ir_d16)) (ir_mem_lookup mem (Nat.add a ir_d16)) (IROption.some IRMemSlot (IRMemSlot.mk (Nat.add a ir_d16) (IRScalar.ptr_ (Nat.succ b2)) Bool.true)) (ir_lzd_lookup_ext mem na mA nA ex2 (Nat.add a ir_d16) hlt16) h16) (hcb2 (ir_cell nA IRScalar.undef_ mA) (Nat.succ nA) (ir_mem_ext_trans mem na mA nA ex2 (ir_cell nA IRScalar.undef_ mA) (Nat.succ nA) (ir_mem_ext_one mA nA IRScalar.undef_))) n G (ir_nl1 ir_d18) (ir_lzd_max_true_sseg_st3 mem a b1 b2 na dests rest mA nA) (fun (m2 : (IRList IRMemSlot)) (n2 : Nat) (v2 : IRList IRScalar) (hq2 : ir_post_exact (ir_cell nA (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) IRScalar.vnil))) mA) (Nat.succ nA) (ir_vl1 (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16))) m2 n2 v2) => hq2 (fun (m2 : (IRList IRMemSlot)) (n2 : Nat) (v2 : IRList IRScalar) => ir_safe G ir_lzd_module n (ir_ret_to (ir_nl1 ir_d18) (ir_lzd_max_true_sseg_st3 mem a b1 b2 na dests rest mA nA) m2 n2 v2)) (ir_lzd_max_true_sseg_r3 mem a b1 b2 ans2 na n ih2 G dests rest hK mA nA eA (ir_mem_ext_trans mem na mA nA ex2 (ir_cell nA (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) IRScalar.vnil))) mA) (Nat.succ nA) (ir_mem_ext_one mA nA (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) IRScalar.vnil)))))))))";
const SRC_IR_LZD_MAX_TRUE_SSEG_R1: &str = "def ir_lzd_max_true_sseg_r1 (mem : (IRList IRMemSlot)) (a : Nat) (b1 : Nat) (b2 : Nat) (ans2 : Bool) (na : Nat) (n : Nat) (h16 : Eq (IROption IRMemSlot) (ir_mem_lookup mem (Nat.add a ir_d16)) (IROption.some IRMemSlot (IRMemSlot.mk (Nat.add a ir_d16) (IRScalar.ptr_ (Nat.succ b2)) Bool.true))) (hlt16 : Eq Bool (ir_nat_ltb (Nat.add a ir_d16) na) Bool.true) (hcb2 : forall (mx : IRList IRMemSlot) (nx : Nat), MemExt mem na mx nx -> Eq IRStepResult (ir_borrow_eval mx (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16))) (IRStepResult.value (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)))) (ih1 : ir_ctr_at ir_lzd_module (ir_lzd_mach0_s (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) (Nat.succ na)) (ir_lzd_zpost (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) Bool.true) n) (ih2 : forall (mA : (IRList IRMemSlot)) (nA : Nat), MemExt (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) mA nA -> ir_ctr_at ir_lzd_module (ir_lzd_mach0_s (ir_cell nA (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) IRScalar.vnil))) mA) (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) (Nat.succ nA)) (ir_lzd_zpost (ir_cell nA (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) IRScalar.vnil))) mA) (Nat.succ nA) ans2) n) (G : IROutcome -> Prop) (dests : IRList Nat) (rest : IRList IRFrame) (hK : forall (mem2 : (IRList IRMemSlot)) (na2 : Nat) (vs : IRList IRScalar), ir_lzd_zpost mem na ans2 mem2 na2 vs -> ir_safe G ir_lzd_module (Nat.succ n) (ir_ret_to dests rest mem2 na2 vs)) (ex1 : MemExt mem na (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na)) : ir_safe G ir_lzd_module n (ir_ret_to (ir_nl1 ir_d12) (ir_lzd_max_true_sseg_st1 mem a b1 b2 na dests rest) (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) (ir_vl1 (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)))) := (ir_safe_pad G ir_lzd_module n ir_d1 (ir_ret_to (ir_nl1 ir_d12) (ir_lzd_max_true_sseg_st1 mem a b1 b2 na dests rest) (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) (ir_vl1 (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)))) (ih1 G (ir_nl1 ir_d13) (ir_lzd_max_true_sseg_st2 mem a b1 b2 na dests rest) (fun (mA : (IRList IRMemSlot)) (nA : Nat) (vsA : IRList IRScalar) (hqA : ir_lzd_zpost (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) Bool.true mA nA vsA) => hqA (ir_safe G ir_lzd_module n (ir_ret_to (ir_nl1 ir_d13) (ir_lzd_max_true_sseg_st2 mem a b1 b2 na dests rest) mA nA vsA)) (fun (eA : MemExt (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) mA nA) (hvA : Eq (IRList IRScalar) vsA (ir_vl1 (IRScalar.bool_ Bool.true))) => Eq.subst (IRList IRScalar) (fun (v : IRList IRScalar) => ir_safe G ir_lzd_module n (ir_ret_to (ir_nl1 ir_d13) (ir_lzd_max_true_sseg_st2 mem a b1 b2 na dests rest) mA nA v)) (ir_vl1 (IRScalar.bool_ Bool.true)) vsA (Eq.symm (IRList IRScalar) vsA (ir_vl1 (IRScalar.bool_ Bool.true)) hvA) (ir_lzd_max_true_sseg_r2 mem a b1 b2 ans2 na n h16 hlt16 hcb2 ih2 G dests rest hK mA nA eA (ir_mem_ext_trans mem na (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) ex1 mA nA eA))))))";
const SRC_IR_LZD_MAX_TRUE_SSEG: &str = "def ir_lzd_max_true_sseg (mem : (IRList IRMemSlot)) (a : Nat) (b1 : Nat) (b2 : Nat) (ans2 : Bool) (na : Nat) (n : Nat) (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ (Nat.succ b1)) (IRScalar.ptr_ (Nat.succ b2)))) Bool.true))) (h8 : Eq (IROption IRMemSlot) (ir_mem_lookup mem (Nat.add a ir_d8)) (IROption.some IRMemSlot (IRMemSlot.mk (Nat.add a ir_d8) (IRScalar.ptr_ (Nat.succ b1)) Bool.true))) (h16 : Eq (IROption IRMemSlot) (ir_mem_lookup mem (Nat.add a ir_d16)) (IROption.some IRMemSlot (IRMemSlot.mk (Nat.add a ir_d16) (IRScalar.ptr_ (Nat.succ b2)) Bool.true))) (hlt8 : Eq Bool (ir_nat_ltb (Nat.add a ir_d8) na) Bool.true) (hlt16 : Eq Bool (ir_nat_ltb (Nat.add a ir_d16) na) Bool.true) (hcb1 : forall (mx : IRList IRMemSlot) (nx : Nat), MemExt mem na mx nx -> Eq IRStepResult (ir_borrow_eval mx (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16))) (IRStepResult.value (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)))) (hcb2 : forall (mx : IRList IRMemSlot) (nx : Nat), MemExt mem na mx nx -> Eq IRStepResult (ir_borrow_eval mx (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16))) (IRStepResult.value (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)))) (ih1 : ir_ctr_at ir_lzd_module (ir_lzd_mach0_s (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) (Nat.succ na)) (ir_lzd_zpost (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) Bool.true) n) (ih2 : forall (mA : (IRList IRMemSlot)) (nA : Nat), MemExt (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) mA nA -> ir_ctr_at ir_lzd_module (ir_lzd_mach0_s (ir_cell nA (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) IRScalar.vnil))) mA) (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) (Nat.succ nA)) (ir_lzd_zpost (ir_cell nA (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) IRScalar.vnil))) mA) (Nat.succ nA) ans2) n) : ir_ctr_at ir_lzd_module (ir_lzd_mach0_s mem (IRScalar.ptr_ a) na) (ir_lzd_zpost mem na ans2) (Nat.succ n) := fun (G : IROutcome -> Prop) (dests : IRList Nat) (rest : IRList IRFrame) (hK : forall (mem2 : (IRList IRMemSlot)) (na2 : Nat) (vs : IRList IRScalar), ir_lzd_zpost mem na ans2 mem2 na2 vs -> ir_safe G ir_lzd_module (Nat.succ n) (ir_ret_to dests rest mem2 na2 vs)) => Eq.subst (IROption IRMemSlot) (fun (o : (IROption IRMemSlot)) => ir_safe G ir_lzd_module n (ir_lzd_after_load mem a na dests rest o)) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ (Nat.succ b1)) (IRScalar.ptr_ (Nat.succ b2)))) Bool.true)) (ir_mem_lookup mem a) (Eq.symm (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ (Nat.succ b1)) (IRScalar.ptr_ (Nat.succ b2)))) Bool.true)) h) (ir_safe_pad G ir_lzd_module n ir_d7 (ir_lzd_after_load mem a na dests rest (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ (Nat.succ b1)) (IRScalar.ptr_ (Nat.succ b2)))) Bool.true))) (ir_lzd_deref_ctr mem (Nat.add a ir_d8) b1 na (ir_lzd_ltb_ext mem na mem na (MemExt.refl mem na) (Nat.add a ir_d8) hlt8) (Eq.trans (IROption IRMemSlot) (ir_mem_lookup mem (Nat.add a ir_d8)) (ir_mem_lookup mem (Nat.add a ir_d8)) (IROption.some IRMemSlot (IRMemSlot.mk (Nat.add a ir_d8) (IRScalar.ptr_ (Nat.succ b1)) Bool.true)) (ir_lzd_lookup_ext mem na mem na (MemExt.refl mem na) (Nat.add a ir_d8) hlt8) h8) (hcb1 (ir_cell na IRScalar.undef_ mem) (Nat.succ na) (ir_mem_ext_trans mem na mem na (MemExt.refl mem na) (ir_cell na IRScalar.undef_ mem) (Nat.succ na) (ir_mem_ext_one mem na IRScalar.undef_))) n G (ir_nl1 ir_d12) (ir_lzd_max_true_sseg_st1 mem a b1 b2 na dests rest) (fun (m1 : (IRList IRMemSlot)) (n1 : Nat) (v1 : IRList IRScalar) (hq1 : ir_post_exact (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) (ir_vl1 (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16))) m1 n1 v1) => hq1 (fun (m1 : (IRList IRMemSlot)) (n1 : Nat) (v1 : IRList IRScalar) => ir_safe G ir_lzd_module n (ir_ret_to (ir_nl1 ir_d12) (ir_lzd_max_true_sseg_st1 mem a b1 b2 na dests rest) m1 n1 v1)) (ir_lzd_max_true_sseg_r1 mem a b1 b2 ans2 na n h16 hlt16 hcb2 ih1 ih2 G dests rest hK (ir_mem_ext_trans mem na mem na (MemExt.refl mem na) (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) (ir_mem_ext_one mem na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil)))))))))";
// ── the device at the real module: what it admits and what it refuses ─────
const SRC_UNREACHABLE_REFUTES: &str = "def ir_lzd_unreachable_refutes (mem : IRList IRMemSlot) (na : Nat) (Q : IRList IRMemSlot -> Nat -> IRList IRScalar -> Prop) (hc : ir_ctr_at ir_lzd_module (fun (d : IRList Nat) (r : IRList IRFrame) => IRMachine.mk (IRList.cons IRFrame (IRFrame.mk ir_d2 ir_d1 Nat.zero (IRList.nil IRBinding) d) r) mem na) Q ir_d1) (C : Prop) : C := ir_ctr_refutes_bad ir_lzd_module (fun (d : IRList Nat) (r : IRList IRFrame) => IRMachine.mk (IRList.cons IRFrame (IRFrame.mk ir_d2 ir_d1 Nat.zero (IRList.nil IRBinding) d) r) mem na) Q ir_d1 (IRList.nil Nat) (IROutcome.ub IRFault.unreachable) (Eq.refl IRConfig (IRConfig.halted (IROutcome.ub IRFault.unreachable))) (Eq.refl Bool Bool.true) hc C";
const SRC_ASSERT_PATH: &str = "def ir_lzd_assert_path_meets_every_ctr (mem : IRList IRMemSlot) (na : Nat) (Q : IRList IRMemSlot -> Nat -> IRList IRScalar -> Prop) (n : Nat) : ir_ctr_at ir_lzd_module (fun (d : IRList Nat) (r : IRList IRFrame) => IRMachine.mk (IRList.cons IRFrame (IRFrame.mk ir_d3 ir_d2 Nat.zero (IRList.nil IRBinding) d) r) mem na) Q n := fun (G : IROutcome -> Prop) (d : IRList Nat) (r : IRList IRFrame) (_ : forall (mem2 : IRList IRMemSlot) (na2 : Nat) (vs : IRList IRScalar), Q mem2 na2 vs -> ir_safe G ir_lzd_module n (ir_ret_to d r mem2 na2 vs)) => ir_safe_pad G ir_lzd_module n ir_d2 (IRConfig.running (IRMachine.mk (IRList.cons IRFrame (IRFrame.mk ir_d3 ir_d2 Nat.zero (IRList.nil IRBinding) d) r) mem na)) (ir_safe_halted G ir_lzd_module (IROutcome.ub IRFault.assert_failed) n (Eq.refl Bool Bool.true))";
const SRC_PC_OK: &str = "def ir_lzd_pc_ok (ans : Bool) (o : IROutcome) : Prop := ir_run_ok (fun (o2 : IROutcome) => Eq IROutcome o2 (IROutcome.ret (ir_vl1 (IRScalar.bool_ ans)))) o";
const SRC_PC_OK_FUEL_OUT: &str = "def ir_lzd_pc_ok_fuel_out (ans : Bool) : ir_lzd_pc_ok ans IROutcome.fuel_out := Eq.refl Bool Bool.true";
const SRC_PC_OK_PANIC: &str = "def ir_lzd_pc_ok_panic (ans : Bool) : ir_lzd_pc_ok ans (IROutcome.ub IRFault.assert_failed) := Eq.refl Bool Bool.true";
const SRC_PC_OK_RET: &str = "def ir_lzd_pc_ok_ret (ans : Bool) : ir_lzd_pc_ok ans (IROutcome.ret (ir_vl1 (IRScalar.bool_ ans))) := Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.bool_ ans)))";
const SRC_PC_OK_BAD: &str = "def ir_lzd_pc_ok_bad (ans : Bool) (o : IROutcome) (hbad : Eq Bool (ir_bad_halt o) Bool.true) (h : ir_lzd_pc_ok ans o) (C : Prop) : C := IROutcome.rec (fun (o0 : IROutcome) => Eq Bool (ir_bad_halt o0) Bool.true -> ir_lzd_pc_ok ans o0 -> C) (fun (vs : IRList IRScalar) (hb : Eq Bool (ir_bad_halt (IROutcome.ret vs)) Bool.true) (_ : ir_lzd_pc_ok ans (IROutcome.ret vs)) => ir_bool_false_ne_true C hb) (fun (f : IRFault) (hb : Eq Bool (ir_bad_halt (IROutcome.ub f)) Bool.true) (hk : ir_lzd_pc_ok ans (IROutcome.ub f)) => Bool.rec (fun (b : Bool) => Eq Bool (Bool.rec (fun (_ : Bool) => Bool) Bool.true Bool.false b) Bool.true -> ir_bprop (Eq IROutcome (IROutcome.ub f) (IROutcome.ret (ir_vl1 (IRScalar.bool_ ans)))) (Eq Bool Bool.true Bool.true) b -> C) (fun (_ : Eq Bool Bool.true Bool.true) (he : Eq IROutcome (IROutcome.ub f) (IROutcome.ret (ir_vl1 (IRScalar.bool_ ans)))) => Eq.subst IROutcome (fun (o1 : IROutcome) => IROutcome.rec (fun (_ : IROutcome) => Prop) (fun (_ : IRList IRScalar) => C) (fun (_ : IRFault) => Eq Bool Bool.true Bool.true) (fun (_ : IRFault) => Eq Bool Bool.true Bool.true) (fun (_ : IRFault) => Eq Bool Bool.true Bool.true) (fun (_ : IRFault) => Eq Bool Bool.true Bool.true) (Eq Bool Bool.true Bool.true) o1) (IROutcome.ub f) (IROutcome.ret (ir_vl1 (IRScalar.bool_ ans))) he (Eq.refl Bool Bool.true)) (fun (hb2 : Eq Bool Bool.false Bool.true) (_ : Eq Bool Bool.true Bool.true) => ir_bool_false_ne_true C hb2) (ir_fault_is_assert f) hb hk) (fun (f : IRFault) (_ : Eq Bool (ir_bad_halt (IROutcome.type_error f)) Bool.true) (he : ir_lzd_pc_ok ans (IROutcome.type_error f)) => Eq.subst IROutcome (fun (o1 : IROutcome) => IROutcome.rec (fun (_ : IROutcome) => Prop) (fun (_ : IRList IRScalar) => C) (fun (_ : IRFault) => Eq Bool Bool.true Bool.true) (fun (_ : IRFault) => Eq Bool Bool.true Bool.true) (fun (_ : IRFault) => Eq Bool Bool.true Bool.true) (fun (_ : IRFault) => Eq Bool Bool.true Bool.true) (Eq Bool Bool.true Bool.true) o1) (IROutcome.type_error f) (IROutcome.ret (ir_vl1 (IRScalar.bool_ ans))) he (Eq.refl Bool Bool.true)) (fun (f : IRFault) (_ : Eq Bool (ir_bad_halt (IROutcome.unmodelled f)) Bool.true) (he : ir_lzd_pc_ok ans (IROutcome.unmodelled f)) => Eq.subst IROutcome (fun (o1 : IROutcome) => IROutcome.rec (fun (_ : IROutcome) => Prop) (fun (_ : IRList IRScalar) => C) (fun (_ : IRFault) => Eq Bool Bool.true Bool.true) (fun (_ : IRFault) => Eq Bool Bool.true Bool.true) (fun (_ : IRFault) => Eq Bool Bool.true Bool.true) (fun (_ : IRFault) => Eq Bool Bool.true Bool.true) (Eq Bool Bool.true Bool.true) o1) (IROutcome.unmodelled f) (IROutcome.ret (ir_vl1 (IRScalar.bool_ ans))) he (Eq.refl Bool Bool.true)) (fun (f : IRFault) (_ : Eq Bool (ir_bad_halt (IROutcome.stuck f)) Bool.true) (he : ir_lzd_pc_ok ans (IROutcome.stuck f)) => Eq.subst IROutcome (fun (o1 : IROutcome) => IROutcome.rec (fun (_ : IROutcome) => Prop) (fun (_ : IRList IRScalar) => C) (fun (_ : IRFault) => Eq Bool Bool.true Bool.true) (fun (_ : IRFault) => Eq Bool Bool.true Bool.true) (fun (_ : IRFault) => Eq Bool Bool.true Bool.true) (fun (_ : IRFault) => Eq Bool Bool.true Bool.true) (Eq Bool Bool.true Bool.true) o1) (IROutcome.stuck f) (IROutcome.ret (ir_vl1 (IRScalar.bool_ ans))) he (Eq.refl Bool Bool.true)) (fun (hb : Eq Bool (ir_bad_halt IROutcome.fuel_out) Bool.true) (_ : ir_lzd_pc_ok ans IROutcome.fuel_out) => ir_bool_false_ne_true C hb) o hbad h";

/// The names this stage registers, in registration order.
pub const LZD_SCTR_NAMES: &[&str] = &[
    "ir_lzd_zpost",
    "ir_lzd_zpost_intro",
    "ir_lzd_deref_ctr",
    "ir_lzd_zero_ctr",
    "ir_lzd_succ_ctr",
    "ir_lzd_param_ctr",
    "ir_lzd_imax_sseg_st1",
    "ir_lzd_imax_sseg_st2",
    "ir_lzd_imax_sseg_r2",
    "ir_lzd_imax_sseg_r1",
    "ir_lzd_imax_sseg",
    "ir_lzd_max_false_sseg_st1",
    "ir_lzd_max_false_sseg_st2",
    "ir_lzd_max_false_sseg_r2",
    "ir_lzd_max_false_sseg_r1",
    "ir_lzd_max_false_sseg",
    "ir_lzd_max_true_sseg_st1",
    "ir_lzd_max_true_sseg_st2",
    "ir_lzd_max_true_sseg_st3",
    "ir_lzd_max_true_sseg_st4",
    "ir_lzd_max_true_sseg_r4",
    "ir_lzd_max_true_sseg_r3",
    "ir_lzd_max_true_sseg_r2",
    "ir_lzd_max_true_sseg_r1",
    "ir_lzd_max_true_sseg",
    "ir_lzd_unreachable_refutes",
    "ir_lzd_assert_path_meets_every_ctr",
    "ir_lzd_pc_ok",
    "ir_lzd_pc_ok_fuel_out",
    "ir_lzd_pc_ok_panic",
    "ir_lzd_pc_ok_ret",
    "ir_lzd_pc_ok_bad",
];

/// `(source, description)`, positionally paired with [`LZD_SCTR_NAMES`].
const DECLS: &[(&str, &str)] = &[
    (
        SRC_ZPOST,
        "ir_lzd_zpost: function 0's POST -- the heap and counter the call returns with EXTEND the ones it was entered with (MemExt), and the returned values are the one Bool `ans`. A Church-encoded conjunction, so the stage names no And. The Full assembly sets ans := level_is_zero l. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_ZPOST_INTRO,
        "ir_lzd_zpost_intro: its introduction, from a MemExt witness. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_DEREF_CTR,
        "ir_lzd_deref_ctr: *** THE DEREF CHAIN'S CONTRACT, DISCHARGED BY ITS EXACT RUN. *** ir_lzd_deref_activation -- forty exact steps through <LevelArc as Deref>::deref, Option::as_deref, Option::expect and <Arc<Level>>::deref, including as_deref's and expect's unreachable switch defaults and expect's assert path, none of which the run reaches under its premises -- through the adapter ir_ctr_exact: at every budget, for every caller, the deref's entry meets the contract whose post is its EXACT final triple (the return slot allocated, the counter advanced, the child pointer returned). DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_ZERO_CTR,
        "ir_lzd_zero_ctr: the Zero leaf's exact six-step run (ir_lzd_activation_zero) lifted by the adapter ir_ctr_of_exact: at every budget the body meets its contract with answer true and the heap unchanged. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_SUCC_CTR,
        "ir_lzd_succ_ctr: the Succ leaf, answer false, likewise. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_PARAM_CTR,
        "ir_lzd_param_ctr: the Param leaf, answer false, likewise. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_IR_LZD_IMAX_SSEG_ST1,
        "ir_lzd_imax_sseg_st1: the frame stack beneath the callee the body's first call pushes -- ir_frames_tail (ir_config_frames c) at the configuration after the body's load and first literal run, NAMED so every statement that returns into it is O(1) text in the number of calls before it (spelled out, it carries the whole execution history, and the segment chain measured superlinear on exactly that). A def, not a claim: definitional unfolding recovers the spelled-out stack. One lemma per call (D5's re-decided remedy; designs/2026-09-24-e2-contract-soundness.md section 9): MINTED by scripts/gen_lzd_sctr.py. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_IR_LZD_IMAX_SSEG_ST2,
        "ir_lzd_imax_sseg_st2: the frame stack beneath the callee the body's second call pushes -- ir_frames_tail (ir_config_frames c) at the configuration ir_lzd_imax_sseg_st1's call returned to, one literal run on, NAMED so every statement that returns into it is O(1) text in the number of calls before it (spelled out, it carries the whole execution history, and the segment chain measured superlinear on exactly that). A def, not a claim: definitional unfolding recovers the spelled-out stack. One lemma per call (D5's re-decided remedy; designs/2026-09-24-e2-contract-soundness.md section 9): MINTED by scripts/gen_lzd_sctr.py. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_IR_LZD_IMAX_SSEG_R2,
        "ir_lzd_imax_sseg_r2: resume segment 2 of ir_lzd_imax_sseg -- the configuration IMax's body resumes at after its recursive call (ih2), at the heap THAT call returned: the last literal run to the body's ret, where the caller's continuation hK takes over. One lemma per call (D5's re-decided remedy; designs/2026-09-24-e2-contract-soundness.md section 9): MINTED by scripts/gen_lzd_sctr.py. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_IR_LZD_IMAX_SSEG_R1,
        "ir_lzd_imax_sseg_r1: resume segment 1 of ir_lzd_imax_sseg -- the configuration IMax's body resumes at after the deref's contract returned (its exact post, by substitution): one literal step and the recursive call on the second child, consuming ih2 at n; its continuation applies ir_lzd_imax_sseg_r2. One lemma per call (D5's re-decided remedy; designs/2026-09-24-e2-contract-soundness.md section 9): MINTED by scripts/gen_lzd_sctr.py. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_IR_LZD_IMAX_SSEG,
        "ir_lzd_imax_sseg: *** IMax's LOCAL OBLIGATION, STEP-INDEXED. *** From the recursion group's contract for the second child at budget n (ih2) and the deref's contract, the body entered at an IMax cell meets its contract at succ n: the load pays the one step, the six literal steps, the deref and the call's push are padded (ir_safe_pad), the call consumes ih2 at n, and the post's answer is returned. MINTED by scripts/gen_lzd_sctr.py from the exact chain's segment list, ONE LEMMA PER CALL: this proof walks the body through the deref and applies ir_lzd_imax_sseg_r1; the statement is the nested form's, byte for byte. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_IR_LZD_MAX_FALSE_SSEG_ST1,
        "ir_lzd_max_false_sseg_st1: the frame stack beneath the callee the body's first call pushes -- ir_frames_tail (ir_config_frames c) at the configuration after the body's load and first literal run, NAMED so every statement that returns into it is O(1) text in the number of calls before it (spelled out, it carries the whole execution history, and the segment chain measured superlinear on exactly that). A def, not a claim: definitional unfolding recovers the spelled-out stack. One lemma per call (D5's re-decided remedy; designs/2026-09-24-e2-contract-soundness.md section 9): MINTED by scripts/gen_lzd_sctr.py. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_IR_LZD_MAX_FALSE_SSEG_ST2,
        "ir_lzd_max_false_sseg_st2: the frame stack beneath the callee the body's second call pushes -- ir_frames_tail (ir_config_frames c) at the configuration ir_lzd_max_false_sseg_st1's call returned to, one literal run on, NAMED so every statement that returns into it is O(1) text in the number of calls before it (spelled out, it carries the whole execution history, and the segment chain measured superlinear on exactly that). A def, not a claim: definitional unfolding recovers the spelled-out stack. One lemma per call (D5's re-decided remedy; designs/2026-09-24-e2-contract-soundness.md section 9): MINTED by scripts/gen_lzd_sctr.py. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_IR_LZD_MAX_FALSE_SSEG_R2,
        "ir_lzd_max_false_sseg_r2: resume segment 2 of ir_lzd_max_false_sseg -- the configuration Max's short-circuit body resumes at after its recursive call (ih1, answer false), at the heap that call returned: the literal run to the body's ret and hK. One lemma per call (D5's re-decided remedy; designs/2026-09-24-e2-contract-soundness.md section 9): MINTED by scripts/gen_lzd_sctr.py. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_IR_LZD_MAX_FALSE_SSEG_R1,
        "ir_lzd_max_false_sseg_r1: resume segment 1 of ir_lzd_max_false_sseg -- the configuration it resumes at after the first deref's contract returned: one literal step and the recursive call on the first child (ih1 at n); its continuation applies ir_lzd_max_false_sseg_r2. One lemma per call (D5's re-decided remedy; designs/2026-09-24-e2-contract-soundness.md section 9): MINTED by scripts/gen_lzd_sctr.py. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_IR_LZD_MAX_FALSE_SSEG,
        "ir_lzd_max_false_sseg: *** Max's SHORT-CIRCUIT LOCAL OBLIGATION, STEP-INDEXED. *** One deref and one recursive call on the first child, whose contract (ih1, at n) returns false, then the short circuit to the body's ret: the body meets its contract at succ n with answer false. MINTED by scripts/gen_lzd_sctr.py ONE LEMMA PER CALL: this proof walks the body through the deref and applies ir_lzd_max_false_sseg_r1; the statement is the nested form's, byte for byte. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_IR_LZD_MAX_TRUE_SSEG_ST1,
        "ir_lzd_max_true_sseg_st1: the frame stack beneath the callee the body's first call pushes -- ir_frames_tail (ir_config_frames c) at the configuration after the body's load and first literal run, NAMED so every statement that returns into it is O(1) text in the number of calls before it (spelled out, it carries the whole execution history, and the segment chain measured superlinear on exactly that). A def, not a claim: definitional unfolding recovers the spelled-out stack. One lemma per call (D5's re-decided remedy; designs/2026-09-24-e2-contract-soundness.md section 9): MINTED by scripts/gen_lzd_sctr.py. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_IR_LZD_MAX_TRUE_SSEG_ST2,
        "ir_lzd_max_true_sseg_st2: the frame stack beneath the callee the body's second call pushes -- ir_frames_tail (ir_config_frames c) at the configuration ir_lzd_max_true_sseg_st1's call returned to, one literal run on, NAMED so every statement that returns into it is O(1) text in the number of calls before it (spelled out, it carries the whole execution history, and the segment chain measured superlinear on exactly that). A def, not a claim: definitional unfolding recovers the spelled-out stack. One lemma per call (D5's re-decided remedy; designs/2026-09-24-e2-contract-soundness.md section 9): MINTED by scripts/gen_lzd_sctr.py. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_IR_LZD_MAX_TRUE_SSEG_ST3,
        "ir_lzd_max_true_sseg_st3: the frame stack beneath the callee the body's third call pushes -- ir_frames_tail (ir_config_frames c) at the configuration ir_lzd_max_true_sseg_st2's call returned to, one literal run on, NAMED so every statement that returns into it is O(1) text in the number of calls before it (spelled out, it carries the whole execution history, and the segment chain measured superlinear on exactly that). A def, not a claim: definitional unfolding recovers the spelled-out stack. One lemma per call (D5's re-decided remedy; designs/2026-09-24-e2-contract-soundness.md section 9): MINTED by scripts/gen_lzd_sctr.py. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_IR_LZD_MAX_TRUE_SSEG_ST4,
        "ir_lzd_max_true_sseg_st4: the frame stack beneath the callee the body's fourth call pushes -- ir_frames_tail (ir_config_frames c) at the configuration ir_lzd_max_true_sseg_st3's call returned to, one literal run on, NAMED so every statement that returns into it is O(1) text in the number of calls before it (spelled out, it carries the whole execution history, and the segment chain measured superlinear on exactly that). A def, not a claim: definitional unfolding recovers the spelled-out stack. One lemma per call (D5's re-decided remedy; designs/2026-09-24-e2-contract-soundness.md section 9): MINTED by scripts/gen_lzd_sctr.py. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_IR_LZD_MAX_TRUE_SSEG_R4,
        "ir_lzd_max_true_sseg_r4: resume segment 4 of ir_lzd_max_true_sseg -- the configuration Max's two-call body resumes at after its SECOND recursive call (ih2 mA nA eA), at the heap that call returned: the literal run to the body's ret and hK. One lemma per call (D5's re-decided remedy; designs/2026-09-24-e2-contract-soundness.md section 9): MINTED by scripts/gen_lzd_sctr.py. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_IR_LZD_MAX_TRUE_SSEG_R3,
        "ir_lzd_max_true_sseg_r3: resume segment 3 of ir_lzd_max_true_sseg -- the configuration it resumes at after the second deref's contract returned: one literal step and the second recursive call, whose contract ih2 is instantiated at the heap the FIRST call returned (mA, nA, eA -- ordinary binders here); its continuation applies ir_lzd_max_true_sseg_r4. One lemma per call (D5's re-decided remedy; designs/2026-09-24-e2-contract-soundness.md section 9): MINTED by scripts/gen_lzd_sctr.py. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_IR_LZD_MAX_TRUE_SSEG_R2,
        "ir_lzd_max_true_sseg_r2: resume segment 2 of ir_lzd_max_true_sseg -- the configuration it resumes at after the FIRST recursive call (ih1, answer true), at the heap that call returned: two literal steps and the second deref, through its contract; its continuation applies ir_lzd_max_true_sseg_r3. One lemma per call (D5's re-decided remedy; designs/2026-09-24-e2-contract-soundness.md section 9): MINTED by scripts/gen_lzd_sctr.py. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_IR_LZD_MAX_TRUE_SSEG_R1,
        "ir_lzd_max_true_sseg_r1: resume segment 1 of ir_lzd_max_true_sseg -- the configuration it resumes at after the first deref's contract returned: one literal step and the first recursive call (ih1 at n); its continuation applies ir_lzd_max_true_sseg_r2. One lemma per call (D5's re-decided remedy; designs/2026-09-24-e2-contract-soundness.md section 9): MINTED by scripts/gen_lzd_sctr.py. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_IR_LZD_MAX_TRUE_SSEG,
        "ir_lzd_max_true_sseg: *** Max's TWO-CALL LOCAL OBLIGATION, STEP-INDEXED. *** Deref and recurse on the first child (ih1 at n, answer true), then -- at the heap THAT call returned, known only inside its continuation, which is why ih2 is quantified over every extension of the first deref's heap -- deref and recurse on the second (ih2 at n, answer ans2), and return ans2. Both calls consume their contract at exactly n. MINTED by scripts/gen_lzd_sctr.py ONE LEMMA PER CALL: this proof walks the body through the first deref and applies ir_lzd_max_true_sseg_r1; the statement is the nested form's, byte for byte. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_UNREACHABLE_REFUTES,
        "ir_lzd_unreachable_refutes: *** THE DEVICE REFUSES AN UNREACHABLE ARM, AT THE REAL MODULE. *** A machine standing at as_deref's switch default (function 2, block 1, an `unreachable`) meets NO contract at budget one, whatever its post, heap or counter: the step halts ub unreachable, which is bad (ir_ctr_refutes_bad). So a contract that HOLDS for the body is itself the proof that its run never reaches such an arm. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_ASSERT_PATH,
        "ir_lzd_assert_path_meets_every_ctr: *** AND ADMITS THE SANCTIONED PANIC, AT THE REAL MODULE. *** A machine standing at expect's None arm (function 3, block 2: const false, assert) meets EVERY contract at EVERY budget, for every caller: two steps halt ub assert_failed, which ir_sanctioned admits. The panic is safe and never a value. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_PC_OK,
        "ir_lzd_pc_ok: *** THE E2 ACCEPTANCE PREDICATE. *** An outcome of the is_zero run is acceptable at answer `ans` when it is fuel_out (the run has not finished), `ret [bool ans]`, or a sanctioned panic -- ir_run_ok at the acceptor `o = ret [bool ans]`. Every other outcome is refused (ir_lzd_pc_ok_bad). DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_PC_OK_FUEL_OUT,
        "ir_lzd_pc_ok_fuel_out: vacuity pin -- fuel exhaustion is acceptable. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_PC_OK_PANIC,
        "ir_lzd_pc_ok_panic: vacuity pin -- a sanctioned panic is acceptable. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_PC_OK_RET,
        "ir_lzd_pc_ok_ret: vacuity pin -- the right answer is acceptable. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_PC_OK_BAD,
        "ir_lzd_pc_ok_bad: *** THE PREDICATE IS NOT VACUOUS. *** A BAD outcome -- ub other than assert_failed (unreachable included), and every type_error, unmodelled (the atomic arm's included) and stuck outcome -- is NOT acceptable at any answer: it implies anything. IROutcome.rec; a non-ret outcome is not ret [bool ans] by a discriminating Eq.subst. DerivedProved, zero axiom_deps.",
    ),
];

impl Specification {
    /// `Level::is_zero`'s local obligations in step-indexed form. MUST follow
    /// `add_eval_ir_lzd_activation` (the exact deref and leaves) and
    /// `add_eval_ir_ctr` (the device).
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check -- by name.
    pub(super) fn add_eval_ir_lzd_sctr(&mut self) -> Result<(), SpecError> {
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
        assert_eq!(DECLS.len(), LZD_SCTR_NAMES.len());
        for ((src, _), name) in DECLS.iter().zip(LZD_SCTR_NAMES) {
            assert!(src.is_ascii(), "spec sources stay ASCII");
            assert_eq!(src.matches('(').count(), src.matches(')').count(), "{name}");
            assert!(src.starts_with(&format!("def {name} ")), "{name}");
        }
    }

    /// The minted obligations consume the recursion group's contract and the
    /// deref's CONTRACT -- never the exact deref lemma directly, and never an
    /// exact recursion hypothesis.
    #[test]
    fn test_minted_obligations_go_through_contracts() {
        for src in [
            SRC_IR_LZD_IMAX_SSEG,
            SRC_IR_LZD_MAX_FALSE_SSEG,
            SRC_IR_LZD_MAX_TRUE_SSEG,
        ] {
            assert!(src.contains("ir_lzd_deref_ctr"));
            assert!(!src.contains("ir_lzd_deref_activation"));
            assert!(src.contains("ir_safe_pad"));
            assert!(
                src.contains(": ir_ctr_at ir_lzd_module (ir_lzd_mach0_s mem (IRScalar.ptr_ a) na)")
            );
            assert!(src.contains("(Nat.succ n) := fun (G : IROutcome -> Prop)"));
        }
    }

    /// ONE LEMMA PER CALL: every term of an obligation's chain discharges AT
    /// MOST one call, the obligation applies its first resume segment, each
    /// segment applies the next, and the last ends at the body's `ret` (hK).
    /// No term spells out a frame stack: each is a named `_st<i>`, so no term's
    /// text grows with the number of calls before it.
    #[test]
    fn test_obligations_are_minted_one_lemma_per_call() {
        let calls = |src: &str| {
            src.matches("(ir_lzd_deref_ctr ").count()
                + src.matches("(ih1 G ").count()
                + src.matches("(ih2 G ").count()
                + src.matches("((ih2 mA nA eA) G ").count()
        };
        let chains: [(&str, &[&str], &[&str]); 3] = [
            (
                SRC_IR_LZD_IMAX_SSEG,
                &[SRC_IR_LZD_IMAX_SSEG_ST1, SRC_IR_LZD_IMAX_SSEG_ST2],
                &[SRC_IR_LZD_IMAX_SSEG_R1, SRC_IR_LZD_IMAX_SSEG_R2],
            ),
            (
                SRC_IR_LZD_MAX_FALSE_SSEG,
                &[SRC_IR_LZD_MAX_FALSE_SSEG_ST1, SRC_IR_LZD_MAX_FALSE_SSEG_ST2],
                &[SRC_IR_LZD_MAX_FALSE_SSEG_R1, SRC_IR_LZD_MAX_FALSE_SSEG_R2],
            ),
            (
                SRC_IR_LZD_MAX_TRUE_SSEG,
                &[
                    SRC_IR_LZD_MAX_TRUE_SSEG_ST1,
                    SRC_IR_LZD_MAX_TRUE_SSEG_ST2,
                    SRC_IR_LZD_MAX_TRUE_SSEG_ST3,
                    SRC_IR_LZD_MAX_TRUE_SSEG_ST4,
                ],
                &[
                    SRC_IR_LZD_MAX_TRUE_SSEG_R1,
                    SRC_IR_LZD_MAX_TRUE_SSEG_R2,
                    SRC_IR_LZD_MAX_TRUE_SSEG_R3,
                    SRC_IR_LZD_MAX_TRUE_SSEG_R4,
                ],
            ),
        ];
        for (top, stacks, segs) in chains {
            let name = top.split(' ').nth(1).unwrap_or_default();
            // Each stack is ONE layer of history over the previous stack's name.
            for (i, st) in stacks.iter().enumerate() {
                let k = i + 1;
                assert!(st.starts_with(&format!("def {name}_st{k} ")));
                assert!(st.contains(": IRList IRFrame := ir_frames_tail (ir_config_frames "));
                assert_eq!(st.matches("ir_frames_tail").count(), 1, "{name}_st{k}");
                if k == 1 {
                    assert!(st.contains("(ir_lzd_after_load "));
                } else {
                    assert!(st.contains(&format!("({name}_st{} ", k - 1)));
                }
            }
            assert_eq!(calls(top), 1, "{name} discharges exactly its first call");
            assert!(top.contains(&format!("({name}_r1 ")), "{name} applies _r1");
            assert!(
                top.contains(&format!("({name}_st1 ")),
                "{name} names its first stack"
            );
            assert!(
                !top.contains("ir_frames_tail"),
                "{name} spells out no stack"
            );
            for (i, seg) in segs.iter().enumerate() {
                let r = i + 1;
                assert!(seg.starts_with(&format!("def {name}_r{r} ")));
                assert!(seg.contains(": ir_safe G ir_lzd_module n (ir_ret_to "));
                assert!(!seg.contains("ir_lzd_deref_activation"));
                assert!(
                    !seg.contains("ir_frames_tail"),
                    "{name}_r{r} spells out no stack"
                );
                assert!(
                    seg.contains(&format!("({name}_st{r} ")),
                    "{name}_r{r} returns into _st{r}"
                );
                if r < segs.len() {
                    assert_eq!(calls(seg), 1, "{name}_r{r} discharges exactly one call");
                    assert!(seg.contains(&format!("({name}_r{} ", r + 1)));
                } else {
                    assert_eq!(calls(seg), 0, "{name}_r{r} is the tail to the ret");
                    assert!(seg.contains("(hK "));
                }
            }
        }
    }
}
