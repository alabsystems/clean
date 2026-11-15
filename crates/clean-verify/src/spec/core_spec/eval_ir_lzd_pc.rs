// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//! **E2's first instance: `Level::is_zero` through the step-indexed contract
//! device** (decision memo §6 Phase E, E2;
//! `designs/2026-09-24-e2-contract-soundness.md`).
//!
//! The recursion group `{Level::is_zero}` of `ir_lzd_module` as a contract
//! TABLE over `IRLzdIn` (heap, counter, pointer argument, the `Level` it
//! represents): precondition `EncodesLevelArcD`, entry `ir_lzd_mach0_s`, post
//! `ir_lzd_zpost` at `level_is_zero`. `ir_lzd_local` is the body's LOCAL
//! OBLIGATION -- a case analysis on the representation, the recursive calls
//! consuming the group's contracts at the strictly smaller budget -- and
//! `ir_lzd_ctr` is `ir_ctr_group_sound` applied to it: every contract, every
//! budget.
//!
//! **The acceptance statement is partial correctness plus safety**
//! (`ir_lzd_pc`): for EVERY fuel, the outcome of `ir_eval` on a represented
//! Level is `fuel_out`, `ret [bool (level_is_zero l)]`, or a sanctioned panic.
//! It is not the structural A4 `ir_lzd_correct`, which is TOTAL (`Le cost fuel
//! -> ret`); termination is out of scope under D5. The two are tied by
//! `ir_lzd_pc_a4_crosscheck`: the device's answer, plus ONLY the Bool that the
//! structural chain's run returns (`ir_lzd_never_faults`), re-derives
//! `ir_lzd_correct`'s equation. Non-vacuity is witnessed at
//! `encodes_live_ref_d_maxzz_at_init`, on the `ret` arm, at the fuel the run
//! returns at.
//!
//! Full-only (names `Level`, `level_is_zero`, `EncodesLevelArcD`,
//! `ir_outcome_is_ret`, `ir_lzd_never_faults`). `ir_lzd_local` and `ir_lzd_pc`
//! are MINTED by `scripts/gen_lzd_sctr.py`; `--check` byte-compares them.

use super::{SpecError, Specification};

const SRC_LZD_IN: &str =
    "inductive IRLzdIn : Type\n| mk : IRList IRMemSlot -> Nat -> IRScalar -> Level -> IRLzdIn";
const SRC_IN_PRE: &str = "def ir_lzd_in_pre (x : IRLzdIn) : Type := IRLzdIn.rec (fun (_ : IRLzdIn) => Type) (fun (mem : IRList IRMemSlot) (na : Nat) (s : IRScalar) (l : Level) => EncodesLevelArcD mem na s l) x";
const SRC_IN_ENTRY: &str = "def ir_lzd_in_entry (x : IRLzdIn) : IRList Nat -> IRList IRFrame -> IRMachine := IRLzdIn.rec (fun (_ : IRLzdIn) => IRList Nat -> IRList IRFrame -> IRMachine) (fun (mem : IRList IRMemSlot) (na : Nat) (s : IRScalar) (l : Level) => ir_lzd_mach0_s mem s na) x";
const SRC_IN_POST: &str = "def ir_lzd_in_post (x : IRLzdIn) : IRList IRMemSlot -> Nat -> IRList IRScalar -> Prop := IRLzdIn.rec (fun (_ : IRLzdIn) => IRList IRMemSlot -> Nat -> IRList IRScalar -> Prop) (fun (mem : IRList IRMemSlot) (na : Nat) (s : IRScalar) (l : Level) => ir_lzd_zpost mem na (level_is_zero l)) x";
// ── minted by scripts/gen_lzd_sctr.py -- do not edit by hand ──────────────
const SRC_IR_LZD_LOCAL: &str = "def ir_lzd_local (n : Nat) (ih : forall (a : IRLzdIn), ir_lzd_in_pre a -> ir_ctr_at ir_lzd_module (ir_lzd_in_entry a) (ir_lzd_in_post a) n) : forall (x : IRLzdIn), ir_lzd_in_pre x -> ir_ctr_at ir_lzd_module (ir_lzd_in_entry x) (ir_lzd_in_post x) (Nat.succ n) := fun (x : IRLzdIn) => IRLzdIn.rec (fun (x0 : IRLzdIn) => ir_lzd_in_pre x0 -> ir_ctr_at ir_lzd_module (ir_lzd_in_entry x0) (ir_lzd_in_post x0) (Nat.succ n)) (fun (mem : IRList IRMemSlot) (na : Nat) (s : IRScalar) (l : Level) (d : EncodesLevelArcD mem na s l) => EncodesLevelArcD.rec mem na (fun (s0 : IRScalar) (l0 : Level) (_ : EncodesLevelArcD mem na s0 l0) => ir_ctr_at ir_lzd_module (ir_lzd_mach0_s mem s0 na) (ir_lzd_zpost mem na (level_is_zero l0)) (Nat.succ n)) (fun (a0 : Nat) (hlt : Eq Bool (ir_nat_ltb a0 na) Bool.true) (hm : Eq (IROption IRMemSlot) (ir_mem_lookup mem a0) (IROption.some IRMemSlot (IRMemSlot.mk a0 (ir_var ir_d0 ir_sp0) Bool.true))) => ir_lzd_zero_ctr mem a0 na hm (Nat.succ n)) (fun (a0 : Nat) (b : Nat) (l0 : Level) (hlt : Eq Bool (ir_nat_ltb a0 na) Bool.true) (hm : Eq (IROption IRMemSlot) (ir_mem_lookup mem a0) (IROption.some IRMemSlot (IRMemSlot.mk a0 (ir_var ir_d1 (ir_sp1 (IRScalar.ptr_ (Nat.succ b)))) Bool.true))) (_r : EncodesLevelArcD mem na (IRScalar.ptr_ (Nat.add (Nat.succ b) ir_d16)) l0) (_ih : ir_ctr_at ir_lzd_module (ir_lzd_mach0_s mem (IRScalar.ptr_ (Nat.add (Nat.succ b) ir_d16)) na) (ir_lzd_zpost mem na (level_is_zero l0)) (Nat.succ n)) => ir_lzd_succ_ctr mem a0 na b hm (Nat.succ n)) (fun (a0 : Nat) (b1 : Nat) (b2 : Nat) (l1 : Level) (l2 : Level) (hlt : Eq Bool (ir_nat_ltb a0 na) Bool.true) (hlt8 : Eq Bool (ir_nat_ltb (Nat.add a0 ir_d8) na) Bool.true) (hlt16 : Eq Bool (ir_nat_ltb (Nat.add a0 ir_d16) na) Bool.true) (hm : Eq (IROption IRMemSlot) (ir_mem_lookup mem a0) (IROption.some IRMemSlot (IRMemSlot.mk a0 (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ (Nat.succ b1)) (IRScalar.ptr_ (Nat.succ b2)))) Bool.true))) (hm8 : Eq (IROption IRMemSlot) (ir_mem_lookup mem (Nat.add a0 ir_d8)) (IROption.some IRMemSlot (IRMemSlot.mk (Nat.add a0 ir_d8) (IRScalar.ptr_ (Nat.succ b1)) Bool.true))) (hm16 : Eq (IROption IRMemSlot) (ir_mem_lookup mem (Nat.add a0 ir_d16)) (IROption.some IRMemSlot (IRMemSlot.mk (Nat.add a0 ir_d16) (IRScalar.ptr_ (Nat.succ b2)) Bool.true))) (r1 : EncodesLevelArcD mem na (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) l1) (r2 : EncodesLevelArcD mem na (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) l2) (_ih1 : ir_ctr_at ir_lzd_module (ir_lzd_mach0_s mem (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) na) (ir_lzd_zpost mem na (level_is_zero l1)) (Nat.succ n)) (_ih2 : ir_ctr_at ir_lzd_module (ir_lzd_mach0_s mem (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) na) (ir_lzd_zpost mem na (level_is_zero l2)) (Nat.succ n)) => Bool.rec (fun (v : Bool) => Eq Bool (level_is_zero l1) v -> ir_ctr_at ir_lzd_module (ir_lzd_mach0_s mem (IRScalar.ptr_ a0) na) (ir_lzd_zpost mem na (Bool.and v (level_is_zero l2))) (Nat.succ n)) (fun (hf : Eq Bool (level_is_zero l1) Bool.false) => ir_lzd_max_false_sseg mem a0 b1 b2 na n hm hm8 hm16 hlt8 hlt16 (ir_lzd_live_ext mem na (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) l1 r1) (ir_lzd_live_ext mem na (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) l2 r2) (Eq.subst Bool (fun (v : Bool) => ir_ctr_at ir_lzd_module (ir_lzd_mach0_s (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) (Nat.succ na)) (ir_lzd_zpost (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) v) n) (level_is_zero l1) Bool.false hf (ih (IRLzdIn.mk (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) l1) (ir_lzd_frame mem na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) l1 r1)))) (fun (ht : Eq Bool (level_is_zero l1) Bool.true) => ir_lzd_max_true_sseg mem a0 b1 b2 (level_is_zero l2) na n hm hm8 hm16 hlt8 hlt16 (ir_lzd_live_ext mem na (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) l1 r1) (ir_lzd_live_ext mem na (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) l2 r2) (Eq.subst Bool (fun (v : Bool) => ir_ctr_at ir_lzd_module (ir_lzd_mach0_s (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) (Nat.succ na)) (ir_lzd_zpost (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) v) n) (level_is_zero l1) Bool.true ht (ih (IRLzdIn.mk (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) l1) (ir_lzd_frame mem na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) l1 r1))) (fun (mA : IRList IRMemSlot) (nA : Nat) (eA : MemExt (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) mA nA) => (ih (IRLzdIn.mk (ir_cell nA (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) IRScalar.vnil))) mA) (Nat.succ nA) (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) l2) (ir_lzd_frame mA nA (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) IRScalar.vnil))) (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) l2 (ir_lzd_frame_ext mem na (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) l2 r2 mA nA (ir_mem_ext_trans mem na (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) (ir_mem_ext_one mem na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) IRScalar.vnil)))) mA nA eA)))))) (level_is_zero l1) (Eq.refl Bool (level_is_zero l1))) (fun (a0 : Nat) (b1 : Nat) (b2 : Nat) (l1 : Level) (l2 : Level) (hlt : Eq Bool (ir_nat_ltb a0 na) Bool.true) (hlt16 : Eq Bool (ir_nat_ltb (Nat.add a0 ir_d16) na) Bool.true) (hm : Eq (IROption IRMemSlot) (ir_mem_lookup mem a0) (IROption.some IRMemSlot (IRMemSlot.mk a0 (ir_var ir_d3 (ir_sp2 (IRScalar.ptr_ (Nat.succ b1)) (IRScalar.ptr_ (Nat.succ b2)))) Bool.true))) (hm16 : Eq (IROption IRMemSlot) (ir_mem_lookup mem (Nat.add a0 ir_d16)) (IROption.some IRMemSlot (IRMemSlot.mk (Nat.add a0 ir_d16) (IRScalar.ptr_ (Nat.succ b2)) Bool.true))) (r1 : EncodesLevelArcD mem na (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) l1) (r2 : EncodesLevelArcD mem na (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) l2) (_ih1 : ir_ctr_at ir_lzd_module (ir_lzd_mach0_s mem (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) na) (ir_lzd_zpost mem na (level_is_zero l1)) (Nat.succ n)) (_ih2 : ir_ctr_at ir_lzd_module (ir_lzd_mach0_s mem (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) na) (ir_lzd_zpost mem na (level_is_zero l2)) (Nat.succ n)) => ir_lzd_imax_sseg mem a0 b1 b2 (level_is_zero l2) na n hm hm16 hlt16 (ir_lzd_live_ext mem na (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) l2 r2) (ih (IRLzdIn.mk (ir_cell na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) IRScalar.vnil))) mem) (Nat.succ na) (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) l2) (ir_lzd_frame mem na (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) IRScalar.vnil))) (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) l2 r2))) (fun (a0 : Nat) (w : IRScalar) (nm : Name) (hlt : Eq Bool (ir_nat_ltb a0 na) Bool.true) (hm : Eq (IROption IRMemSlot) (ir_mem_lookup mem a0) (IROption.some IRMemSlot (IRMemSlot.mk a0 (ir_var ir_d4 (ir_sp1 w)) Bool.true))) => ir_lzd_param_ctr mem a0 na w hm (Nat.succ n)) s l d) x";
// ──────────────────────────────────────────────────────────────────────────
const SRC_CTR: &str = "def ir_lzd_ctr (n : Nat) : forall (x : IRLzdIn), ir_lzd_in_pre x -> ir_ctr_at ir_lzd_module (ir_lzd_in_entry x) (ir_lzd_in_post x) n := ir_ctr_group_sound ir_lzd_module IRLzdIn ir_lzd_in_pre ir_lzd_in_entry ir_lzd_in_post ir_lzd_local n";
// ── minted by scripts/gen_lzd_sctr.py -- do not edit by hand ──────────────
const SRC_IR_LZD_PC: &str = "def ir_lzd_pc (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (r : IRScalar) (l : Level) (href : EncodesLiveLevelRefD (ir_lzd_init_mem mem) na r l) : ir_lzd_pc_ok (level_is_zero l) (ir_eval fuel ir_lzd_module ir_d0 (ir_vl1 r) mem na) := EncodesLiveLevelRefD.rec (ir_lzd_init_mem mem) na (fun (s0 : IRScalar) (l1 : Level) (_ : EncodesLiveLevelRefD (ir_lzd_init_mem mem) na s0 l1) => ir_lzd_pc_ok (level_is_zero l1) (ir_eval fuel ir_lzd_module ir_d0 (ir_vl1 s0) mem na)) (fun (a : Nat) (l0 : Level) (arc : EncodesLevelArcD (ir_lzd_init_mem mem) na (IRScalar.ptr_ a) l0) => ir_ctr_run ir_lzd_module (ir_lzd_mach0_s (ir_lzd_init_mem mem) (IRScalar.ptr_ a) na) (ir_lzd_zpost (ir_lzd_init_mem mem) na (level_is_zero l0)) fuel (ir_lzd_ctr fuel (IRLzdIn.mk (ir_lzd_init_mem mem) na (IRScalar.ptr_ a) l0) arc) (fun (o2 : IROutcome) => Eq IROutcome o2 (IROutcome.ret (ir_vl1 (IRScalar.bool_ (level_is_zero l0))))) (IRList.nil Nat) (fun (mem2 : IRList IRMemSlot) (na2 : Nat) (vs : IRList IRScalar) (hz : ir_lzd_zpost (ir_lzd_init_mem mem) na (level_is_zero l0) mem2 na2 vs) => hz (Eq IROutcome (IROutcome.ret vs) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (level_is_zero l0))))) (fun (_ : MemExt (ir_lzd_init_mem mem) na mem2 na2) (hv : Eq (IRList IRScalar) vs (ir_vl1 (IRScalar.bool_ (level_is_zero l0)))) => ir_eq_cong (IRList IRScalar) IROutcome IROutcome.ret vs (ir_vl1 (IRScalar.bool_ (level_is_zero l0))) hv))) r l href";
// ──────────────────────────────────────────────────────────────────────────
const SRC_PC_OK_IS_RET: &str = "def ir_lzd_pc_ok_is_ret (ans : Bool) (o : IROutcome) (hok : ir_lzd_pc_ok ans o) (hr : Eq Bool (ir_outcome_is_ret o) Bool.true) : Eq IROutcome o (IROutcome.ret (ir_vl1 (IRScalar.bool_ ans))) := IROutcome.rec (fun (o0 : IROutcome) => ir_lzd_pc_ok ans o0 -> Eq Bool (ir_outcome_is_ret o0) Bool.true -> Eq IROutcome o0 (IROutcome.ret (ir_vl1 (IRScalar.bool_ ans)))) (fun (vs : IRList IRScalar) (h : ir_lzd_pc_ok ans (IROutcome.ret vs)) (_ : Eq Bool (ir_outcome_is_ret (IROutcome.ret vs)) Bool.true) => h) (fun (f : IRFault) (_ : ir_lzd_pc_ok ans (IROutcome.ub f)) (hb : Eq Bool (ir_outcome_is_ret (IROutcome.ub f)) Bool.true) => ir_bool_false_ne_true (Eq IROutcome (IROutcome.ub f) (IROutcome.ret (ir_vl1 (IRScalar.bool_ ans)))) hb) (fun (f : IRFault) (_ : ir_lzd_pc_ok ans (IROutcome.type_error f)) (hb : Eq Bool (ir_outcome_is_ret (IROutcome.type_error f)) Bool.true) => ir_bool_false_ne_true (Eq IROutcome (IROutcome.type_error f) (IROutcome.ret (ir_vl1 (IRScalar.bool_ ans)))) hb) (fun (f : IRFault) (_ : ir_lzd_pc_ok ans (IROutcome.unmodelled f)) (hb : Eq Bool (ir_outcome_is_ret (IROutcome.unmodelled f)) Bool.true) => ir_bool_false_ne_true (Eq IROutcome (IROutcome.unmodelled f) (IROutcome.ret (ir_vl1 (IRScalar.bool_ ans)))) hb) (fun (f : IRFault) (_ : ir_lzd_pc_ok ans (IROutcome.stuck f)) (hb : Eq Bool (ir_outcome_is_ret (IROutcome.stuck f)) Bool.true) => ir_bool_false_ne_true (Eq IROutcome (IROutcome.stuck f) (IROutcome.ret (ir_vl1 (IRScalar.bool_ ans)))) hb) (fun (_ : ir_lzd_pc_ok ans IROutcome.fuel_out) (hb : Eq Bool (ir_outcome_is_ret IROutcome.fuel_out) Bool.true) => ir_bool_false_ne_true (Eq IROutcome IROutcome.fuel_out (IROutcome.ret (ir_vl1 (IRScalar.bool_ ans)))) hb) o hok hr";
const SRC_CROSSCHECK: &str = "def ir_lzd_pc_a4_crosscheck (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (r : IRScalar) (l : Level) (href : EncodesLiveLevelRefD (ir_lzd_init_mem mem) na r l) : Le (ir_lzd_cost l) fuel -> Eq IROutcome (ir_eval fuel ir_lzd_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ret (ir_vl1 (IRScalar.bool_ (level_is_zero l)))) := fun (hle : Le (ir_lzd_cost l) fuel) => ir_lzd_pc_ok_is_ret (level_is_zero l) (ir_eval fuel ir_lzd_module ir_d0 (ir_vl1 r) mem na) (ir_lzd_pc mem fuel na r l href) (ir_lzd_never_faults mem fuel na r l href hle)";
const SRC_NO_BAD_HALT: &str = "def ir_lzd_pc_no_bad_halt (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (r : IRScalar) (l : Level) (href : EncodesLiveLevelRefD (ir_lzd_init_mem mem) na r l) (hbad : Eq Bool (ir_bad_halt (ir_eval fuel ir_lzd_module ir_d0 (ir_vl1 r) mem na)) Bool.true) (C : Prop) : C := ir_lzd_pc_ok_bad (level_is_zero l) (ir_eval fuel ir_lzd_module ir_d0 (ir_vl1 r) mem na) hbad (ir_lzd_pc mem fuel na r l href) C";
const SRC_NEVER_UNREACHABLE: &str = "def ir_lzd_pc_never_unreachable (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (r : IRScalar) (l : Level) (href : EncodesLiveLevelRefD (ir_lzd_init_mem mem) na r l) (h : Eq IROutcome (ir_eval fuel ir_lzd_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ub IRFault.unreachable)) (C : Prop) : C := ir_lzd_pc_no_bad_halt mem fuel na r l href (Eq.subst IROutcome (fun (o : IROutcome) => Eq Bool (ir_bad_halt o) Bool.true) (IROutcome.ub IRFault.unreachable) (ir_eval fuel ir_lzd_module ir_d0 (ir_vl1 r) mem na) (Eq.symm IROutcome (ir_eval fuel ir_lzd_module ir_d0 (ir_vl1 r) mem na) (IROutcome.ub IRFault.unreachable) h) (Eq.refl Bool Bool.true)) C";
const SRC_IN_MAXZZ: &str = "def ir_lzd_in_maxzz : IRLzdIn := IRLzdIn.mk (ir_lzd_init_mem (ir_cell ir_d40 (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ ir_d1) (IRScalar.ptr_ ir_d2))) (ir_cell ir_d48 (IRScalar.ptr_ ir_d1) (ir_cell ir_d56 (IRScalar.ptr_ ir_d2) (ir_cell ir_d17 (ir_var ir_d0 ir_sp0) (ir_cell ir_d18 (ir_var ir_d0 ir_sp0) ir_mem0)))))) ir_d63 (IRScalar.ptr_ ir_d40) (Level.max Level.zero Level.zero)";
const SRC_IN_PRE_WITNESS: &str =
    "def ir_lzd_in_pre_witness : ir_lzd_in_pre ir_lzd_in_maxzz := encodes_arcd_maxzz_at_init";
const SRC_WITNESS: &str = "def ir_lzd_pc_witness_maxzz (fuel : Nat) : ir_lzd_pc_ok Bool.true (ir_eval fuel ir_lzd_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d40)) (ir_cell ir_d40 (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ ir_d1) (IRScalar.ptr_ ir_d2))) (ir_cell ir_d48 (IRScalar.ptr_ ir_d1) (ir_cell ir_d56 (IRScalar.ptr_ ir_d2) (ir_cell ir_d17 (ir_var ir_d0 ir_sp0) (ir_cell ir_d18 (ir_var ir_d0 ir_sp0) ir_mem0))))) ir_d63) := ir_lzd_pc (ir_cell ir_d40 (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ ir_d1) (IRScalar.ptr_ ir_d2))) (ir_cell ir_d48 (IRScalar.ptr_ ir_d1) (ir_cell ir_d56 (IRScalar.ptr_ ir_d2) (ir_cell ir_d17 (ir_var ir_d0 ir_sp0) (ir_cell ir_d18 (ir_var ir_d0 ir_sp0) ir_mem0))))) fuel ir_d63 (IRScalar.ptr_ ir_d40) (Level.max Level.zero Level.zero) encodes_live_ref_d_maxzz_at_init";
const SRC_WITNESS_RET: &str = "def ir_lzd_pc_crosscheck_maxzz : Eq IROutcome (ir_eval (ir_lzd_cost (Level.max Level.zero Level.zero)) ir_lzd_module ir_d0 (ir_vl1 (IRScalar.ptr_ ir_d40)) (ir_cell ir_d40 (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ ir_d1) (IRScalar.ptr_ ir_d2))) (ir_cell ir_d48 (IRScalar.ptr_ ir_d1) (ir_cell ir_d56 (IRScalar.ptr_ ir_d2) (ir_cell ir_d17 (ir_var ir_d0 ir_sp0) (ir_cell ir_d18 (ir_var ir_d0 ir_sp0) ir_mem0))))) ir_d63) (IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true))) := ir_lzd_pc_a4_crosscheck (ir_cell ir_d40 (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ ir_d1) (IRScalar.ptr_ ir_d2))) (ir_cell ir_d48 (IRScalar.ptr_ ir_d1) (ir_cell ir_d56 (IRScalar.ptr_ ir_d2) (ir_cell ir_d17 (ir_var ir_d0 ir_sp0) (ir_cell ir_d18 (ir_var ir_d0 ir_sp0) ir_mem0))))) (ir_lzd_cost (Level.max Level.zero Level.zero)) ir_d63 (IRScalar.ptr_ ir_d40) (Level.max Level.zero Level.zero) encodes_live_ref_d_maxzz_at_init (Le.refl (ir_lzd_cost (Level.max Level.zero Level.zero)))";

/// The declarations this stage registers, in registration order (the first
/// is an inductive).
pub const LZD_PC_NAMES: &[&str] = &[
    "IRLzdIn",
    "ir_lzd_in_pre",
    "ir_lzd_in_entry",
    "ir_lzd_in_post",
    "ir_lzd_local",
    "ir_lzd_ctr",
    "ir_lzd_pc",
    "ir_lzd_pc_ok_is_ret",
    "ir_lzd_pc_a4_crosscheck",
    "ir_lzd_pc_no_bad_halt",
    "ir_lzd_pc_never_unreachable",
    "ir_lzd_in_maxzz",
    "ir_lzd_in_pre_witness",
    "ir_lzd_pc_witness_maxzz",
    "ir_lzd_pc_crosscheck_maxzz",
];

/// `(source, description)` of the definitions, positionally paired with
/// `LZD_PC_NAMES[1..]`.
const DECLS: &[(&str, &str)] = &[
    (
        SRC_IN_PRE,
        "ir_lzd_in_pre: the table's PRECONDITION at an index -- the pointer argument represents the Level in the heap below the counter (EncodesLevelArcD). A large elimination into Type. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_IN_ENTRY,
        "ir_lzd_in_entry: the table's ENTRY at an index -- function 0 entered with the pointer, over the heap and counter, curried over the caller (dests, stack). DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_IN_POST,
        "ir_lzd_in_post: the table's POST at an index -- the heap grew and the call returned [bool (level_is_zero l)]. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_IR_LZD_LOCAL,
        "ir_lzd_local: *** THE LOCAL OBLIGATION OF Level::is_zero's BODY. *** Assuming every contract of the group at budget n, the body's contract holds at succ n for every represented Level: a CASE ANALYSIS on EncodesLevelArcD (never an induction on it -- the recursion is on the budget): the three leaves by their exact runs (ir_lzd_zero_ctr / succ / param), Max by a Bool.rec on level_is_zero of the first child into the short-circuit or the two-call obligation, IMax into its one-call obligation. Each child's contract is the group hypothesis at the heap the deref allocated, its precondition re-framed there (ir_lzd_frame, ir_lzd_frame_ext) and its borrow premise read off the representation (ir_lzd_live_ext). MINTED by scripts/gen_lzd_sctr.py. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_CTR,
        "ir_lzd_ctr: *** Level::is_zero MEETS ITS CONTRACT AT EVERY BUDGET. *** ir_ctr_group_sound on the table (IRLzdIn, ir_lzd_in_pre, ir_lzd_in_entry, ir_lzd_in_post) with the local obligation ir_lzd_local. The deref chain (functions 1-4) enters as ir_lzd_deref_ctr, its exact run through the adapter. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_IR_LZD_PC,
        "ir_lzd_pc: *** E2's ACCEPTANCE THEOREM -- PARTIAL CORRECTNESS PLUS SAFETY FOR Level::is_zero, AT EVERY FUEL. *** For every heap, fuel, counter, pointer and Level with the pointer representing the Level in the initial heap (EncodesLiveLevelRefD, the premise ir_lzd_correct takes), the outcome of ir_eval over ir_lzd_module -- a module with no authored function in it -- is fuel_out, ret [bool (level_is_zero l)], or a sanctioned panic (ir_lzd_pc_ok); never ub unreachable, type_error, unmodelled or stuck. ir_ctr_run at the empty caller stack on ir_lzd_ctr. NOT total correctness: it does not say the run returns (ir_lzd_pc_a4_crosscheck ties it to the structural A4, which does). MINTED by scripts/gen_lzd_sctr.py. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_PC_OK_IS_RET,
        "ir_lzd_pc_ok_is_ret: an acceptable outcome that IS a return is the right return -- the ret arm of ir_lzd_pc_ok is an equation, every other arm contradicts ir_outcome_is_ret. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_CROSSCHECK,
        "ir_lzd_pc_a4_crosscheck: *** THE CROSS-CHECK AGAINST THE STRUCTURAL A4. *** ir_lzd_correct's equation re-derived with the ANSWER from the step-indexed device (ir_lzd_pc) and ONLY the fact that the run returns from the structural chain (ir_lzd_never_faults, a Bool): at fuel >= ir_lzd_cost l the outcome is ret [bool (level_is_zero l)]. Two independent routes agree on the value; termination still comes from the structural chain alone. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_NO_BAD_HALT,
        "ir_lzd_pc_no_bad_halt: at EVERY fuel, the represented run never halts badly -- no ub other than assert_failed, no type_error, unmodelled or stuck. A contract that holds is the refutation of every unreachable arm the run could reach -- as_deref's and expect's switch defaults, the only `unreachable` nodes in the module (function 0's switch default is its IMax arm, not an unreachable) -- and of expect's panic path as a VALUE: a panic would be admitted, never returned. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_NEVER_UNREACHABLE,
        "ir_lzd_pc_never_unreachable: the named instance -- at every fuel, the outcome is never ub unreachable. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_IN_MAXZZ,
        "ir_lzd_in_maxzz: a table index -- Max(Zero, Zero) at address 40 of the initial witness heap, counter 63. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_IN_PRE_WITNESS,
        "ir_lzd_in_pre_witness: the table's precondition is INHABITED -- at ir_lzd_in_maxzz it is encodes_arcd_maxzz_at_init. The premise every contract in the table assumes is satisfiable, not merely stated. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_WITNESS,
        "ir_lzd_pc_witness_maxzz: *** NON-VACUITY. *** ir_lzd_pc instantiated at the inhabited premise encodes_live_ref_d_maxzz_at_init (Max(Zero, Zero) at address 40, counter 63): at every fuel the outcome is acceptable at answer true. DerivedProved, zero axiom_deps.",
    ),
    (
        SRC_WITNESS_RET,
        "ir_lzd_pc_crosscheck_maxzz: *** AND THE ret ARM IS EXERCISED. *** At the same witness, at fuel ir_lzd_cost (Max(Zero, Zero)), the cross-check yields ret [bool true] -- the device's answer, on a real run, at the fuel it returns at. DerivedProved, zero axiom_deps.",
    ),
];

impl Specification {
    /// E2's first instance. Full-only; MUST follow `add_eval_ir_lzd_correct`
    /// (`EncodesLevelArcD`, `ir_lzd_frame*`, `ir_lzd_live_ext`,
    /// `ir_lzd_never_faults`, `encodes_live_ref_d_maxzz_at_init`),
    /// `add_eval_ir_correct` (`ir_outcome_is_ret`) and `add_eval_ir_lzd_sctr`.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check -- by name.
    pub(super) fn add_eval_ir_lzd_pc(&mut self) -> Result<(), SpecError> {
        self.add_inductive(
            SRC_LZD_IN,
            "IRLzdIn: the index of the Level::is_zero contract TABLE -- heap, counter, the pointer argument, and the Level it represents. A plain data carrier, no proof content. DerivedProved, zero axiom_deps.",
        )?;
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
        assert_eq!(DECLS.len() + 1, LZD_PC_NAMES.len());
        assert!(SRC_LZD_IN.starts_with("inductive IRLzdIn "));
        for ((src, _), name) in DECLS.iter().zip(&LZD_PC_NAMES[1..]) {
            assert!(src.is_ascii(), "spec sources stay ASCII");
            assert_eq!(src.matches('(').count(), src.matches(')').count(), "{name}");
            assert!(src.starts_with(&format!("def {name} ")), "{name}");
        }
    }

    /// The contract at every budget is DERIVED by the group-soundness theorem,
    /// not proved by a separate induction; and the acceptance theorem reads it
    /// at the empty caller stack.
    #[test]
    fn test_the_contract_goes_through_group_soundness() {
        assert!(SRC_CTR.contains("ir_ctr_group_sound ir_lzd_module IRLzdIn"));
        assert!(SRC_IR_LZD_PC.contains("ir_ctr_run"));
        assert!(SRC_IR_LZD_PC.contains("(ir_lzd_ctr fuel"));
        assert!(!SRC_IR_LZD_LOCAL.contains("ir_lzd_activation "));
        assert!(SRC_CROSSCHECK.contains("ir_lzd_never_faults"));
        assert!(!SRC_CROSSCHECK.contains("ir_lzd_correct "));
    }
}
