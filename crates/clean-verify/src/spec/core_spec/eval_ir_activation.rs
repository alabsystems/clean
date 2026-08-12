// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The activation lemma, leaf arms** — crystal A4's last prerequisite, in part.
//!
//! One activation of `Level::is_zero`: push a frame whose single parameter is a
//! pointer to a heap-encoded `Level`, run exactly `ir_lz_cost l` steps, and land
//! on the caller's resumption — `ir_ret_to dests rest mem na [bool answer]`.
//!
//! Everything the caller owns stays universally quantified: the heap `mem`, the
//! next-address counter `na`, the call's result ids `dests`, and the whole
//! frame stack `rest` beneath this activation. That generality is the point.
//! `ir_ret_to` is stuck on an opaque `rest`, but it is stuck IDENTICALLY on both
//! sides of the equation, so the lemma states where the machine goes without
//! needing to know who called it — which is what lets the recursive arms feed
//! their own induction hypotheses in.
//!
//! ## The obstacle: you cannot rewrite under a stuck lookup
//!
//! The first instruction of block b0 is `load *self`, which evaluates
//! `ir_mem_lookup mem a`. With `mem` a variable that is STUCK, so the machine
//! does not step and `Eq.refl` proves nothing. The natural move — `Eq.subst` the
//! representation hypothesis `ir_mem_lookup mem a = some cell` — does not apply
//! either, because the goal
//!
//! ```text
//! ir_steps (ir_lz_cost l) M (running (ir_lz_mach0 mem a na dests rest)) = ir_ret_to …
//! ```
//!
//! does not MENTION `ir_mem_lookup mem a` anywhere. `Eq.subst` needs the term it
//! rewrites to occur; abstracting a subterm that is not there yields a constant
//! motive and rewrites nothing.
//!
//! ## The move: make one step expose the lookup, then rewrite
//!
//! `ir_lz_step_load` is the bridge. It says, by `Eq.refl` alone,
//!
//! ```text
//! ir_step M (ir_lz_mach0 mem a na dests rest)
//!   = ir_bind_result (ir_lz_mach0 …) [1] (ir_load_slot (ir_mem_lookup mem a))
//! ```
//!
//! Both sides are already definitionally equal — the content is that the
//! right-hand side is written in a form where `ir_mem_lookup mem a` occurs
//! SYNTACTICALLY. Now the motive `fun o => … (ir_load_slot o) …` is genuine,
//! `Eq.subst` fires, and the remaining four steps compute on a concrete cell.
//!
//! The hypothesis points the wrong way for `Eq.subst`, which carries a proof
//! FORWARDS along the equation: it is the concrete side that has the proof and
//! the stuck side that needs one, so each arm goes through `Eq.symm`.
//!
//! ## What is proved here, and what is not
//!
//! The three LEAF arms — `zero`, `succ`, `param` — all at cost 5. `succ` is a
//! leaf because `Level::is_zero` does not recurse into it (`Succ(_) => false`);
//! the sub-pointer is bound but never followed, which is why the arm quantifies
//! over `b` and never mentions it again. `param` likewise quantifies over an
//! arbitrary payload `w`, matching A2's deliberate freedom there.
//!
//! The recursive arms `max` and `imax` are NOT here. They need blocks b3/b4/b5:
//! a null-check `assert` on the child pointer, a `Call`, the induction
//! hypothesis for the child, and `ir_steps_add` to splice the segments. The
//! assert is now reducible because A2's child fields were narrowed from
//! arbitrary `IRScalar` to `Nat` addresses — see `eval_ir_repr`.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const IRO: &str = "(IROption IRMemSlot)";
const BIND: &str =
    "(mem : IRList IRMemSlot) (a : Nat) (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame)";
const MACH0: &str = "(ir_lz_mach0 mem a na dests rest)";

const SRC_MACH0: &str = "def ir_lz_mach0 (mem : IRList IRMemSlot) (a : Nat) (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame) : IRMachine := IRMachine.mk (IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 Nat.zero (ir_bind_params (ir_nl1 ir_d0) (ir_vl1 (IRScalar.ptr_ a)) (IRList.nil IRBinding)) dests) rest) mem na";

/// The cell the heap must hold at `a`, live, for a given payload.
fn some(val: &str) -> String {
    format!("(IROption.some IRMemSlot (IRMemSlot.mk a {val} Bool.true))")
}

/// Where the caller resumes once this activation returns `ans`.
fn target(ans: &str) -> String {
    format!("(ir_ret_to dests rest mem na (ir_vl1 (IRScalar.bool_ Bool.{ans})))")
}

/// `ir_step` rewritten so the heap lookup occurs syntactically. `Eq.refl` — the
/// content is the SHAPE, not the equality.
fn src_step_load() -> String {
    let rhs =
        format!("(ir_bind_result {MACH0} (ir_nl1 ir_d1) (ir_load_slot (ir_mem_lookup mem a)))");
    format!("def ir_lz_step_load {BIND} : Eq IRConfig (ir_step ir_lz_module {MACH0}) {rhs} := Eq.refl IRConfig {rhs}")
}

/// A leaf activation: five steps from frame push to the caller's resumption.
fn activation(name: &str, extra: &str, val: &str, ans: &str) -> String {
    let (s, t) = (some(val), target(ans));
    let mot = format!(
        "(fun (o : {IRO}) => Eq IRConfig (ir_steps ir_d4 ir_lz_module (ir_bind_result {MACH0} (ir_nl1 ir_d1) (ir_load_slot o))) {t})"
    );
    let body = format!(
        "Eq.subst {IRO} {mot} {s} (ir_mem_lookup mem a) (Eq.symm {IRO} (ir_mem_lookup mem a) {s} h) (Eq.refl IRConfig {t})"
    );
    format!(
        "def {name} {BIND} {extra}(h : Eq {IRO} (ir_mem_lookup mem a) {s}) : Eq IRConfig (ir_steps ir_d5 ir_lz_module (IRConfig.running {MACH0})) {t} := {body}"
    )
}

const SRC_FRAMES_TAIL: &str = "def ir_frames_tail (fs : IRList IRFrame) : IRList IRFrame := IRList.rec IRFrame (fun (_ : IRList IRFrame) => IRList IRFrame) (IRList.nil IRFrame) (fun (_ : IRFrame) (t : IRList IRFrame) (_ : IRList IRFrame) => t) fs";

const SRC_CONFIG_FRAMES: &str = "def ir_config_frames (c : IRConfig) : IRList IRFrame := IRConfig.rec (fun (_ : IRConfig) => IRList IRFrame) (fun (s : IRMachine) => ir_mach_frames s) (fun (_ : IROutcome) => IRList.nil IRFrame) c";

const SRC_AFTER_LOAD: &str = "def ir_lz_after_load (mem : IRList IRMemSlot) (a : Nat) (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame) (o : (IROption IRMemSlot)) : IRConfig := ir_bind_result (ir_lz_mach0 mem a na dests rest) (ir_nl1 ir_d1) (ir_load_slot o)";

const SRC_MAX_TRUE_SEG: &str = "def ir_lz_max_true_seg (mem : IRList IRMemSlot) (a : Nat) (b1 : Nat) (b2 : Nat) (c1 : Nat) (c2 : Nat) (ans2 : Bool) (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame) (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true))) (ih1 : forall (na2 : Nat) (d2 : IRList Nat) (r2 : IRList IRFrame), Eq IRConfig (ir_steps c1 ir_lz_module (IRConfig.running (ir_lz_mach0 mem b1 na2 d2 r2))) (ir_ret_to d2 r2 mem na2 (ir_vl1 (IRScalar.bool_ Bool.true)))) (ih2 : forall (na2 : Nat) (d2 : IRList Nat) (r2 : IRList IRFrame), Eq IRConfig (ir_steps c2 ir_lz_module (IRConfig.running (ir_lz_mach0 mem b2 na2 d2 r2))) (ir_ret_to d2 r2 mem na2 (ir_vl1 (IRScalar.bool_ ans2)))) : Eq IRConfig (ir_steps (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add ir_d1 c2) ir_d5) ir_d1) c1) ir_d8) ir_lz_module (IRConfig.running (ir_lz_mach0 mem a na dests rest))) (ir_ret_to dests rest mem na (ir_vl1 (IRScalar.bool_ ans2))) := Eq.subst (IROption IRMemSlot) (fun (o : (IROption IRMemSlot)) => Eq IRConfig (ir_steps (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add ir_d1 c2) ir_d5) ir_d1) c1) ir_d7) ir_lz_module (ir_lz_after_load mem a na dests rest o)) (ir_ret_to dests rest mem na (ir_vl1 (IRScalar.bool_ ans2)))) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true)) (ir_mem_lookup mem a) (Eq.symm (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true)) h) (Eq.trans IRConfig (ir_steps (Nat.add (Nat.add (Nat.add (Nat.add ir_d1 c2) ir_d5) ir_d1) c1) ir_lz_module (ir_steps ir_d7 ir_lz_module (ir_lz_after_load mem a na dests rest (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true))))) (ir_steps (Nat.add (Nat.add (Nat.add ir_d1 c2) ir_d5) ir_d1) ir_lz_module (ir_steps c1 ir_lz_module (ir_steps ir_d7 ir_lz_module (ir_lz_after_load mem a na dests rest (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true)))))) (ir_ret_to dests rest mem na (ir_vl1 (IRScalar.bool_ ans2))) (ir_steps_add ir_lz_module (Nat.add (Nat.add (Nat.add ir_d1 c2) ir_d5) ir_d1) c1 (ir_steps ir_d7 ir_lz_module (ir_lz_after_load mem a na dests rest (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true))))) (Eq.subst IRConfig (fun (k : IRConfig) => Eq IRConfig (ir_steps (Nat.add (Nat.add (Nat.add ir_d1 c2) ir_d5) ir_d1) ir_lz_module k) (ir_ret_to dests rest mem na (ir_vl1 (IRScalar.bool_ ans2)))) (ir_ret_to (ir_nl1 ir_d8) (ir_frames_tail (ir_config_frames (ir_steps ir_d7 ir_lz_module (ir_lz_after_load mem a na dests rest (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true)))))) mem na (ir_vl1 (IRScalar.bool_ Bool.true))) (ir_steps c1 ir_lz_module (ir_steps ir_d7 ir_lz_module (ir_lz_after_load mem a na dests rest (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true))))) (Eq.symm IRConfig (ir_steps c1 ir_lz_module (ir_steps ir_d7 ir_lz_module (ir_lz_after_load mem a na dests rest (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true))))) (ir_ret_to (ir_nl1 ir_d8) (ir_frames_tail (ir_config_frames (ir_steps ir_d7 ir_lz_module (ir_lz_after_load mem a na dests rest (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true)))))) mem na (ir_vl1 (IRScalar.bool_ Bool.true))) (ih1 na (ir_nl1 ir_d8) (ir_frames_tail (ir_config_frames (ir_steps ir_d7 ir_lz_module (ir_lz_after_load mem a na dests rest (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true)))))))) (Eq.trans IRConfig (ir_steps (Nat.add (Nat.add (Nat.add ir_d1 c2) ir_d5) ir_d1) ir_lz_module (ir_ret_to (ir_nl1 ir_d8) (ir_frames_tail (ir_config_frames (ir_steps ir_d7 ir_lz_module (ir_lz_after_load mem a na dests rest (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true)))))) mem na (ir_vl1 (IRScalar.bool_ Bool.true)))) (ir_steps ir_d1 ir_lz_module (ir_steps c2 ir_lz_module (ir_steps ir_d6 ir_lz_module (ir_ret_to (ir_nl1 ir_d8) (ir_frames_tail (ir_config_frames (ir_steps ir_d7 ir_lz_module (ir_lz_after_load mem a na dests rest (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true)))))) mem na (ir_vl1 (IRScalar.bool_ Bool.true)))))) (ir_ret_to dests rest mem na (ir_vl1 (IRScalar.bool_ ans2))) (ir_steps_add ir_lz_module ir_d1 c2 (ir_steps ir_d6 ir_lz_module (ir_ret_to (ir_nl1 ir_d8) (ir_frames_tail (ir_config_frames (ir_steps ir_d7 ir_lz_module (ir_lz_after_load mem a na dests rest (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true)))))) mem na (ir_vl1 (IRScalar.bool_ Bool.true))))) (Eq.subst IRConfig (fun (k : IRConfig) => Eq IRConfig (ir_steps ir_d1 ir_lz_module k) (ir_ret_to dests rest mem na (ir_vl1 (IRScalar.bool_ ans2)))) (ir_ret_to (ir_nl1 ir_d12) (ir_frames_tail (ir_config_frames (ir_steps ir_d6 ir_lz_module (ir_ret_to (ir_nl1 ir_d8) (ir_frames_tail (ir_config_frames (ir_steps ir_d7 ir_lz_module (ir_lz_after_load mem a na dests rest (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true)))))) mem na (ir_vl1 (IRScalar.bool_ Bool.true)))))) mem na (ir_vl1 (IRScalar.bool_ ans2))) (ir_steps c2 ir_lz_module (ir_steps ir_d6 ir_lz_module (ir_ret_to (ir_nl1 ir_d8) (ir_frames_tail (ir_config_frames (ir_steps ir_d7 ir_lz_module (ir_lz_after_load mem a na dests rest (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true)))))) mem na (ir_vl1 (IRScalar.bool_ Bool.true))))) (Eq.symm IRConfig (ir_steps c2 ir_lz_module (ir_steps ir_d6 ir_lz_module (ir_ret_to (ir_nl1 ir_d8) (ir_frames_tail (ir_config_frames (ir_steps ir_d7 ir_lz_module (ir_lz_after_load mem a na dests rest (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true)))))) mem na (ir_vl1 (IRScalar.bool_ Bool.true))))) (ir_ret_to (ir_nl1 ir_d12) (ir_frames_tail (ir_config_frames (ir_steps ir_d6 ir_lz_module (ir_ret_to (ir_nl1 ir_d8) (ir_frames_tail (ir_config_frames (ir_steps ir_d7 ir_lz_module (ir_lz_after_load mem a na dests rest (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true)))))) mem na (ir_vl1 (IRScalar.bool_ Bool.true)))))) mem na (ir_vl1 (IRScalar.bool_ ans2))) (ih2 na (ir_nl1 ir_d12) (ir_frames_tail (ir_config_frames (ir_steps ir_d6 ir_lz_module (ir_ret_to (ir_nl1 ir_d8) (ir_frames_tail (ir_config_frames (ir_steps ir_d7 ir_lz_module (ir_lz_after_load mem a na dests rest (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true)))))) mem na (ir_vl1 (IRScalar.bool_ Bool.true)))))))) (Eq.refl IRConfig (ir_ret_to dests rest mem na (ir_vl1 (IRScalar.bool_ ans2))))))))";

const SRC_MAX_FALSE_SEG: &str = "def ir_lz_max_false_seg (mem : IRList IRMemSlot) (a : Nat) (b1 : Nat) (b2 : Nat) (c1 : Nat) (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame) (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true))) (ih1 : forall (na2 : Nat) (d2 : IRList Nat) (r2 : IRList IRFrame), Eq IRConfig (ir_steps c1 ir_lz_module (IRConfig.running (ir_lz_mach0 mem b1 na2 d2 r2))) (ir_ret_to d2 r2 mem na2 (ir_vl1 (IRScalar.bool_ Bool.false)))) : Eq IRConfig (ir_steps (Nat.add (Nat.add ir_d3 c1) ir_d8) ir_lz_module (IRConfig.running (ir_lz_mach0 mem a na dests rest))) (ir_ret_to dests rest mem na (ir_vl1 (IRScalar.bool_ Bool.false))) := Eq.subst (IROption IRMemSlot) (fun (o : (IROption IRMemSlot)) => Eq IRConfig (ir_steps (Nat.add (Nat.add ir_d3 c1) ir_d7) ir_lz_module (ir_lz_after_load mem a na dests rest o)) (ir_ret_to dests rest mem na (ir_vl1 (IRScalar.bool_ Bool.false)))) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true)) (ir_mem_lookup mem a) (Eq.symm (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true)) h) (Eq.trans IRConfig (ir_steps (Nat.add ir_d3 c1) ir_lz_module (ir_steps ir_d7 ir_lz_module (ir_lz_after_load mem a na dests rest (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true))))) (ir_steps ir_d3 ir_lz_module (ir_steps c1 ir_lz_module (ir_steps ir_d7 ir_lz_module (ir_lz_after_load mem a na dests rest (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true)))))) (ir_ret_to dests rest mem na (ir_vl1 (IRScalar.bool_ Bool.false))) (ir_steps_add ir_lz_module ir_d3 c1 (ir_steps ir_d7 ir_lz_module (ir_lz_after_load mem a na dests rest (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true))))) (Eq.subst IRConfig (fun (k : IRConfig) => Eq IRConfig (ir_steps ir_d3 ir_lz_module k) (ir_ret_to dests rest mem na (ir_vl1 (IRScalar.bool_ Bool.false)))) (ir_ret_to (ir_nl1 ir_d8) (ir_frames_tail (ir_config_frames (ir_steps ir_d7 ir_lz_module (ir_lz_after_load mem a na dests rest (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true)))))) mem na (ir_vl1 (IRScalar.bool_ Bool.false))) (ir_steps c1 ir_lz_module (ir_steps ir_d7 ir_lz_module (ir_lz_after_load mem a na dests rest (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true))))) (Eq.symm IRConfig (ir_steps c1 ir_lz_module (ir_steps ir_d7 ir_lz_module (ir_lz_after_load mem a na dests rest (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true))))) (ir_ret_to (ir_nl1 ir_d8) (ir_frames_tail (ir_config_frames (ir_steps ir_d7 ir_lz_module (ir_lz_after_load mem a na dests rest (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true)))))) mem na (ir_vl1 (IRScalar.bool_ Bool.false))) (ih1 na (ir_nl1 ir_d8) (ir_frames_tail (ir_config_frames (ir_steps ir_d7 ir_lz_module (ir_lz_after_load mem a na dests rest (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d2 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true)))))))) (Eq.refl IRConfig (ir_ret_to dests rest mem na (ir_vl1 (IRScalar.bool_ Bool.false))))))";

const SRC_IMAX_SEG: &str = "def ir_lz_imax_seg (mem : IRList IRMemSlot) (a : Nat) (b1 : Nat) (b2 : Nat) (c2 : Nat) (ans2 : Bool) (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame) (h : Eq (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d3 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true))) (ih1 : forall (na2 : Nat) (d2 : IRList Nat) (r2 : IRList IRFrame), Eq IRConfig (ir_steps c2 ir_lz_module (IRConfig.running (ir_lz_mach0 mem b2 na2 d2 r2))) (ir_ret_to d2 r2 mem na2 (ir_vl1 (IRScalar.bool_ ans2)))) : Eq IRConfig (ir_steps (Nat.add (Nat.add ir_d1 c2) ir_d8) ir_lz_module (IRConfig.running (ir_lz_mach0 mem a na dests rest))) (ir_ret_to dests rest mem na (ir_vl1 (IRScalar.bool_ ans2))) := Eq.subst (IROption IRMemSlot) (fun (o : (IROption IRMemSlot)) => Eq IRConfig (ir_steps (Nat.add (Nat.add ir_d1 c2) ir_d7) ir_lz_module (ir_lz_after_load mem a na dests rest o)) (ir_ret_to dests rest mem na (ir_vl1 (IRScalar.bool_ ans2)))) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d3 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true)) (ir_mem_lookup mem a) (Eq.symm (IROption IRMemSlot) (ir_mem_lookup mem a) (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d3 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true)) h) (Eq.trans IRConfig (ir_steps (Nat.add ir_d1 c2) ir_lz_module (ir_steps ir_d7 ir_lz_module (ir_lz_after_load mem a na dests rest (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d3 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true))))) (ir_steps ir_d1 ir_lz_module (ir_steps c2 ir_lz_module (ir_steps ir_d7 ir_lz_module (ir_lz_after_load mem a na dests rest (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d3 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true)))))) (ir_ret_to dests rest mem na (ir_vl1 (IRScalar.bool_ ans2))) (ir_steps_add ir_lz_module ir_d1 c2 (ir_steps ir_d7 ir_lz_module (ir_lz_after_load mem a na dests rest (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d3 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true))))) (Eq.subst IRConfig (fun (k : IRConfig) => Eq IRConfig (ir_steps ir_d1 ir_lz_module k) (ir_ret_to dests rest mem na (ir_vl1 (IRScalar.bool_ ans2)))) (ir_ret_to (ir_nl1 ir_d16) (ir_frames_tail (ir_config_frames (ir_steps ir_d7 ir_lz_module (ir_lz_after_load mem a na dests rest (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d3 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true)))))) mem na (ir_vl1 (IRScalar.bool_ ans2))) (ir_steps c2 ir_lz_module (ir_steps ir_d7 ir_lz_module (ir_lz_after_load mem a na dests rest (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d3 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true))))) (Eq.symm IRConfig (ir_steps c2 ir_lz_module (ir_steps ir_d7 ir_lz_module (ir_lz_after_load mem a na dests rest (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d3 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true))))) (ir_ret_to (ir_nl1 ir_d16) (ir_frames_tail (ir_config_frames (ir_steps ir_d7 ir_lz_module (ir_lz_after_load mem a na dests rest (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d3 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true)))))) mem na (ir_vl1 (IRScalar.bool_ ans2))) (ih1 na (ir_nl1 ir_d16) (ir_frames_tail (ir_config_frames (ir_steps ir_d7 ir_lz_module (ir_lz_after_load mem a na dests rest (IROption.some IRMemSlot (IRMemSlot.mk a (ir_var ir_d3 (ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))) Bool.true)))))))) (Eq.refl IRConfig (ir_ret_to dests rest mem na (ir_vl1 (IRScalar.bool_ ans2))))))";

impl Specification {
    /// The activation lemma's leaf arms.
    pub(super) fn add_eval_ir_activation(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(SRC_MACH0, "ir_lz_mach0: the machine one activation of Level::is_zero starts from -- a fresh frame for function 0 at block 0, its single parameter bound to a pointer at address a, stacked on WHATEVER the caller had. \
\
mem, na, dests and rest all stay universally quantified. That is deliberate: the recursive arms of the activation lemma instantiate rest with their own frame, so a lemma that pinned the caller could not feed its own induction hypothesis. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_CONFIG_FRAMES, "ir_config_frames: the frame stack of a configuration, empty once halted. Paired with ir_frames_tail this is how a recursive arm NAMES the caller it just pushed onto, without anyone having to write that frame out. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_FRAMES_TAIL, "ir_frames_tail: drop the top frame. \
\
Together with ir_config_frames this solves the problem that would otherwise dominate these proofs. To apply the child's induction hypothesis one must supply the frame stack the callee sits on -- and that stack is the caller mid-instruction, with four SSA ids already bound. Writing it out is possible and miserable. Writing it as ir_frames_tail (ir_config_frames (the 8-step config)) is exact, short, and cannot drift from what the machine actually built. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_AFTER_LOAD, "ir_lz_after_load: the entry block's first step, as a function of the LOADED SLOT. Naming it keeps the arm proofs legible and gives Eq.subst the o-shaped hole it needs. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(&src_step_load(), "ir_lz_step_load: one step of the entry block, written so the heap lookup is VISIBLE. \
\
Eq.refl proves it, and that is exactly the point -- the two sides are already definitionally equal, so this declaration adds no mathematical content. What it adds is SYNTAX. The activation goal never mentions ir_mem_lookup mem a, so Eq.subst on the representation hypothesis has nothing to rewrite and produces a constant motive. Restating the step with the lookup occurring literally is what turns the hypothesis into something that can fire. \
\
Everything downstream of the load computes, because the cell the hypothesis supplies is concrete. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(&activation("ir_lz_activation_zero", "", "(ir_var ir_d0 ir_sp0)", "true"), "ir_lz_activation_zero: an activation on a heap-encoded Level.zero runs 5 steps and hands the caller back true. \
\
Arbitrary heap, arbitrary caller. ir_ret_to is stuck on the opaque rest -- but stuck IDENTICALLY on both sides, so the lemma pins where the machine goes without knowing who called it. \
\
Eq.symm is needed because Eq.subst transports FORWARDS along the equation and the proof lives on the concrete side while the goal sits on the stuck side. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(&activation("ir_lz_activation_succ", "(b : Nat) ", "(ir_var ir_d1 (ir_sp1 (IRScalar.ptr_ b)))", "false"), "ir_lz_activation_succ: Succ is a LEAF, not a recursive case -- Level::is_zero answers false without following the edge. \
\
Hence cost 5, the same as zero, and hence the child address b is quantified over and then never mentioned again: the machine binds the field and ignores it. A semantics that wrongly recursed would need b to point somewhere, and this lemma -- which constrains nothing about b, not even that it is allocated -- would stop being provable. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(&activation("ir_lz_activation_param", "(w : IRScalar) ", "(ir_var ir_d4 (ir_sp1 w))", "false"), "ir_lz_activation_param: Param is the other leaf, and its payload w is an ARBITRARY scalar. \
\
That freedom is A2's, carried through faithfully: EncodesLevelArc's param arm constrains the payload not at all, so one heap encodes Level.param nm for every nm. The activation's cost and answer are independent of it, which is why the non-functionality is harmless. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_MAX_TRUE_SEG, "ir_lz_max_true_seg: the Max arm's RECURSIVE edge, and the deepest machine fact in the crystal so far. \
\
When the left operand IS zero the CondBr takes the then-edge into b4, which derefs the second child, asserts it non-null, calls again, and returns the callee's answer as the whole Max's. So the segment is 8 + c1 + 1 + 5 + c2 + 1, TWO nested activations deep, and both induction hypotheses are consumed -- ih1 to learn the left side returned true, ih2 to learn what the right side returned. \
\
The cost is written as a right-nested Nat.add whose literal segments sit in the SECOND argument on purpose. Nat.add recurses there, so a literal segment peels definitionally and needs no lemma; only the two VARIABLE segments c1 and c2 go through ir_steps_add. That is why this proof has exactly two applications of it rather than six. \
\
Neither caller frame is ever written out. The stack the first callee sits on is named ir_frames_tail (ir_config_frames <the 8-step config>), and the second likewise -- exact by construction, and incapable of drifting from what the machine built. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_MAX_FALSE_SEG, "ir_lz_max_false_seg: the Max arm's SHORT-CIRCUIT edge. If the left operand is not zero, block b3's CondBr jumps to b2 and the right operand is never evaluated -- so the cost is 8 + c1 + 3 and only ONE induction hypothesis appears. A proof that consumed ih2 here would be describing a machine that does not short-circuit. \
\
The && in l1.is_zero() && l2.is_zero() compiles to that CondBr, not to a BinOp::And, and this lemma is where that distinction becomes a theorem. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_IMAX_SEG, "ir_lz_imax_seg: IMax(_, l2) => l2.is_zero(). The first operand is bound in the heap cell and NEVER READ -- impredicative collapse, level/mod.rs:529. \
\
b1 appears in the hypothesis and nowhere else in the proof, and the lemma constrains nothing about it: not that it is allocated, not that it encodes anything. That asymmetry is the semantics, made checkable. DerivedProved, zero axiom_deps.")?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The caller's state must stay universally quantified. If `rest` or
    /// `dests` ever became concrete, the recursive arms could not instantiate
    /// them with their own frame and the lemma would not compose.
    #[test]
    fn test_caller_state_is_universally_quantified() {
        for src in [SRC_MACH0, &src_step_load()] {
            assert!(src.contains("(dests : IRList Nat) (rest : IRList IRFrame)"));
        }
        let z = activation("z", "", "(ir_var ir_d0 ir_sp0)", "true");
        assert!(
            z.contains("(ir_ret_to dests rest mem na"),
            "the target must be the caller's resumption, not a halt"
        );
    }

    /// `ir_lz_step_load` earns its place by SHAPE, not by content — it must stay
    /// an `Eq.refl` whose right-hand side mentions the lookup literally.
    #[test]
    fn test_step_load_exposes_the_lookup_syntactically() {
        let s = src_step_load();
        assert!(s.contains("(ir_load_slot (ir_mem_lookup mem a))"));
        assert!(s.contains(":= Eq.refl IRConfig"));
    }

    /// Every arm rewrites via the motive that abstracts the lookup result, and
    /// every arm needs `Eq.symm` because the proof is on the concrete side.
    #[test]
    fn test_arms_rewrite_through_the_abstracted_motive() {
        for a in [
            activation("z", "", "(ir_var ir_d0 ir_sp0)", "true"),
            activation(
                "s",
                "(b : Nat) ",
                "(ir_var ir_d1 (ir_sp1 (IRScalar.ptr_ b)))",
                "false",
            ),
            activation("p", "(w : IRScalar) ", "(ir_var ir_d4 (ir_sp1 w))", "false"),
        ] {
            assert!(
                a.contains("(fun (o : (IROption IRMemSlot)) =>"),
                "motive abstracts o"
            );
            assert!(a.contains("(ir_load_slot o)"), "and o replaces the lookup");
            assert!(
                a.contains("Eq.symm"),
                "transport runs against the hypothesis"
            );
        }
    }

    /// All three leaves cost 5. `succ` costing anything else would mean the
    /// machine followed the edge, which `Level::is_zero` does not do.
    #[test]
    fn test_all_three_leaves_run_five_steps() {
        for a in [
            activation("z", "", "(ir_var ir_d0 ir_sp0)", "true"),
            activation(
                "s",
                "(b : Nat) ",
                "(ir_var ir_d1 (ir_sp1 (IRScalar.ptr_ b)))",
                "false",
            ),
            activation("p", "(w : IRScalar) ", "(ir_var ir_d4 (ir_sp1 w))", "false"),
        ] {
            assert!(a.contains("ir_steps ir_d5 ir_lz_module"));
            assert!(
                a.contains("ir_steps ir_d4 ir_lz_module"),
                "four remain after the load"
            );
        }
    }

    /// `succ` binds a child address and must never use it; `param` binds a
    /// payload and must never use it. Both are claims about the semantics.
    #[test]
    fn test_leaf_children_are_bound_but_unused() {
        let s = activation(
            "s",
            "(b : Nat) ",
            "(ir_var ir_d1 (ir_sp1 (IRScalar.ptr_ b)))",
            "false",
        );
        // The cell is written three times per arm — in the hypothesis type, as
        // `Eq.subst`'s target, and inside `Eq.symm`. The child must occur in
        // exactly those copies and nowhere else: the machine binds the field
        // and never follows it. Compare against the cell count rather than a
        // literal, so the invariant survives a change in proof shape.
        let cell_succ = some("(ir_var ir_d1 (ir_sp1 (IRScalar.ptr_ b)))");
        assert_eq!(
            s.matches("IRScalar.ptr_ b").count(),
            s.matches(cell_succ.as_str()).count(),
            "b must occur only inside the cell copies"
        );
        let p = activation("p", "(w : IRScalar) ", "(ir_var ir_d4 (ir_sp1 w))", "false");
        let cell_param = some("(ir_var ir_d4 (ir_sp1 w))");
        assert_eq!(
            p.matches("ir_sp1 w").count(),
            p.matches(cell_param.as_str()).count(),
            "w likewise -- A2 leaves the param payload free and the answer ignores it"
        );
    }

    #[test]
    fn test_sources_balanced_ascii() {
        let owned = [
            src_step_load(),
            activation("z", "", "(ir_var ir_d0 ir_sp0)", "true"),
            activation(
                "s",
                "(b : Nat) ",
                "(ir_var ir_d1 (ir_sp1 (IRScalar.ptr_ b)))",
                "false",
            ),
            activation("p", "(w : IRScalar) ", "(ir_var ir_d4 (ir_sp1 w))", "false"),
        ];
        for src in std::iter::once(SRC_MACH0).chain(owned.iter().map(String::as_str)) {
            assert!(src.is_ascii(), "spec sources stay ASCII");
            assert_eq!(
                src.matches('(').count(),
                src.matches(')').count(),
                "unbalanced parens in: {}",
                &src[..50.min(src.len())]
            );
        }
    }
}
