#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Mint the 33 proof terms in `eval_ir_slot_lemmas.rs`.

WHY THIS EXISTS. That file carries ~16k characters of proof term across its
string constants -- the `alloca` / `store` / `load` / `ret` return slot, closed
at an ABSTRACT heap and an ABSTRACT allocation counter, the shape every callee
body the crystal's A0 closure still needs (`Option::as_deref`, `Option::expect`,
`<Arc<T>>::deref`) opens with. They were not typed; they were emitted from the
Phase-B kernel probe (28/28 candidates kernel-checked) by a script that lived
OUTSIDE the repo, so nothing in-tree could re-derive the file or notice a
hand-edit. That is the class `scripts/gen_lzb_activation.py` closes for the four
`ir_lzb_*` activation terms one lane over; this closes it here, same contract.
The terms are built STRUCTURALLY, not transcribed: `ir_slot_seg`'s splicing
chain and `ir_slot_cost_is_4`'s arithmetic pin come from the same four-element
`segments()` list, so a mis-costed segment cannot pass one and fail the other.

THE PROOF SHAPE, ONCE. `alloca` conses its fresh cell at the HEAD of memory, so
the store's liveness read and the load's read are both lookups at the head --
and a head lookup resolves by `ir_nat_eqb na na = true`, a Nat induction, not a
walk over an unknown heap. Everything above is transport: a shape witness
(`Eq.refl`) restates the machine's own step with the stuck `ir_mem_lookup` /
`ir_mem_update` occurring SYNTACTICALLY, then `Eq.subst`+`Eq.symm` rewrites it.

WHAT --check SAYS. That the committed constants, the `SLOT_LEMMA_NAMES` list and
the `DECLS` registration ORDER are what this script emits today. NOT that the
terms are true -- the kernel says that, in the spec build, and the acceptance
gate is `crates/clean-verify/tests/eval_ir/slot_lemmas.rs`. It reads no Rust
source for a verdict beyond anchored `const NAME: &str = "...";` declarations
and two anchored lists; one that stops matching is a refusal, never a zero.

USAGE: --check | --self-test | --print SRC_ACTIVATION | --emit (then rustfmt)."""

from __future__ import annotations

import argparse
import hashlib
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
SLOT_RS = REPO / "crates/clean-verify/src/spec/core_spec/eval_ir_slot_lemmas.rs"

# Every declared name is reached through `N(key)`, never spelled inline, so
# `--self-test` can re-emit the family under the probe's own `ir_probe_` names
# and hold it against digests of terms a kernel accepted.
NAMES: dict[str, str] = {}


def N(key: str) -> str:
    return NAMES[key]


SLOT = "(IROption IRMemSlot)"
MEMT = "(IRList IRMemSlot)"
TY = "(IRTy.enum_ ir_d0)"
BINDERS = "(mem : IRList IRMemSlot) (v : IRScalar) (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame)"
ARGS = "mem v na dests rest"
FRAME0 = "(IRFrame.mk ir_d0 ir_d0 Nat.zero (ir_bind_params (ir_nl1 ir_d0) (ir_vl1 v) (IRList.nil IRBinding)) dests)"
FRAME1 = f"(ir_frame_bind {FRAME0} (ir_nl1 ir_d1) (IRScalar.ptr_ na))"
FRAME2 = f"(ir_frame_advance {FRAME1})"
MEM1 = "(IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) mem)"
MEM2 = "(IRList.cons IRMemSlot (IRMemSlot.mk na v Bool.true) mem)"
CELL0 = "(IRMemSlot.mk na IRScalar.undef_ Bool.true)"

# `ir_load_slot` dispatches on the value's CONSTRUCTOR, so `ir_slot_load_seg`
# and above are stated at `v := IRScalar.int_ n` for an abstract `n` rather than
# at a fully opaque scalar -- a real boundary, named rather than discovered.
NB = "(mem : IRList IRMemSlot) (n : Nat) (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame)"
NARGS = "mem (IRScalar.int_ n) na dests rest"
NMEM2 = "(IRList.cons IRMemSlot (IRMemSlot.mk na (IRScalar.int_ n) Bool.true) mem)"
NCELL1 = "(IRMemSlot.mk na (IRScalar.int_ n) Bool.true)"
TARGET = f"(ir_ret_to dests rest {NMEM2} (Nat.succ na) (ir_vl1 (IRScalar.int_ n)))"


def symm(ty: str, x: str, y: str, h: str) -> str:
    return f"(Eq.symm {ty} {x} {y} {h})"


def steps(n: str, c: str) -> str:
    return f"(ir_steps {n} {N('module')} {c})"


AGG = "(IRScalar.aggv fs)"
VAL = f"(IRStepResult.value {AGG})"
VTY = "(ir_view_ty encs (ir_enc_len encs))"
LVIEW = "(ir_bind_result s rs (ir_load_view (ir_mod_encs m) t (ir_load_eval s (ir_getd s p))))"


def _opt_rec(motive_body: str, none_case: str, some_case: str, scrut: str) -> str:
    """`IROption.rec` over an IREnc option — the table lookup, which is stuck."""
    return (
        f"IROption.rec IREnc (fun (o0 : IROption IREnc) => {motive_body}) "
        f"{none_case} {some_case} {scrut}"
    )


def exec_load_is_view() -> str:
    return (
        f"def {N('exec_load_is_view')} (m : IRModule) (t : IRTy) (p : Nat) (vol : Bool) "
        f"(rs : IRList Nat) (s : IRMachine) : Eq IRConfig "
        f"(ir_exec m (IRInst.load t p vol) rs s) {LVIEW} := Eq.refl IRConfig {LVIEW}"
    )


def view_word_agg() -> str:
    goal = f"Eq IRScalar (ir_view_word rec_ e0 {AGG}) {AGG}"
    return (
        f"def {N('view_word_agg')} (rec_ : IRTy -> IRScalar -> IRScalar) (e : IREnc) "
        f"(fs : IRScalar) : Eq IRScalar (ir_view_word rec_ e {AGG}) {AGG} := "
        f"IREnc.rec (fun (e0 : IREnc) => {goal}) "
        f"(fun (k : Nat) (no : Nat) (so : Nat) (pt : IRTy) => Eq.refl IRScalar {AGG}) "
        f"(fun (k : Nat) (i : Nat) (c : Nat) (pt : IRTy) => Eq.refl IRScalar {AGG}) e"
    )


def _view_body(o: str) -> str:
    return (
        f"IROption.rec IREnc (fun (_ : IROption IREnc) => IRScalar) {AGG} "
        f"(fun (e : IREnc) => ir_view_word ih e {AGG}) {o}"
    )


def view_opt_agg() -> str:
    return (
        f"def {N('view_opt_agg')} (ih : IRTy -> IRScalar -> IRScalar) (fs : IRScalar) "
        f"(o : IROption IREnc) : Eq IRScalar ({_view_body('o')}) {AGG} := "
        + _opt_rec(
            f"Eq IRScalar ({_view_body('o0')}) {AGG}",
            f"(Eq.refl IRScalar {AGG})",
            f"(fun (e : IREnc) => {N('view_word_agg')} ih e fs)",
            "o",
        )
    )


def view_ty_agg() -> str:
    goal = f"forall (t : IRTy), Eq IRScalar (ir_view_ty encs k t {AGG}) {AGG}"
    return (
        f"def {N('view_ty_agg')} (encs : IRList IREnc) (fs : IRScalar) : "
        f"forall (n : Nat) (t : IRTy), Eq IRScalar (ir_view_ty encs n t {AGG}) {AGG} := "
        f"Nat.rec (fun (k : Nat) => {goal}) "
        f"(fun (t : IRTy) => Eq.refl IRScalar {AGG}) "
        f"(fun (k : Nat) (_ih : {goal}) (t : IRTy) => "
        f"{N('view_opt_agg')} (ir_view_ty encs k) fs (ir_enc_find encs t))"
    )


def _lview_body(o: str) -> str:
    return (
        f"IROption.rec IREnc (fun (_ : IROption IREnc) => IRStepResult) {VAL} "
        f"(fun (e : IREnc) => ir_view_result encs e {VAL}) {o}"
    )


def load_view_opt_agg() -> str:
    word = f"(ir_view_word {VTY} e {AGG})"
    step = f"({N('view_word_agg')} {VTY} e fs)"
    cong = (
        "(fun (e : IREnc) => Eq.subst IRScalar (fun (x : IRScalar) => Eq IRStepResult "
        f"(IRStepResult.value x) {VAL}) {AGG} {word} "
        + symm("IRScalar", word, AGG, step)
        + f" (Eq.refl IRStepResult {VAL}))"
    )
    return (
        f"def {N('load_view_opt_agg')} (encs : IRList IREnc) (fs : IRScalar) "
        f"(o : IROption IREnc) : Eq IRStepResult ({_lview_body('o')}) {VAL} := "
        + _opt_rec(
            f"Eq IRStepResult ({_lview_body('o0')}) {VAL}",
            f"(Eq.refl IRStepResult {VAL})",
            cong,
            "o",
        )
    )


def load_view_agg() -> str:
    return (
        f"def {N('load_view_agg')} (encs : IRList IREnc) (t : IRTy) (fs : IRScalar) : "
        f"Eq IRStepResult (ir_load_view encs t {VAL}) {VAL} := "
        f"{N('load_view_opt_agg')} encs fs (ir_enc_find encs t)"
    )


def exec_load_agg() -> str:
    tgt = f"(ir_bind_result s rs {VAL})"
    viewed = f"(ir_load_view (ir_mod_encs m) t {VAL})"
    read = "(ir_load_eval s (ir_getd s p))"
    inner = (
        "(Eq.subst IRStepResult (fun (r : IRStepResult) => Eq IRConfig "
        f"(ir_bind_result s rs r) {tgt}) {VAL} {viewed} "
        + symm("IRStepResult", viewed, VAL, f"({N('load_view_agg')} (ir_mod_encs m) t fs)")
        + f" (Eq.refl IRConfig {tgt}))"
    )
    return (
        f"def {N('exec_load_agg')} (m : IRModule) (t : IRTy) (p : Nat) (vol : Bool) "
        f"(rs : IRList Nat) (s : IRMachine) (fs : IRScalar) "
        f"(h : Eq IRStepResult {read} {VAL}) : Eq IRConfig "
        f"(ir_exec m (IRInst.load t p vol) rs s) {tgt} := "
        "Eq.subst IRStepResult (fun (r : IRStepResult) => Eq IRConfig "
        f"(ir_bind_result s rs (ir_load_view (ir_mod_encs m) t r)) {tgt}) "
        f"{VAL} {read} "
        + symm("IRStepResult", read, VAL, "h")
        + f" {inner}"
    )


def nat_sub_self() -> str:
    return (
        f"def {N('nat_sub_self')} (k : Nat) : Eq Nat (Nat.sub k k) Nat.zero := "
        "Nat.rec (fun (m : Nat) => Eq Nat (Nat.sub m m) Nat.zero) (Eq.refl Nat Nat.zero) "
        "(fun (m : Nat) (ih : Eq Nat (Nat.sub m m) Nat.zero) => "
        "Eq.trans Nat (Nat.sub (Nat.succ m) (Nat.succ m)) (Nat.sub m m) Nat.zero "
        "(ir_nat_sub_succ_succ m m) ih) k"
    )


def nat_eqb_walk_refl() -> str:
    """`ir_nat_eqb_walk n n = true`, by induction, with NO subtraction anywhere.

    The successor minor is the induction hypothesis UNCHANGED -- `ih` itself, not
    a rewrite of it -- because `ir_nat_eqb_walk (succ k) (succ k)` reduces to
    `ir_nat_eqb_walk k k` by two iota steps and delta, in both kernels. That is
    the whole content of this lemma and the reason it exists: see
    `nat_eqb_refl` below for what it replaced and why."""
    return (
        f"def {N('nat_eqb_walk_refl')} (n : Nat) : Eq Bool (ir_nat_eqb_walk n n) Bool.true := "
        "Nat.rec (fun (k : Nat) => Eq Bool (ir_nat_eqb_walk k k) Bool.true) (Eq.refl Bool Bool.true) "
        "(fun (k : Nat) (ih : Eq Bool (ir_nat_eqb_walk k k) Bool.true) => ih) n"
    )


def nat_eqb_refl() -> str:
    """`ir_nat_eqb n n = true`, routed through the unary WALK rather than through
    `ir_nat_sub_self`.

    THE OLD PROOF WAS RIGHT IN CLEAN AND UNCHECKABLE IN LEAN, and the reason is
    worth stating because it will happen again. It closed the successor case with
    `ir_eq_cong ... (Nat.sub k k) Nat.zero (ir_nat_sub_self k)`, rewriting under
    the `Bool.rec` that `ir_nat_eqb (succ k) (succ k)` peels to. But the exporter
    installs a REPLAY GUARD over reflected comparisons: it emits
    `ReplayBridge.sub` -- `casesOn b a (fun _ => casesOn a 0 (fun _ => Nat.sub a
    b))` -- in place of `Nat.sub` inside `ir_nat_sub_eqb`'s body, so that Lean
    cannot walk a subtraction unary at a closed operand. It does NOT rewrite
    `ir_nat_sub_self`, which keeps speaking about the raw `Nat.sub`. At a
    SYMBOLIC `k` the guarded form is stuck at its own `casesOn` and is not defeq
    to `Nat.sub k k`, so the rewrite landed on a term the goal no longer
    contained and Lean reported a type mismatch on a proof Clean accepts
    (`gate::leancross`, 2026-09-15, the first of its two causes).

    `ir_nat_eqb_walk` contains no subtraction, so the guard never touches it, and
    `ir_nat_eqb_walk_eq` -- already proved, already re-checked by Lean -- carries
    us the rest of the way. The fix is therefore to stop depending on the shape
    of a definition the exporter is entitled to rewrite."""
    return (
        f"def {N('nat_eqb_refl')} (n : Nat) : Eq Bool (ir_nat_eqb n n) Bool.true := "
        "Eq.trans Bool (ir_nat_eqb n n) (ir_nat_eqb_walk n n) Bool.true "
        f"(ir_nat_eqb_walk_eq n n) ({N('nat_eqb_walk_refl')} n)"
    )


def mem_lookup_head() -> str:
    return (
        f"def {N('mem_lookup_head')} (a : Nat) (v : IRScalar) (live : Bool) (m : IRList IRMemSlot) : "
        "Eq (IROption IRMemSlot) (ir_mem_lookup (IRList.cons IRMemSlot (IRMemSlot.mk a v live) m) a) "
        "(IROption.some IRMemSlot (IRMemSlot.mk a v live)) := ir_eq_cong Bool (IROption IRMemSlot) "
        "(fun (b : Bool) => Bool.rec (fun (_ : Bool) => IROption IRMemSlot) (ir_mem_lookup m a) "
        "(IROption.some IRMemSlot (IRMemSlot.mk a v live)) b) "
        f"(ir_nat_eqb a a) Bool.true ({N('nat_eqb_refl')} a)"
    )


def mem_update_head() -> str:
    return (
        f"def {N('mem_update_head')} (a : Nat) (v0 : IRScalar) (live : Bool) (m : IRList IRMemSlot) (v : IRScalar) : "
        "Eq (IRList IRMemSlot) (ir_mem_update (IRList.cons IRMemSlot (IRMemSlot.mk a v0 live) m) a v) "
        "(IRList.cons IRMemSlot (IRMemSlot.mk a v live) m) := ir_eq_cong Bool (IRList IRMemSlot) "
        "(fun (b : Bool) => Bool.rec (fun (_ : Bool) => IRList IRMemSlot) "
        "(IRList.cons IRMemSlot (IRMemSlot.mk a v0 live) (ir_mem_update m a v)) "
        "(IRList.cons IRMemSlot (IRMemSlot.mk a v live) m) b) "
        f"(ir_nat_eqb a a) Bool.true ({N('nat_eqb_refl')} a)"
    )


def mem_lookup_skip() -> str:
    return (
        f"def {N('mem_lookup_skip')} (k : Nat) (p : Nat) (v : IRScalar) (live : Bool) (m : IRList IRMemSlot) "
        "(hne : Eq Bool (ir_nat_eqb k p) Bool.false) : Eq (IROption IRMemSlot) "
        "(ir_mem_lookup (IRList.cons IRMemSlot (IRMemSlot.mk k v live) m) p) (ir_mem_lookup m p) := "
        "ir_eq_cong Bool (IROption IRMemSlot) "
        "(fun (b : Bool) => Bool.rec (fun (_ : Bool) => IROption IRMemSlot) (ir_mem_lookup m p) "
        "(IROption.some IRMemSlot (IRMemSlot.mk k v live)) b) (ir_nat_eqb k p) Bool.false hne"
    )


def slot_b0() -> str:
    return (
        f"def {N('slot_b0')} : IRBlock := IRBlock.mk ir_d0 ir_nl0 "
        f"(IRList.cons IRNode (ir_nd1 (IRInst.alloca {TY} (IROption.none Nat)) ir_d1) "
        f"(ir_bd3 (ir_nd (IRInst.store {TY} ir_d1 ir_d0 Bool.false)) "
        f"(ir_nd1 (IRInst.load {TY} ir_d1 Bool.false) ir_d2) (ir_nd (IRInst.ret (ir_nl1 ir_d2)))))"
    )


def slot_func() -> str:
    return f"def {N('slot_func')} : IRFunc := IRFunc.mk ir_d0 (ir_nl1 ir_d0) ir_d0 (ir_blk {N('slot_b0')} ir_blk0)"


def module() -> str:
    return (f"def {N('module')} : IRModule := IRModule.mk "
            f"(IRList.cons IRFunc {N('slot_func')} (IRList.nil IRFunc)) (IRList.nil IRGlobal)")


def mach0() -> str:
    return f"def {N('mach0')} {BINDERS} : IRMachine := IRMachine.mk (IRList.cons IRFrame {FRAME0} rest) mem na"


def smach() -> str:
    return (f"def {N('smach')} {BINDERS} : IRMachine := IRMachine.mk "
            f"(IRList.cons IRFrame {FRAME1} rest) {MEM1} (Nat.succ na)")


def lmach() -> str:
    return (f"def {N('lmach')} {BINDERS} : IRMachine := IRMachine.mk "
            f"(IRList.cons IRFrame {FRAME2} rest) {MEM2} (Nat.succ na)")


def rmach() -> str:
    return (f"def {N('rmach')} {BINDERS} : IRMachine := IRMachine.mk (IRList.cons IRFrame "
            f"(ir_frame_bind {FRAME2} (ir_nl1 ir_d2) v) rest) {MEM2} (Nat.succ na)")


def after_store_lookup() -> str:
    return (f"def {N('after_store_lookup')} {BINDERS} (o : IROption IRMemSlot) : IRConfig := "
            f"ir_store_checked ({N('smach')} {ARGS}) na v o")


def after_store_update() -> str:
    return (f"def {N('after_store_update')} {BINDERS} (m2 : IRList IRMemSlot) : IRConfig := "
            f"ir_advance (ir_set_mem ({N('smach')} {ARGS}) m2)")


def after_load() -> str:
    return (f"def {N('after_load')} {BINDERS} (o : IROption IRMemSlot) : IRConfig := "
            f"ir_bind_result ({N('lmach')} {ARGS}) (ir_nl1 ir_d2) (ir_load_slot o)")


def step_alloca() -> str:
    rhs = f"(IRConfig.running ({N('smach')} {ARGS}))"
    return (f"def {N('step_alloca')} {BINDERS} : Eq IRConfig (ir_step {N('module')} ({N('mach0')} {ARGS})) "
            f"{rhs} := Eq.refl IRConfig {rhs}")


def step_store() -> str:
    rhs = f"({N('after_store_lookup')} {ARGS} (ir_mem_lookup {MEM1} na))"
    return (f"def {N('step_store')} {BINDERS} : Eq IRConfig (ir_step {N('module')} ({N('smach')} {ARGS})) "
            f"{rhs} := Eq.refl IRConfig {rhs}")


def store_resolved() -> str:
    rhs = f"({N('after_store_update')} {ARGS} (ir_mem_update {MEM1} na v))"
    return (f"def {N('store_resolved')} {BINDERS} : Eq IRConfig ({N('after_store_lookup')} {ARGS} "
            f"(IROption.some IRMemSlot {CELL0})) {rhs} := Eq.refl IRConfig {rhs}")


def step_load() -> str:
    rhs = f"({N('after_load')} {ARGS} (ir_mem_lookup {MEM2} na))"
    return (f"def {N('step_load')} {BINDERS} : Eq IRConfig (ir_step {N('module')} ({N('lmach')} {ARGS})) "
            f"{rhs} := Eq.refl IRConfig {rhs}")


def store_seg() -> str:
    goal = f"(IRConfig.running ({N('lmach')} {ARGS}))"
    return (
        f"def {N('store_seg')} {BINDERS} : Eq IRConfig "
        f"(ir_steps ir_d1 {N('module')} (IRConfig.running ({N('smach')} {ARGS}))) {goal} := "
        f"Eq.subst {SLOT} (fun (o : {SLOT}) => Eq IRConfig ({N('after_store_lookup')} {ARGS} o) {goal}) "
        f"(IROption.some IRMemSlot {CELL0}) (ir_mem_lookup {MEM1} na) "
        + symm(SLOT, f"(ir_mem_lookup {MEM1} na)", f"(IROption.some IRMemSlot {CELL0})",
               f"({N('mem_lookup_head')} na IRScalar.undef_ Bool.true mem)")
        + f" (Eq.subst {MEMT} (fun (m2 : {MEMT}) => Eq IRConfig ({N('after_store_update')} {ARGS} m2) {goal}) "
        f"{MEM2} (ir_mem_update {MEM1} na v) "
        + symm(MEMT, f"(ir_mem_update {MEM1} na v)", MEM2,
               f"({N('mem_update_head')} na IRScalar.undef_ Bool.true mem v)")
        + f" (Eq.refl IRConfig {goal}))"
    )


def load_seg() -> str:
    goal = f"(IRConfig.running ({N('rmach')} {NARGS}))"
    return (
        f"def {N('load_seg')} {NB} : Eq IRConfig "
        f"(ir_steps ir_d1 {N('module')} (IRConfig.running ({N('lmach')} {NARGS}))) {goal} := "
        f"Eq.subst {SLOT} (fun (o : {SLOT}) => Eq IRConfig ({N('after_load')} {NARGS} o) {goal}) "
        f"(IROption.some IRMemSlot {NCELL1}) (ir_mem_lookup {NMEM2} na) "
        + symm(SLOT, f"(ir_mem_lookup {NMEM2} na)", f"(IROption.some IRMemSlot {NCELL1})",
               f"({N('mem_lookup_head')} na (IRScalar.int_ n) Bool.true mem)")
        + f" (Eq.refl IRConfig {goal})"
    )


def activation() -> str:  # the leaf shape: three nested Eq.substs -- lookup, update, lookup
    cfg0 = f"(IRConfig.running ({N('mach0')} {NARGS}))"
    return (
        f"def {N('activation')} {NB} : Eq IRConfig (ir_steps ir_d4 {N('module')} {cfg0}) {TARGET} := "
        f"Eq.subst {SLOT} (fun (o : {SLOT}) => Eq IRConfig "
        f"(ir_steps ir_d2 {N('module')} ({N('after_store_lookup')} {NARGS} o)) {TARGET}) "
        f"(IROption.some IRMemSlot {CELL0}) (ir_mem_lookup {MEM1} na) "
        + symm(SLOT, f"(ir_mem_lookup {MEM1} na)", f"(IROption.some IRMemSlot {CELL0})",
               f"({N('mem_lookup_head')} na IRScalar.undef_ Bool.true mem)")
        + f" (Eq.subst {MEMT} (fun (m2 : {MEMT}) => Eq IRConfig "
        f"(ir_steps ir_d2 {N('module')} ({N('after_store_update')} {NARGS} m2)) {TARGET}) "
        f"{NMEM2} (ir_mem_update {MEM1} na (IRScalar.int_ n)) "
        + symm(MEMT, f"(ir_mem_update {MEM1} na (IRScalar.int_ n))", NMEM2,
               f"({N('mem_update_head')} na IRScalar.undef_ Bool.true mem (IRScalar.int_ n))")
        + f" (Eq.subst {SLOT} (fun (o : {SLOT}) => Eq IRConfig "
        f"(ir_steps ir_d1 {N('module')} ({N('after_load')} {NARGS} o)) {TARGET}) "
        f"(IROption.some IRMemSlot {NCELL1}) (ir_mem_lookup {NMEM2} na) "
        + symm(SLOT, f"(ir_mem_lookup {NMEM2} na)", f"(IROption.some IRMemSlot {NCELL1})",
               f"({N('mem_lookup_head')} na (IRScalar.int_ n) Bool.true mem)")
        + f" (Eq.refl IRConfig {TARGET})))"
    )


# The chain shape: `Eq.trans` / `ir_steps_add` / `Eq.subst` per segment, literal
# runs left for the kernel and lemma-backed runs spliced in opaque. Proving the
# slot twice -- leaf shape above, chain here -- licenses a generator to emit the
# chain form without re-deriving the semantics. A segment is
# (step count, RHS config or None if literal, discharging lemma).


def total(segs) -> str:
    expr = segs[-1][0]
    for s in reversed(segs[:-1]):
        expr = f"(Nat.add {expr} {s[0]})"
    return expr


def chain(segs, cfg: str, target: str) -> str:
    if len(segs) == 1:
        return f"(Eq.refl IRConfig {target})"
    (count, result, lemma), rest = segs[0], segs[1:]
    after = total(rest)
    stepped = steps(count, cfg)
    split = f"(ir_steps_add {N('module')} {after} {count} {cfg})"
    if result is None:
        body = chain(rest, stepped, target)
    else:
        body = (
            f"(Eq.subst IRConfig (fun (k : IRConfig) => Eq IRConfig {steps(after, 'k')} {target}) "
            f"{result} {stepped} (Eq.symm IRConfig {stepped} {result} {lemma}) "
            f"{chain(rest, result, target)})"
        )
    return f"(Eq.trans IRConfig {steps(total(segs), cfg)} {steps(after, stepped)} {target} {split} {body})"


def segments():
    return [
        ("ir_d1", None, None),  # alloca -- computes
        ("ir_d1", f"(IRConfig.running ({N('lmach')} {NARGS}))", f"({N('store_seg')} {NARGS})"),
        ("ir_d1", f"(IRConfig.running ({N('rmach')} {NARGS}))", f"({N('load_seg')} mem n na dests rest)"),
        ("ir_d1", None, None),  # ret -- computes
    ]


def seg() -> str:
    segs = segments()
    cfg0 = f"(IRConfig.running ({N('mach0')} {NARGS}))"
    return (f"def {N('seg')} {NB} : Eq IRConfig (ir_steps {total(segs)} {N('module')} {cfg0}) "
            f"{TARGET} := ") + chain(segs, cfg0, TARGET)


def cost_is_4() -> str:
    """From the SAME `segments()` list the chain is."""
    return f"def {N('cost_is_4')} : Eq Nat {total(segments())} ir_d4 := Eq.refl Nat ir_d4"


def concrete() -> str:
    return (f"def {N('concrete')} : Eq IROutcome (ir_eval ir_d8 {N('module')} ir_d0 "
            "(ir_vl1 (IRScalar.int_ ir_d5)) ir_mem0 ir_d7) (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d5))) := "
            "Eq.refl IROutcome (IROutcome.ret (ir_vl1 (IRScalar.int_ ir_d5)))")


def resumes_caller() -> str:
    return (
        f"def {N('resumes_caller')} (mem : IRList IRMemSlot) (n : Nat) (na : Nat) (dests : IRList Nat) "
        "(caller : IRFrame) (rest2 : IRList IRFrame) : Eq IRConfig "
        f"(ir_steps ir_d4 {N('module')} (IRConfig.running ({N('mach0')} mem (IRScalar.int_ n) na dests "
        "(IRList.cons IRFrame caller rest2)))) (IRConfig.running (IRMachine.mk (IRList.cons IRFrame "
        f"(ir_frame_set_many caller dests (ir_vl1 (IRScalar.int_ n))) rest2) {NMEM2} (Nat.succ na))) := "
        f"{N('activation')} mem n na dests (IRList.cons IRFrame caller rest2)"
    )


# (const, builder, key, spec name, probe name, sha256 of the PROBE term), in the
# REGISTRATION order `--check` pins against the stage's DECLS table.
TERMS = [
    ("SRC_EXEC_LOAD_IS_VIEW", exec_load_is_view, "exec_load_is_view", "ir_exec_load_is_view", "ir_probe_exec_load_is_view", "d98f97a60f5f72ed5cc394fdee01ce0266c2946317b49c701373227aa2d0e43a"),
    ("SRC_VIEW_WORD_AGG", view_word_agg, "view_word_agg", "ir_view_word_agg", "ir_probe_view_word_agg", "4b21950966d6113ea1e40c9317d3159a7a32d5038a692c5b6e19581d627327ab"),
    ("SRC_VIEW_OPT_AGG", view_opt_agg, "view_opt_agg", "ir_view_opt_agg", "ir_probe_view_opt_agg", "951fc43f0cab8b9eba977246eac444c593549679b50e3a94cdfb65872a30ab58"),
    ("SRC_VIEW_TY_AGG", view_ty_agg, "view_ty_agg", "ir_view_ty_agg", "ir_probe_view_ty_agg", "c5ef7c32e42f39b5cdb0749dae68a3f3a3f156b0406030ab4ba51843abb79db2"),
    ("SRC_LOAD_VIEW_OPT_AGG", load_view_opt_agg, "load_view_opt_agg", "ir_load_view_opt_agg", "ir_probe_load_view_opt_agg", "8d8ede92165d551ff50f683d0648aefabdca48ba8c5cc5427b2a0664c92e9f76"),
    ("SRC_LOAD_VIEW_AGG", load_view_agg, "load_view_agg", "ir_load_view_agg", "ir_probe_load_view_agg", "8c52346fc94eeb4bcceaee6e1208c402afc129f6e91471abd0c1bc2953d7c6eb"),
    ("SRC_EXEC_LOAD_AGG", exec_load_agg, "exec_load_agg", "ir_exec_load_agg", "ir_probe_exec_load_agg", "b01825386da687c31ef5d53e88701391feacbac4873cf1766d316f75278016b8"),
    ("SRC_NAT_SUB_SELF", nat_sub_self, "nat_sub_self", "ir_nat_sub_self", "ir_probe_nat_sub_self", "9f50e8c354acfcad4978e8596014687bb7f3337633ac9656658fade158b518ba"),
    ("SRC_NAT_EQB_WALK_REFL", nat_eqb_walk_refl, "nat_eqb_walk_refl", "ir_nat_eqb_walk_refl", "ir_probe_nat_eqb_walk_refl", "42cfc0a556bbeb3576f5dad32485e5b3c40066363cd4d73c6964ec1e2d9e85e1"),
    ("SRC_NAT_EQB_REFL", nat_eqb_refl, "nat_eqb_refl", "ir_nat_eqb_refl", "ir_probe_nat_eqb_refl", "bbcf976bd18f4153c0bc342c267144fdaa53e783f524653a419a5bc9f473cb56"),
    ("SRC_MEM_LOOKUP_HEAD", mem_lookup_head, "mem_lookup_head", "ir_mem_lookup_head", "ir_probe_mem_lookup_head", "3bf5bde0aac41bc438e1e5d580c36d22ccdcdf7754b5fa8c55fae42b2fa11698"),
    ("SRC_MEM_UPDATE_HEAD", mem_update_head, "mem_update_head", "ir_mem_update_head", "ir_probe_mem_update_head", "af2ac1b5d765b7a287aa424a85f7b87c7697bca4374c3171d2a33dbd0ddc8ce3"),
    ("SRC_MEM_LOOKUP_SKIP", mem_lookup_skip, "mem_lookup_skip", "ir_mem_lookup_skip", "ir_probe_mem_lookup_skip", "fdf15420192dbe0277c12c42c8b60a603af8a0188dcd4daf0adae7e73e39f819"),
    ("SRC_SLOT_B0", slot_b0, "slot_b0", "ir_slot_b0", "ir_probe_slot_b0", "d218c466fbd1abd7699d0172e455d560154a1e8e16b67be4fac0b3af28038791"),
    ("SRC_SLOT_FUNC", slot_func, "slot_func", "ir_slot_func", "ir_probe_slot_func", "543039e5b0690fd182b7c71d112c65e1ebb87332fb0f9ad7fffb9e820d0de563"),
    ("SRC_SLOT_MODULE", module, "module", "ir_slot_module", "ir_probe_module", "5e2d22c7c496625ea529f7736325d4d63c312625adcd47aaf131c5c35dc2f120"),
    ("SRC_MACH0", mach0, "mach0", "ir_slot_mach0", "ir_probe_mach0", "ac0273bdb66870eb7683e4421fe5c70149196a5e6d3539f1846fdccde35effc5"),
    ("SRC_SMACH", smach, "smach", "ir_slot_smach", "ir_probe_smach", "7d5a74c9be9e2536c5482e4d87146e1983cea701dd8a82dcff92ef699ae463ef"),
    ("SRC_LMACH", lmach, "lmach", "ir_slot_lmach", "ir_probe_lmach", "43411edf6ad18a9fda8d3eb89f697647861b37cd74a43585401ca6b8a02773a2"),
    ("SRC_RMACH", rmach, "rmach", "ir_slot_rmach", "ir_probe_rmach", "630091e383e4121f39cf00238fcae1a9f6a9f39b540c2489d396bf747291b153"),
    ("SRC_AFTER_STORE_LOOKUP", after_store_lookup, "after_store_lookup", "ir_slot_after_store_lookup", "ir_probe_after_store_lookup", "59bd71c63242cd343d5400e6d3e432790601e5d9a075a166c4d586a78a9b152e"),
    ("SRC_AFTER_STORE_UPDATE", after_store_update, "after_store_update", "ir_slot_after_store_update", "ir_probe_after_store_update", "eab58fbe4af5cf2fe5b7f73915586109d54f343e54f4380c251dbeca7a049845"),
    ("SRC_AFTER_LOAD", after_load, "after_load", "ir_slot_after_load", "ir_probe_after_load", "74ee952e8af51fb45d9f6d64a6f2af59da0cd4792f5a62a8231781a59c4e15ec"),
    ("SRC_STEP_ALLOCA", step_alloca, "step_alloca", "ir_slot_step_alloca", "ir_probe_step_alloca", "536d7638963f7a175c39fe2cc3510577afef65a0207f624d566cf624231cf8d8"),
    ("SRC_STEP_STORE", step_store, "step_store", "ir_slot_step_store", "ir_probe_step_store", "f044af18434e53c826c8d825df46ef68a06aa8fecdcbb31d373f5929f85425f9"),
    ("SRC_STORE_RESOLVED", store_resolved, "store_resolved", "ir_slot_store_resolved", "ir_probe_store_resolved", "d713b21ce0cd8bce33325a477b9682feaa565a275d0ca161a9289fdaa24d61a1"),
    ("SRC_STEP_LOAD", step_load, "step_load", "ir_slot_step_load", "ir_probe_step_load", "02c419c72eacaaa1bc7694ab9657741ab123edf95028286e9f2d90577a0f4581"),
    ("SRC_STORE_SEG", store_seg, "store_seg", "ir_slot_store_seg", "ir_probe_store_seg", "b4a5f958b3dabb02ca52964b7b342a65b8cc0d564450b185c186409a3d2b5cf0"),
    ("SRC_LOAD_SEG", load_seg, "load_seg", "ir_slot_load_seg", "ir_probe_load_seg", "862e1a3486396fa67d0d902ea03fceb12176b78f9231d9a66d895b269b0b34f7"),
    ("SRC_ACTIVATION", activation, "activation", "ir_slot_activation", "ir_probe_slot_activation", "ec69a9163e99ab0f3c8f53dfd5b4ab2475adfb63b07201366c4984fffa308d54"),
    ("SRC_SEG", seg, "seg", "ir_slot_seg", "ir_probe_slot_seg", "2ac1b5813b58be65fb908f9373dac0b41857272fdb935f11a38509cf1535b9dd"),
    ("SRC_COST_IS_4", cost_is_4, "cost_is_4", "ir_slot_cost_is_4", "ir_probe_slot_cost_is_4", "b086235fcb46398006dddee1e4471ff23ae2423a6d20edab92be8d15c2a005b3"),
    ("SRC_CONCRETE", concrete, "concrete", "ir_slot_concrete", "ir_probe_slot_concrete", "863c3b8832649d2c2056991ac302f45bdaea42040d12e1b4b34411724e06835b"),
    ("SRC_RESUMES_CALLER", resumes_caller, "resumes_caller", "ir_slot_resumes_caller", "ir_probe_slot_resumes_caller", "bb1384f2973d213b30ff1ff5610ba25f6c21fe64d4d1e19c6f44d12382b01400"),
]
NAMES.update({k: s for _c, _f, k, s, _p, _d in TERMS})

CONST_RE = re.compile(r'^const (SRC_[A-Z0-9_]+): &str =\s*"(.*?)";$', re.M | re.S)
# The stage registers its `DECLS` table and nothing else, so the row order IS
# the registration order and `SLOT_LEMMA_NAMES` is every declaration it adds.
DECLS_RE = re.compile(r"const DECLS: &\[\(&str, &str\)\] = &\[(.*?)\n\];", re.S)
ROW_RE = re.compile(r"^\s*\((SRC_[A-Z0-9_]+),", re.M)
DECLARED_RE = re.compile(r"pub const SLOT_LEMMA_NAMES: &\[&str\] = &\[(.*?)\];", re.S)


def rust_escape(s: str) -> str:
    return s.replace("\\", "\\\\").replace('"', '\\"')


def minted() -> dict[str, str]:
    return {const: fn() for const, fn, _k, _s, _p, _d in TERMS}


def check() -> int:
    if not SLOT_RS.exists():
        raise SystemExit(f"gen_slot_lemmas: {SLOT_RS} does not exist")
    src = SLOT_RS.read_text()
    have = dict(CONST_RE.findall(src))
    want = minted()
    bad = 0
    for const, body in want.items():
        escaped = rust_escape(body)
        if const not in have:
            print(f"MISSING {const}: no `const {const}: &str = \"...\";` in {SLOT_RS.name}")
            bad += 1
        elif have[const] != escaped:
            print(f"DIFFERS {const}: committed {len(have[const])} chars, minted {len(escaped)} chars")
            i = next((j for j, (x, y) in enumerate(zip(have[const], escaped)) if x != y), 0)
            print(f"  first difference at {i}:\n    committed: ...{have[const][max(0, i - 90):i + 90]}..."
                  f"\n    minted:    ...{escaped[max(0, i - 90):i + 90]}...")
            bad += 1
        else:
            print(f"ok {const} ({len(body)} chars)")
    extra = sorted(set(have) - set(want))
    if extra:
        print(f"UNDECLARED consts in {SLOT_RS.name}: {extra} -- add them to TERMS or delete them")
        bad += len(extra)
    table = DECLS_RE.search(src)  # the registration ORDER, and then the name list
    want_order = [c for c, _f, _k, _s, _p, _d in TERMS]
    if not table:
        print("MISSING: the stage's `const DECLS: &[(&str, &str)] = &[...]` no longer parses")
        bad += 1
    elif ROW_RE.findall(table.group(1)) != want_order:
        print(f"ORDER: DECLS rows are {ROW_RE.findall(table.group(1))}, expected {want_order}")
        bad += 1
    block = DECLARED_RE.search(src)
    if not block:
        print("MISSING: the stage's `pub const SLOT_LEMMA_NAMES: &[&str] = &[...]` no longer parses")
        bad += 1
    else:
        declared = re.findall(r'"([^"]+)"', block.group(1))
        want_names = [s for _c, _f, _k, s, _p, _d in TERMS]
        if declared != want_names:
            print(f"SLOT_LEMMA_NAMES: tree has {declared}, expected {want_names}")
            bad += 1
    if bad:
        print(f"gen_slot_lemmas: {bad} discrepancy(ies)", file=sys.stderr)
        return 1
    print(f"gen_slot_lemmas: {len(want)} terms, DECLS order and SLOT_LEMMA_NAMES match {SLOT_RS.name}")
    return 0


def emit() -> int:
    src = SLOT_RS.read_text()
    for const, body in minted().items():
        pat = re.compile(r'(const ' + const + r': &str =\s*")(.*?)(";\n)', re.S)
        if not pat.search(src):
            print(f"gen_slot_lemmas: {const} not found in {SLOT_RS}", file=sys.stderr)
            return 1
        src = pat.sub(lambda m: m.group(1) + rust_escape(body) + m.group(3), src, count=1)
    SLOT_RS.write_text(src)
    print(f"gen_slot_lemmas: emitted {len(TERMS)} term(s) into {SLOT_RS.name}; run rustfmt")
    return 0


def self_test() -> int:
    """The correctness argument, and not a claim about this script's code:
    re-emitted under the probe's OWN names, every term must reproduce -- byte for
    byte -- the one the Phase-B probe kernel-checked (28/28 candidates,
    target/crystal-lane/probeB/gen_probeB.py). Those digests are of terms a kernel
    accepted, so a refactor that changes a shape fails here, not in a spec build.

    PROVENANCE IS NOT UNIFORM, and saying so is the point of a digest. The 26
    return-slot terms reproduce the 2026 Phase-B probe. The seven store/load
    VIEW terms added 2026-09-13 have no probe behind them -- their digests are
    of the terms THIS tree's kernel accepted in the EvalIr bundle on that date.
    A THIRD kind arrived 2026-09-15 with `ir_nat_eqb_walk_refl` and the reworked
    `ir_nat_eqb_refl`: terms pinned at the shape TWO DISJOINT kernels accept.
    Clean's kernel checks them in the EvalIr bundle, and Lean 4 v4.30.0-rc2
    checks the exported image -- which is the property the rework exists to buy,
    because the shape it replaced had only the first kernel. Re-pinning one of
    these means the export's replay guard may have moved underneath it; re-run
    `gate::leancross` rather than just re-minting the digest.

    All three kinds pin a shape a kernel has seen; the first also pins an
    independent re-derivation and the third an independent RE-CHECK, and a reader
    is owed that distinction."""
    keep = dict(NAMES)
    NAMES.update({k: p for _c, _f, k, _s, p, _d in TERMS})
    try:
        bad = 0
        for const, fn, _k, _s, _p, digest in TERMS:
            got = hashlib.sha256(fn().encode()).hexdigest()
            if got == digest:
                print(f"ok {const}: probe term reproduced ({digest[:12]}...)")
            else:
                print(f"FAIL {const}: probe shape is {got[:12]}..., pinned {digest[:12]}...")
                bad += 1
        if bad:
            print(
                "gen_slot_lemmas: the emitter no longer reproduces the kernel-checked "
                "Phase-B probe terms, so --check below proves nothing",
                file=sys.stderr,
            )
            return 1
        print(f"gen_slot_lemmas self-test: {len(TERMS)}/{len(TERMS)} probe terms reproduced")
        return 0
    finally:
        NAMES.clear()
        NAMES.update(keep)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true", help="byte-compare with the committed consts")
    ap.add_argument("--print", dest="show", help="print one term by const name")
    ap.add_argument("--emit", action="store_true", help="rewrite the consts in place")
    ap.add_argument("--self-test", action="store_true", help="reproduce the probe's terms")
    args = ap.parse_args(argv)
    if args.self_test:
        return self_test()
    if args.show:
        print(minted()[args.show])
        return 0
    if args.emit:
        return emit()
    return check()


if __name__ == "__main__":
    sys.exit(main())
