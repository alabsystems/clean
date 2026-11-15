#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Mint E2's SECOND instance: `TypeChecker::infer_type` through the step-indexed
contract device (`eval_ir_ctr.rs`).

The first instance (`gen_lzd_sctr.py`) is `Level::is_zero`: a one-function
recursion group whose body calls ITSELF. This one is chosen because its shape
differs on every axis the cost question is about:

  * the body is the designated target's own minted body (`ir_it_func`, six
    blocks, 36 nodes), over an ABSTRACT module `IRModule.mk fs gs` -- every step
    is a rewrite through `h0` / `h1` / `h2` (the itf step lemmas), never a
    definitional computation;
  * it calls two OTHER functions (tick_heartbeat, infer_type_fast) and itself
    not at all;
  * the recursion group is MUTUAL: a three-member table (`IRItIn`: infer_type,
    tick_heartbeat, infer_type_fast) whose two callee members' LOCAL
    obligations are premises -- the assume-guarantee form of infer_type's real
    situation, where infer_type_fast calls back into infer_type.

Every CALL in the body's obligation is discharged by the group hypothesis at
the strictly smaller budget `n`; the one step `succ n` pays for is the body's
first node (the alloca); every other literal run is padded (`ir_safe_pad`)
through the SAME step lemmas `ir_it_ag_activation` splices -- nothing about the
body is re-stated here.

ONE LEMMA PER CALL (D5's re-decided remedy, 2026-09-25): the body's
obligation is minted as a chain -- `ir_it_top_sseg` walks the body to its
first call (tick_heartbeat) and hands that call's continuation to
`ir_it_top_sseg_r1`, the safety of the configuration the body resumes at; `_r1`
walks the dispatch to the second call (infer_type_fast) and hands its
continuation to `_r2`, which runs the transport tail to the `ret`. No term
nests one call's continuation inside another's. Each segment binds exactly the
names its statement and proof mention, the continuation-bound heaps, counters,
posts and case witnesses of earlier calls included. `ir_it_top_sseg`'s
STATEMENT is byte-identical to the nested form's; `--self-test` still
reproduces the nested term the kernel accepted on 2026-09-24 (`LEGACY_DIGESTS`).

The terms emitted, and where they live:

  eval_ir_it_sctr.rs  ir_it_top_sseg_r2, ir_it_top_sseg_r1, ir_it_top_sseg
                                            -- the body's local obligation
  eval_ir_it_pc.rs    ir_it_local           -- the table's local obligation
                      ir_it_ctr             -- ir_ctr_group_sound on the table
                      ir_it_pc              -- partial correctness + safety
                      ir_it_pc_no_bad_halt / ir_it_pc_never_unreachable
                      ir_it_pc_of_exact     -- the table at the exact premises
                      ir_it_pc_a4_crosscheck -- EXACTLY ir_it_ag_correct's type

USAGE
    python3 scripts/gen_it_sctr.py --print <name>
    python3 scripts/gen_it_sctr.py --emit       # rewrite the Rust consts
    python3 scripts/gen_it_sctr.py --check      # byte-compare with the tree
    python3 scripts/gen_it_sctr.py --self-test  # pinned digests + coverage
    python3 scripts/gen_it_sctr.py --pin        # re-pin (only after the kernel accepted)
"""

from __future__ import annotations

import argparse
import hashlib
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
CORE = REPO / "crates/clean-verify/src/spec/core_spec"
SCTR_RS = CORE / "eval_ir_it_sctr.rs"
PC_RS = CORE / "eval_ir_it_pc.rs"
TARGETS = (SCTR_RS, PC_RS)

# ------------------------------------------------------------ vocabulary
M = "(IRModule.mk fs gs)"
MEMT = "IRList IRMemSlot"
VST = "IRList IRScalar"
SLOT = "IROption IRMemSlot"
# The same two types in ARGUMENT position (after Eq / Eq.subst / ...), where the
# application must be parenthesized.
VSTA = f"({VST})"
SLOTA = f"({SLOT})"
POST = f"{MEMT} -> Nat -> {VST} -> Prop"
QHT = f"Nat -> {MEMT} -> Nat -> {POST}"
QFT = f"Nat -> Nat -> {MEMT} -> Nat -> {POST}"
PTT = f"Nat -> Nat -> {MEMT} -> Nat -> Prop"
PHT = f"Nat -> {MEMT} -> Nat -> Prop"
PFT = PTT


def fnd(i: str, f: str) -> str:
    return f"Eq (IROption IRFunc) (ir_func_find fs {i}) (IROption.some IRFunc {f})"


H0T, H1T, H2T = fnd("ir_d0", "ir_it_func"), fnd("ir_d1", "g1"), fnd("ir_d2", "g2")


def hb_heap(mem: str, na: str) -> str:
    """The heap tick_heartbeat is entered with: the Result slot allocated at `na`."""
    return f"(IRList.cons IRMemSlot (IRMemSlot.mk {na} IRScalar.undef_ Bool.true) {mem})"


def loc0(p: str, q: str, na: str) -> str:
    """infer_type's locals after the alloca: %2 the slot pointer, then the parameters."""
    return (f"(IRList.cons IRBinding (IRBinding.mk ir_d2 (IRScalar.ptr_ {na})) "
            f"(IRList.cons IRBinding (IRBinding.mk ir_d0 (IRScalar.ptr_ {p})) "
            f"(IRList.cons IRBinding (IRBinding.mk ir_d1 (IRScalar.ptr_ {q})) (IRList.nil IRBinding))))")


def frame5(sp: str, p: str, q: str, na: str, ds: str) -> str:
    """The b5 frame beneath infer_type_fast's: pc 1, %4 the tag, %3 the answer."""
    return (f"(IRFrame.mk ir_d0 ir_d5 ir_d1 (IRList.cons IRBinding (IRBinding.mk ir_d4 (IRScalar.int_ ir_d0)) "
            f"(IRList.cons IRBinding (IRBinding.mk ir_d3 (ir_it_hb_answer {sp})) {loc0(p, q, na)})) {ds})")


def hbans(sp: str) -> str:
    return f"(ir_vl1 (ir_it_hb_answer {sp}))"


def aggv(spv: str) -> str:
    return f"(ir_vl1 (IRScalar.aggv {spv}))"


def lookup_live(mem: str, a: str, v0: str) -> str:
    return f"Eq {SLOTA} (ir_mem_lookup {mem} {a}) (IROption.some IRMemSlot (IRMemSlot.mk {a} {v0} Bool.true))"


def ctr(entry: str, post: str, budget: str) -> str:
    return f"ir_ctr_at {M} {entry} {post} {budget}"


def safe(cfg: str) -> str:
    return f"ir_safe G {M} n {cfg}"


def pad(k: str, cfg: str, inner: str) -> str:
    """`ir_safe G M n cfg` from `ir_safe G M n (ir_steps k M cfg)` -- an exact run is free."""
    return f"(ir_safe_pad G {M} n {k} {cfg} {inner})"


def rw(frm: str, to: str, eq: str, inner: str) -> str:
    """`ir_safe G M n frm` from `eq : frm = to` and `inner : ir_safe G M n to`."""
    return (f"(Eq.subst IRConfig (fun (c : IRConfig) => {safe('c')}) {to} {frm} "
            f"(Eq.symm IRConfig {frm} {to} {eq}) {inner})")


def run(mach: str) -> str:
    return f"(IRConfig.running {mach})"


# ------------------------------------------------ one lemma per call
#
# `SEGMENTED = False` reproduces the nested term the kernel accepted on
# 2026-09-24 (the self-test's legacy arm); the tree carries the segmented form.
SEGMENTED = True
_TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")


def split_binders(text: str) -> list:
    """`(x : T) (y : U) ` -> [(x, T), (y, U)], split at top-level parentheses."""
    out, depth, start = [], 0, 0
    for i, ch in enumerate(text):
        if ch == "(":
            if depth == 0:
                start = i
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0:
                name, ty = text[start + 1:i].split(" : ", 1)
                out.append((name.strip(), ty.strip()))
    assert depth == 0, "unbalanced binder list"
    return out


def needed(scope: list, text: str) -> list:
    """The binders of `scope` that `text` mentions, closed under mention in the
    kept binders' types, in scope order (over-inclusion is the only error a
    token scan can make, and an unused binder is harmless)."""
    names = [nm for nm, _ in scope]
    assert len(names) == len(set(names)), f"shadowed binder in scope: {names}"
    want, keep = set(_TOKEN.findall(text)), set()
    grew = True
    while grew:
        grew = False
        for nm, ty in scope:
            if nm in want and nm not in keep:
                keep.add(nm)
                want |= set(_TOKEN.findall(ty))
                grew = True
    return [(nm, ty) for nm, ty in scope if nm in keep]


def resume(lemmas: list, name: str, scope: list, cfg: str, proof: str) -> str:
    """`ir_safe G M n cfg` by `proof`: inline (legacy), or ONE named lemma --
    appended to `lemmas` -- applied to exactly the binders it needs."""
    if not SEGMENTED:
        return proof
    stmt = safe(cfg)
    binders = needed(scope, f"{stmt} {proof}")
    rendered = "".join(f"({nm} : {ty}) " for nm, ty in binders)
    lemmas.append((name, f"def {name} {rendered}: {stmt} := {proof}"))
    return f"({name} {' '.join(nm for nm, _ in binders)})"


# ------------------------------------------------ the body's local obligation

def hq1_ty(p: str, mem: str, na: str) -> str:
    return (f"forall (mem1 : {MEMT}) (na1 : Nat) (vs : {VST}), QH {p} {mem} {na} mem1 na1 vs -> "
            f"forall (C : Prop), (forall (sp : IRScalar), Eq {VSTA} vs {hbans('sp')} -> C) -> C")


def hq2_ty(p: str, q: str, na: str, hbm: str, prefix: str = "") -> str:
    return (f"forall {prefix}(mem1 : {MEMT}) (na1 : Nat) (vs1 : {VST}) (mem2 : {MEMT}) (na2 : Nat) (vs : {VST}), "
            f"QH {p} {hbm} (Nat.succ {na}) mem1 na1 vs1 -> QF {p} {q} mem1 na1 mem2 na2 vs -> "
            f"forall (C : Prop), (forall (spv : IRScalar) (v0 : IRScalar), Eq {VSTA} vs {aggv('spv')} -> "
            f"{lookup_live('mem2', na, 'v0')} -> C) -> C")


def top_sseg() -> list:
    """The body's obligation as `[(name, source)]`: `_r2`, `_r1`, then the
    obligation itself (a segment before every lemma that applies it)."""
    lemmas: list = []
    hbm = hb_heap("mem", "na")
    l0 = loc0("p", "q", "na")
    r1 = f"(IRList.cons IRFrame (ir_it_dframe {l0} ds) rest)"
    f5 = frame5("sp", "p", "q", "na", "ds")
    r2 = f"(IRList.cons IRFrame {f5} rest)"
    tpost = "ir_it_tpost QH QF p q mem na"
    binders = (f"(fs : IRList IRFunc) (gs : IRList IRGlobal) (g1 : IRFunc) (g2 : IRFunc) "
               f"(QH : {QHT}) (QF : {QFT}) (p : Nat) (q : Nat) (mem : {MEMT}) (na : Nat) (n : Nat) "
               f"(h0 : {H0T}) (h1 : {H1T}) (h2 : {H2T}) "
               f"(hq1 : {hq1_ty('p', hbm, '(Nat.succ na)')}) "
               f"(hq2 : {hq2_ty('p', 'q', 'na', hbm)}) "
               f"(ihh : {ctr(f'(ir_it_hb_entry g1 p {hbm} (Nat.succ na))', f'(QH p {hbm} (Nat.succ na))', 'n')}) "
               f"(ihf : forall (mem1 : {MEMT}) (na1 : Nat) (vs1 : {VST}), QH p {hbm} (Nat.succ na) mem1 na1 vs1 -> "
               f"{ctr('(ir_it_fast_entry g2 p q mem1 na1)', '(QF p q mem1 na1)', 'n')}) ")
    concl = ctr("(ir_it_ag_entry p q mem na)", f"({tpost})", "(Nat.succ n)")
    kty = (f"forall (mem3 : {MEMT}) (na3 : Nat) (vs : {VST}), {tpost} mem3 na3 vs -> "
           f"ir_safe G {M} (Nat.succ n) (ir_ret_to ds rest mem3 na3 vs)")
    # What is in scope at each resume point: the obligation's binders, the
    # contract's (G, caller, continuation), then what each call's continuation
    # and its post's case analysis bind.
    scope0 = split_binders(binders) + [
        ("G", "IROutcome -> Prop"), ("ds", "IRList Nat"), ("rest", "IRList IRFrame"), ("hK", kty)]
    scope1 = scope0 + [
        ("mem1", MEMT), ("na1", "Nat"), ("vs1", VST),
        ("hqh", f"QH p {hbm} (Nat.succ na) mem1 na1 vs1"),
        ("sp", "IRScalar"), ("hv", f"Eq {VSTA} vs1 {hbans('sp')}")]
    scope2 = scope1 + [
        ("mem2", MEMT), ("na2", "Nat"), ("vs2", VST),
        ("hqf", "QF p q mem1 na1 mem2 na2 vs2"),
        ("spv", "IRScalar"), ("v0", "IRScalar"), ("hv2", f"Eq {VSTA} vs2 {aggv('spv')}"),
        ("hslot", lookup_live("mem2", "na", "v0"))]

    # ---- after infer_type_fast returned: store, br, load (the transport seam), ret
    smach = run("(ir_it3_smach p q na sp spv ds rest mem2 na2)")
    lmach = run("(ir_it3_lmach p q na sp spv ds rest mem2 na2)")
    final = f"(ir_ret_to ds rest (ir_mem_update mem2 na (IRScalar.aggv spv)) na2 {aggv('spv')})"
    tpi = (f"(fun (C : Prop) (k : forall (m1 : {MEMT}) (k1 : Nat) (w1 : {VST}) (m2 : {MEMT}), "
           f"QH p {hbm} (Nat.succ na) m1 k1 w1 -> QF p q m1 k1 m2 na2 {aggv('spv')} -> C) => "
           f"k mem1 na1 vs1 mem2 hqh (Eq.subst {VSTA} (fun (v : {VST}) => QF p q mem1 na1 mem2 na2 v) "
           f"vs2 {aggv('spv')} hv2 hqf))")
    tail = pad("ir_d3", smach, rw(
        f"(ir_steps ir_d3 {M} {smach})", lmach,
        f"(ir_it_seam3_ext fs gs h0 {smach} (ir_it3_lmach p q na sp spv ds rest mem2 na2) "
        f"(ir_it_transport3_at p q na sp spv ds rest mem2 na2 v0 hslot))",
        pad("ir_d1", lmach, rw(
            f"(ir_steps ir_d1 {M} {lmach})", final,
            "(ir_it_ag_ret_steps1 fs gs p q na sp spv ds rest mem2 na2 h0)",
            f"(ir_safe_down G {M} n {final} (hK (ir_mem_update mem2 na (IRScalar.aggv spv)) na2 "
            f"{aggv('spv')} {tpi}))"))))
    tail = resume(lemmas, "ir_it_top_sseg_r2", scope2,
                  f"(ir_ret_to (ir_nl1 ir_d29) {r2} mem2 na2 {aggv('spv')})", tail)
    ret2 = f"(ir_ret_to (ir_nl1 ir_d29) {r2} mem2 na2 vs2)"
    k2 = (
        f"(fun (mem2 : {MEMT}) (na2 : Nat) (vs2 : {VST}) (hqf : QF p q mem1 na1 mem2 na2 vs2) => "
        f"hq2 mem1 na1 vs1 mem2 na2 vs2 hqh hqf ({safe(ret2)}) "
        f"(fun (spv : IRScalar) (v0 : IRScalar) (hv2 : Eq {VSTA} vs2 {aggv('spv')}) "
        f"(hslot : {lookup_live('mem2', 'na', 'v0')}) => "
        f"Eq.subst {VSTA} (fun (v : {VST}) => {safe(f'(ir_ret_to (ir_nl1 ir_d29) {r2} mem2 na2 v)')}) "
        f"{aggv('spv')} vs2 (Eq.symm {VSTA} vs2 {aggv('spv')} hv2) {tail}))"
    )

    # ---- after tick_heartbeat returned: br, extractfield, switch (the dispatch seam), call 2
    hbret = f"(ir_ret_to (ir_nl1 ir_d3) {r1} mem1 na1 {hbans('sp')})"
    dend = run(f"(ir_it_dispatch_end sp {l0} ds rest mem1 na1)")
    push2 = run("(ir_it_ag_push2_m g2 sp p q na ds rest mem1 na1)")
    mid = pad("ir_d3", hbret, rw(
        f"(ir_steps ir_d3 {M} {hbret})", dend,
        f"(ir_it_dispatch_seg_ext fs gs h0 sp {l0} ds rest mem1 na1)",
        pad("ir_d1", dend, rw(
            f"(ir_steps ir_d1 {M} {dend})", push2,
            "(ir_it_ag_call2_steps1 fs gs g2 sp p q na ds rest mem1 na1 h0 h2)",
            f"(ihf mem1 na1 vs1 hqh G (ir_nl1 ir_d29) {r2} {k2})"))))
    mid = resume(lemmas, "ir_it_top_sseg_r1", scope1, hbret, mid)
    ret1 = f"(ir_ret_to (ir_nl1 ir_d3) {r1} mem1 na1 vs1)"
    k1 = (
        f"(fun (mem1 : {MEMT}) (na1 : Nat) (vs1 : {VST}) (hqh : QH p {hbm} (Nat.succ na) mem1 na1 vs1) => "
        f"hq1 mem1 na1 vs1 hqh ({safe(ret1)}) "
        f"(fun (sp : IRScalar) (hv : Eq {VSTA} vs1 {hbans('sp')}) => "
        f"Eq.subst {VSTA} (fun (v : {VST}) => {safe(f'(ir_ret_to (ir_nl1 ir_d3) {r1} mem1 na1 v)')}) "
        f"{hbans('sp')} vs1 (Eq.symm {VSTA} vs1 {hbans('sp')} hv) {mid}))"
    )

    # ---- entry: the budget pays the alloca; the heartbeat call's push is padded
    entry = "(ir_it_ag_entry p q mem na ds rest)"
    alloca = run("(ir_it_ag_alloca_m p q mem na ds rest)")
    push1 = run("(ir_it_ag_push1_m g1 p q mem na ds rest)")
    proof = (
        f"fun (G : IROutcome -> Prop) (ds : IRList Nat) (rest : IRList IRFrame) (hK : {kty}) => "
        + rw(f"(ir_step {M} {entry})", alloca, "(ir_it_ag_step_alloca fs gs p q mem na ds rest h0)",
             pad("ir_d1", alloca, rw(
                 f"(ir_steps ir_d1 {M} {alloca})", push1,
                 "(ir_it_ag_step_call fs gs g1 p q mem na ds rest h0 h1)",
                 f"(ihh G (ir_nl1 ir_d3) {r1} {k1})")))
    )
    return lemmas + [("ir_it_top_sseg", f"def ir_it_top_sseg {binders}: {concl} := {proof}")]


# ------------------------------------------------------------- the table

def in_ctr(x: str, budget: str) -> str:
    return ctr(f"(ir_it_in_entry g1 g2 {x})", f"(ir_it_in_post QH QF {x})", budget)


def ih_ty(budget: str) -> str:
    return f"forall (a : IRItIn), ir_it_in_pre PT PH PF a -> {in_ctr('a', budget)}"


HB_M = hb_heap("mem", "na")

PARAMS = (
    f"(fs : IRList IRFunc) (gs : IRList IRGlobal) (g1 : IRFunc) (g2 : IRFunc) "
    f"(PT : {PTT}) (PH : {PHT}) (PF : {PFT}) (QH : {QHT}) (QF : {QFT}) "
    f"(h0 : {H0T}) (h1 : {H1T}) (h2 : {H2T}) "
    f"(hp1 : forall (p : Nat) (q : Nat) (mem : {MEMT}) (na : Nat), PT p q mem na -> PH p {HB_M} (Nat.succ na)) "
    f"(hp2 : forall (p : Nat) (q : Nat) (mem : {MEMT}) (na : Nat) (mem1 : {MEMT}) (na1 : Nat) (vs1 : {VST}), "
    f"PT p q mem na -> QH p {HB_M} (Nat.succ na) mem1 na1 vs1 -> PF p q mem1 na1) "
    f"(hq1 : forall (p : Nat) (mem : {MEMT}) (na : Nat), PH p mem na -> {hq1_ty('p', 'mem', 'na')}) "
    f"(hq2 : forall (p : Nat) (q : Nat) (mem : {MEMT}) (na : Nat), PT p q mem na -> {hq2_ty('p', 'q', 'na', HB_M)}) "
    f"(hloc_hb : forall (n : Nat), ({ih_ty('n')}) -> forall (p : Nat) (mem : {MEMT}) (na : Nat), "
    f"PH p mem na -> {ctr('(ir_it_hb_entry g1 p mem na)', '(QH p mem na)', '(Nat.succ n)')}) "
    f"(hloc_fast : forall (n : Nat), ({ih_ty('n')}) -> forall (p : Nat) (q : Nat) (mem : {MEMT}) (na : Nat), "
    f"PF p q mem na -> {ctr('(ir_it_fast_entry g2 p q mem na)', '(QF p q mem na)', '(Nat.succ n)')}) "
)
ARGS = "fs gs g1 g2 PT PH PF QH QF h0 h1 h2 hp1 hp2 hq1 hq2 hloc_hb hloc_fast"


def local_obligation() -> str:
    succ_n = "(Nat.succ n)"
    hbm = HB_M
    motive = (f"(fun (x0 : IRItIn) => ir_it_in_pre PT PH PF x0 -> {in_ctr('x0', succ_n)})")
    hq1s = (f"(fun (mem1 : {MEMT}) (na1 : Nat) (vs : {VST}) (h : QH p {hbm} (Nat.succ na) mem1 na1 vs) => "
            f"hq1 p {hbm} (Nat.succ na) (hp1 p q mem na pt) mem1 na1 vs h)")
    hq2s = "(hq2 p q mem na pt)"
    ihh = (f"(ih (IRItIn.hb p {hbm} (Nat.succ na)) "
           f"(LiftP.up (PH p {hbm} (Nat.succ na)) (hp1 p q mem na pt)))")
    ihf = (f"(fun (mem1 : {MEMT}) (na1 : Nat) (vs1 : {VST}) (h : QH p {hbm} (Nat.succ na) mem1 na1 vs1) => "
           f"ih (IRItIn.fast p q mem1 na1) (LiftP.up (PF p q mem1 na1) (hp2 p q mem na mem1 na1 vs1 pt h)))")
    top = (
        f"(fun (p : Nat) (q : Nat) (mem : {MEMT}) (na : Nat) (lp : LiftP (PT p q mem na)) => "
        f"LiftP.rec (PT p q mem na) (fun (_ : LiftP (PT p q mem na)) => "
        f"{ctr('(ir_it_ag_entry p q mem na)', '(ir_it_tpost QH QF p q mem na)', succ_n)}) "
        f"(fun (pt : PT p q mem na) => ir_it_top_sseg fs gs g1 g2 QH QF p q mem na n h0 h1 h2 "
        f"{hq1s} {hq2s} {ihh} {ihf}) lp)"
    )
    hb = (
        f"(fun (p : Nat) (mem : {MEMT}) (na : Nat) (lp : LiftP (PH p mem na)) => "
        f"LiftP.rec (PH p mem na) (fun (_ : LiftP (PH p mem na)) => "
        f"{ctr('(ir_it_hb_entry g1 p mem na)', '(QH p mem na)', succ_n)}) "
        f"(fun (ph : PH p mem na) => hloc_hb n ih p mem na ph) lp)"
    )
    fast = (
        f"(fun (p : Nat) (q : Nat) (mem : {MEMT}) (na : Nat) (lp : LiftP (PF p q mem na)) => "
        f"LiftP.rec (PF p q mem na) (fun (_ : LiftP (PF p q mem na)) => "
        f"{ctr('(ir_it_fast_entry g2 p q mem na)', '(QF p q mem na)', succ_n)}) "
        f"(fun (pf : PF p q mem na) => hloc_fast n ih p q mem na pf) lp)"
    )
    return (
        f"def ir_it_local {PARAMS}(n : Nat) (ih : {ih_ty('n')}) : forall (x : IRItIn), "
        f"ir_it_in_pre PT PH PF x -> {in_ctr('x', succ_n)} := fun (x : IRItIn) => "
        f"IRItIn.rec {motive} {top} {hb} {fast} x"
    )


def group_ctr() -> str:
    return (
        f"def ir_it_ctr {PARAMS}(n : Nat) : {ih_ty('n')} := "
        f"ir_ctr_group_sound {M} IRItIn (ir_it_in_pre PT PH PF) (ir_it_in_entry g1 g2) "
        f"(ir_it_in_post QH QF) (ir_it_local {ARGS}) n"
    )


H0M = "(ir_mem_concat (ir_globals_mem gs) mem0)"
ARGS2 = "(ir_vl2 (IRScalar.ptr_ p) (IRScalar.ptr_ q))"


def eval_at(fuel: str) -> str:
    return f"(ir_eval {fuel} {M} ir_d0 {ARGS2} mem0 na)"


def tpost0(qh: str = "QH", qf: str = "QF") -> str:
    return f"(ir_it_tpost {qh} {qf} p q {H0M} na)"


def partial_correctness() -> str:
    tp = tpost0()
    initm = run(f"(IRMachine.mk (IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 Nat.zero (ir_bind_params "
                f"(ir_nl2 ir_d0 ir_d1) {ARGS2} (IRList.nil IRBinding)) (IRList.nil Nat)) "
                f"(IRList.nil IRFrame)) {H0M} na)")
    init = f"(ir_init {M} ir_d0 {ARGS2} mem0 na)"
    hq = (f"(fun (mem2 : {MEMT}) (na2 : Nat) (vs : {VST}) (h : {tp} mem2 na2 vs) => "
          f"fun (C : Prop) (k : forall (m3 : {MEMT}) (n3 : Nat), {tp} m3 n3 vs -> C) => k mem2 na2 h)")
    body = (
        f"ir_ctr_run {M} (ir_it_ag_entry p q {H0M} na) {tp} fuel "
        f"(ir_it_ctr {ARGS} fuel (IRItIn.top p q {H0M} na) (LiftP.up (PT p q {H0M} na) pt)) "
        f"(ir_ret_post {tp}) (IRList.nil Nat) {hq}"
    )
    return (
        f"def ir_it_pc {PARAMS}(p : Nat) (q : Nat) (mem0 : {MEMT}) (na : Nat) "
        f"(pt : PT p q {H0M} na) (fuel : Nat) : ir_it_pc_ok {tp} {eval_at('fuel')} := "
        f"Eq.subst IRConfig (fun (c : IRConfig) => ir_it_pc_ok {tp} (ir_run fuel {M} c)) {initm} {init} "
        f"(Eq.symm IRConfig {init} {initm} (ir_it_ag_init fs gs p q mem0 na h0)) ({body})"
    )


PC_BINDERS = f"{PARAMS}(p : Nat) (q : Nat) (mem0 : {MEMT}) (na : Nat) (pt : PT p q {H0M} na) (fuel : Nat) "
PC_ARGS = f"{ARGS} p q mem0 na pt fuel"


def no_bad_halt() -> str:
    o = eval_at("fuel")
    return (
        f"def ir_it_pc_no_bad_halt {PC_BINDERS}(hbad : Eq Bool (ir_bad_halt {o}) Bool.true) (C : Prop) : C := "
        f"ir_it_pc_ok_bad {tpost0()} {o} hbad (ir_it_pc {PC_ARGS}) C"
    )


def never_unreachable() -> str:
    o = eval_at("fuel")
    return (
        f"def ir_it_pc_never_unreachable {PC_BINDERS}(h : Eq IROutcome {o} (IROutcome.ub IRFault.unreachable)) "
        f"(C : Prop) : C := ir_it_pc_no_bad_halt {PC_ARGS} "
        f"(Eq.subst IROutcome (fun (o : IROutcome) => Eq Bool (ir_bad_halt o) Bool.true) "
        f"(IROutcome.ub IRFault.unreachable) {o} (Eq.symm IROutcome {o} (IROutcome.ub IRFault.unreachable) h) "
        f"(Eq.refl Bool Bool.true)) C"
    )


# ------------------------------------------- the table at the EXACT premises
#
# ir_it_ag_correct's premises are two EXACT callee runs and a slot fact. The
# table is instantiated with Leibniz-point preconditions (ir_it_at3/4) and the
# exact posts (ir_it_xqh/xqf); every premise of ir_it_pc is DERIVED from them,
# and the callees' local obligations come from ir_ctr_exact, ignoring the group
# hypothesis (an exact run needs none).

AG_BINDERS = (
    f"(fs : IRList IRFunc) (gs : IRList IRGlobal) (g1 : IRFunc) (g2 : IRFunc) (p : Nat) (q : Nat) "
    f"(mem0 : {MEMT}) (na : Nat) (c1 : Nat) (mem1 : {MEMT}) (na1 : Nat) (sp : IRScalar) (c2 : Nat) "
    f"(mem2 : {MEMT}) (na2 : Nat) (v0 : IRScalar) (spv : IRScalar) (fuel : Nat) "
    f"(h0 : {H0T}) (h1 : {H1T}) (h2 : {H2T}) "
    f"(hc1 : forall (d : IRList Nat) (r : IRList IRFrame), Eq IRConfig (ir_steps c1 {M} (IRConfig.running "
    f"(IRMachine.mk (IRList.cons IRFrame (IRFrame.mk (ir_func_id g1) (ir_func_entry g1) Nat.zero "
    f"(ir_bind_params (ir_func_params g1) (ir_vl1 (IRScalar.ptr_ p)) (IRList.nil IRBinding)) d) r) "
    f"(IRList.cons IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true) {H0M}) (Nat.succ na)))) "
    f"(ir_ret_to d r mem1 na1 (ir_vl1 (ir_it_hb_answer sp)))) "
    f"(hc2 : forall (d : IRList Nat) (r : IRList IRFrame), Eq IRConfig (ir_steps c2 {M} (IRConfig.running "
    f"(IRMachine.mk (IRList.cons IRFrame (IRFrame.mk (ir_func_id g2) (ir_func_entry g2) Nat.zero "
    f"(ir_bind_params (ir_func_params g2) (ir_vl2 (IRScalar.ptr_ p) (IRScalar.ptr_ q)) (IRList.nil IRBinding)) d) r) "
    f"mem1 na1))) (ir_ret_to d r mem2 na2 (ir_vl1 (IRScalar.aggv spv)))) "
    f"(hslot : Eq (IROption IRMemSlot) (ir_mem_lookup mem2 na) (IROption.some IRMemSlot (IRMemSlot.mk na v0 Bool.true))) "
)
AG_ARGS = "fs gs g1 g2 p q mem0 na c1 mem1 na1 sp c2 mem2 na2 v0 spv fuel h0 h1 h2 hc1 hc2 hslot"

HB0 = hb_heap(H0M, "na")
XPT = f"(ir_it_at4 p q {H0M} na)"
XPH = f"(ir_it_at3 p {HB0} (Nat.succ na))"
XPF = "(ir_it_at4 p q mem1 na1)"
XQH = "(ir_it_xqh mem1 na1 sp)"
XQF = "(ir_it_xqf mem2 na2 spv)"
XTP = f"(ir_it_tpost {XQH} {XQF} p q {H0M} na)"


def x_ih_ty(n: str) -> str:
    return (f"forall (a : IRItIn), ir_it_in_pre {XPT} {XPH} {XPF} a -> "
            f"ir_ctr_at {M} (ir_it_in_entry g1 g2 a) (ir_it_in_post {XQH} {XQF} a) {n}")


def of_exact() -> str:
    hbx = hb_heap("m", "k")
    hp1 = (
        f"(fun (a : Nat) (b : Nat) (m : {MEMT}) (k : Nat) (pt0 : ir_it_at4 p q {H0M} na a b m k) "
        f"(R : Nat -> {MEMT} -> Nat -> Prop) (r : R p {HB0} (Nat.succ na)) => "
        f"pt0 (fun (a0 : Nat) (b0 : Nat) (m0 : {MEMT}) (k0 : Nat) => "
        f"R a0 {hb_heap('m0', 'k0')} (Nat.succ k0)) r)"
    )
    hp2 = (
        f"(fun (a : Nat) (b : Nat) (m : {MEMT}) (k : Nat) (m1 : {MEMT}) (k1 : Nat) (w1 : {VST}) "
        f"(pt0 : ir_it_at4 p q {H0M} na a b m k) (hqh : ir_it_xqh mem1 na1 sp a {hbx} (Nat.succ k) m1 k1 w1) "
        f"(R : Nat -> Nat -> {MEMT} -> Nat -> Prop) (r : R p q mem1 na1) => "
        f"pt0 (fun (a0 : Nat) (b0 : Nat) (m0 : {MEMT}) (k0 : Nat) => R a0 b0 m1 k1) "
        f"(hqh (fun (m9 : {MEMT}) (k9 : Nat) (_ : {VST}) => R p q m9 k9) r))"
    )
    hq1 = (
        f"(fun (a : Nat) (m : {MEMT}) (k : Nat) (_ : ir_it_at3 p {HB0} (Nat.succ na) a m k) "
        f"(m1 : {MEMT}) (k1 : Nat) (vs : {VST}) (hqh : ir_it_xqh mem1 na1 sp a m k m1 k1 vs) "
        f"(C : Prop) (kk : forall (sp0 : IRScalar), Eq {VSTA} vs {hbans('sp0')} -> C) => "
        f"kk sp (hqh (fun (_ : {MEMT}) (_ : Nat) (v : {VST}) => Eq {VSTA} v {hbans('sp')}) "
        f"(Eq.refl {VSTA} {hbans('sp')})))"
    )
    look_k = f"Eq {SLOTA} (ir_mem_lookup m9 k) (IROption.some IRMemSlot (IRMemSlot.mk k v0 Bool.true))"
    hq2 = (
        f"(fun (a : Nat) (b : Nat) (m : {MEMT}) (k : Nat) (pt0 : ir_it_at4 p q {H0M} na a b m k) "
        f"(m1 : {MEMT}) (k1 : Nat) (w1 : {VST}) (m2 : {MEMT}) (k2 : Nat) (vs : {VST}) "
        f"(_ : ir_it_xqh mem1 na1 sp a {hbx} (Nat.succ k) m1 k1 w1) "
        f"(hqf : ir_it_xqf mem2 na2 spv a b m1 k1 m2 k2 vs) "
        f"(C : Prop) (kk : forall (spv0 : IRScalar) (v00 : IRScalar), Eq {VSTA} vs {aggv('spv0')} -> "
        f"{lookup_live('m2', 'k', 'v00')} -> C) => "
        f"kk spv v0 (hqf (fun (_ : {MEMT}) (_ : Nat) (v : {VST}) => Eq {VSTA} v {aggv('spv')}) "
        f"(Eq.refl {VSTA} {aggv('spv')})) "
        f"(hqf (fun (m9 : {MEMT}) (_ : Nat) (_ : {VST}) => {look_k}) "
        f"(pt0 (fun (_ : Nat) (_ : Nat) (_ : {MEMT}) (d9 : Nat) => "
        f"{lookup_live('mem2', 'd9', 'v0')}) hslot)))"
    )
    xh_post = f"(ir_post_exact mem1 na1 {hbans('sp')})"
    xf_post = f"(ir_post_exact mem2 na2 {aggv('spv')})"
    hloc_hb = (
        f"(fun (n : Nat) (_ : {x_ih_ty('n')}) (a : Nat) (m : {MEMT}) (k : Nat) "
        f"(ph : ir_it_at3 p {HB0} (Nat.succ na) a m k) => "
        f"ph (fun (a0 : Nat) (m0 : {MEMT}) (k0 : Nat) => "
        f"{ctr('(ir_it_hb_entry g1 a0 m0 k0)', xh_post, '(Nat.succ n)')}) "
        f"(ir_ctr_exact {M} (ir_it_hb_entry g1 p {HB0} (Nat.succ na)) c1 mem1 na1 {hbans('sp')} hc1 (Nat.succ n)))"
    )
    hloc_fast = (
        f"(fun (n : Nat) (_ : {x_ih_ty('n')}) (a : Nat) (b : Nat) (m : {MEMT}) (k : Nat) "
        f"(pf : ir_it_at4 p q mem1 na1 a b m k) => "
        f"pf (fun (a0 : Nat) (b0 : Nat) (m0 : {MEMT}) (k0 : Nat) => "
        f"{ctr('(ir_it_fast_entry g2 a0 b0 m0 k0)', xf_post, '(Nat.succ n)')}) "
        f"(ir_ctr_exact {M} (ir_it_fast_entry g2 p q mem1 na1) c2 mem2 na2 {aggv('spv')} hc2 (Nat.succ n)))"
    )
    pt0 = (f"(fun (R : Nat -> Nat -> {MEMT} -> Nat -> Prop) (r : R p q {H0M} na) => r)")
    return (
        f"def ir_it_pc_of_exact {AG_BINDERS}: ir_it_pc_ok {XTP} {eval_at('fuel')} := "
        f"ir_it_pc fs gs g1 g2 {XPT} {XPH} {XPF} {XQH} {XQF} h0 h1 h2 "
        f"{hp1} {hp2} {hq1} {hq2} {hloc_hb} {hloc_fast} p q mem0 na {pt0} fuel"
    )


def crosscheck() -> str:
    o = eval_at("fuel")
    ret = f"(IROutcome.ret {aggv('spv')})"
    goal = f"Eq IROutcome {o} {ret}"
    k = (
        f"(fun (vs : {VST}) (m3 : {MEMT}) (n3 : Nat) (he : Eq IROutcome {o} (IROutcome.ret vs)) "
        f"(ht : {XTP} m3 n3 vs) => ht ({goal}) "
        f"(fun (m1 : {MEMT}) (k1 : Nat) (w1 : {VST}) (m2 : {MEMT}) "
        f"(_ : {XQH} p {HB0} (Nat.succ na) m1 k1 w1) (hf : {XQF} p q m1 k1 m2 n3 vs) => "
        f"Eq.trans IROutcome {o} (IROutcome.ret vs) {ret} he "
        f"(ir_eq_cong {VSTA} IROutcome IROutcome.ret vs {aggv('spv')} "
        f"(Eq.symm {VSTA} {aggv('spv')} vs (hf (fun (_ : {MEMT}) (_ : Nat) (v : {VST}) => "
        f"Eq {VSTA} {aggv('spv')} v) (Eq.refl {VSTA} {aggv('spv')}))))))"
    )
    return (
        f"def ir_it_pc_a4_crosscheck {AG_BINDERS}"
        f"(hle : Le (Nat.add (Nat.add (Nat.add (Nat.add ir_d4 c2) ir_d4) c1) ir_d2) fuel) : {goal} := "
        f"ir_it_pc_ok_is_ret {XTP} {o} (ir_it_pc_of_exact {AG_ARGS}) "
        f"(ir_it_ag_returns {AG_ARGS} hle) ({goal}) {k}"
    )


def ag_returns() -> str:
    """ONLY termination, from the structural chain: the run at fuel >= cost is a ret."""
    o = eval_at("fuel")
    return (
        f"def ir_it_ag_returns {AG_BINDERS}"
        f"(hle : Le (Nat.add (Nat.add (Nat.add (Nat.add ir_d4 c2) ir_d4) c1) ir_d2) fuel) : "
        f"Eq Bool (ir_outcome_is_ret {o}) Bool.true := "
        f"ir_eq_cong IROutcome Bool ir_outcome_is_ret {o} (IROutcome.ret {aggv('spv')}) "
        f"(ir_it_ag_correct {AG_ARGS} hle)"
    )


# ------------------------------------------------ non-vacuity at ir_itd_module
#
# The premises are INHABITED: at the module that carries the two authored models
# (ir_itb_hb, ir_itd_fast) every premise of ir_it_pc_of_exact is discharged by
# the structural chain's own witnesses (ir_it_ag_*_at_itd), exactly the arguments
# ir_it_ag_witness_eval passes to ir_it_ag_correct.

ITD_M = "(IRModule.mk (ir_it_ag_itd_fs spc) (IRList.nil IRGlobal))"
ITD_H0 = "(ir_mem_concat (ir_globals_mem (IRList.nil IRGlobal)) ir_mem0)"
ITD_M1 = f"(IRList.cons IRMemSlot (IRMemSlot.mk ir_d7 IRScalar.undef_ Bool.true) {ITD_H0})"


def itd_args(fuel: str) -> str:
    return (
        f"(ir_it_ag_itd_fs spc) (IRList.nil IRGlobal) ir_itb_hb (ir_itd_fast spc) p q ir_mem0 ir_d7 "
        f"ir_d2 {ITD_M1} (Nat.succ ir_d7) ir_it_ag_itd_hbsp ir_d2 {ITD_M1} (Nat.succ ir_d7) "
        f"IRScalar.undef_ (ir_it_ag_itd_spv spc) {fuel} (ir_it_ag_h0_at_itd spc) (ir_it_ag_h1_at_itd spc) "
        f"(ir_it_ag_h2_at_itd spc) (ir_it_ag_hc1_at_itd spc p {ITD_H0} ir_d7) "
        f"(ir_it_ag_hc2_at_itd spc p q {ITD_M1} (Nat.succ ir_d7)) (ir_it_ag_hslot_at_itd {ITD_H0})"
    )


def itd_eval(fuel: str) -> str:
    return f"(ir_eval {fuel} {ITD_M} ir_d0 {ARGS2} ir_mem0 ir_d7)"


def witness_itd() -> str:
    tp = (f"(ir_it_tpost (ir_it_xqh {ITD_M1} (Nat.succ ir_d7) ir_it_ag_itd_hbsp) "
          f"(ir_it_xqf {ITD_M1} (Nat.succ ir_d7) (ir_it_ag_itd_spv spc)) p q {ITD_H0} ir_d7)")
    return (
        f"def ir_it_pc_witness_itd (spc : IRConst) (p : Nat) (q : Nat) (fuel : Nat) : "
        f"ir_it_pc_ok {tp} {itd_eval('fuel')} := ir_it_pc_of_exact {itd_args('fuel')}"
    )


def crosscheck_itd() -> str:
    return (
        f"def ir_it_pc_crosscheck_itd (spc : IRConst) (p : Nat) (q : Nat) : "
        f"Eq IROutcome {itd_eval('ir_d14')} (IROutcome.ret (ir_vl1 (IRScalar.aggv (ir_it_ag_itd_spv spc)))) := "
        f"ir_it_pc_a4_crosscheck {itd_args('ir_d14')} (Le.refl ir_d14)"
    )


# The body's obligation mints a FAMILY -- its resume segments, then the
# obligation -- in registration order; every other term is one declaration.
FAMILIES = (top_sseg,)
SINGLES = {
    "SRC_IR_IT_LOCAL": local_obligation,
    "SRC_IR_IT_CTR": group_ctr,
    "SRC_IR_IT_PC": partial_correctness,
    "SRC_IR_IT_PC_NO_BAD_HALT": no_bad_halt,
    "SRC_IR_IT_PC_NEVER_UNREACHABLE": never_unreachable,
    "SRC_IR_IT_PC_OF_EXACT": of_exact,
    "SRC_IR_IT_AG_RETURNS": ag_returns,
    "SRC_IR_IT_PC_A4_CROSSCHECK": crosscheck,
    "SRC_IR_IT_PC_WITNESS_ITD": witness_itd,
    "SRC_IR_IT_PC_CROSSCHECK_ITD": crosscheck_itd,
}


def const_of(name: str) -> str:
    return "SRC_" + name.upper()


def minted() -> dict:
    """Every emitted term, const name -> source, in registration order."""
    out = {}
    for family in FAMILIES:
        for name, src in family():
            out[const_of(name)] = src
    for k, f in SINGLES.items():
        out[k] = f()
    return out


# The NESTED obligation the kernel accepted on 2026-09-24 (E2's second
# instance), before it was minted one lemma per call. With `SEGMENTED = False`
# the emitter must still reproduce it byte for byte.
LEGACY_DIGESTS: dict = {
    "SRC_IR_IT_TOP_SSEG": "4eddbc168469597859ac0d7d39664bab85c50077dc5e5d328ddfcddae62202a6",
}


def legacy() -> dict:
    """The nested obligation, as the 2026-09-24 emitter wrote it."""
    global SEGMENTED
    keep = SEGMENTED
    SEGMENTED = False
    try:
        out = {}
        for family in FAMILIES:
            fam = family()
            assert len(fam) == 1, "the nested form mints no segments"
            out[const_of(fam[0][0])] = fam[0][1]
        return out
    finally:
        SEGMENTED = keep


# The terms a kernel accepted. `--self-test` recomputes them and compares these
# digests, so a refactor that changes the emitted SHAPE fails in a second
# rather than in a spec build.
PINNED_DIGESTS: dict = {
    "SRC_IR_IT_AG_RETURNS": "4b014c9805c8749485edad4822180c180b2c8586fad28e26fecbd65eb582cf3e",
    "SRC_IR_IT_CTR": "ea8f2216355f7c6efbd1b73aa9135960060e5c37d9525c96598452e7de536fd5",
    "SRC_IR_IT_LOCAL": "69468aaa2c5fcf17960099ecb2d42b232482d71000f0eb23ddc241c2e9d58946",
    "SRC_IR_IT_PC": "cc882da5fd030449dc9d21ce06d8ef27d8d2565bf33cd1073d5da25f2817def5",
    "SRC_IR_IT_PC_A4_CROSSCHECK": "1f6a24bdb65046575424e48f7a6b1f92d4fb370073baeea10c8f0e7a94dcc3c3",
    "SRC_IR_IT_PC_CROSSCHECK_ITD": "db4b38aa928159fc7517412dd02d9ce690ab2992019ae411485a2f4a845335bd",
    "SRC_IR_IT_PC_NEVER_UNREACHABLE": "6ce26c8aee6a167bfcd8c0ce62e0f5c7d80cc543afece990021ec03d7ca94bdc",
    "SRC_IR_IT_PC_NO_BAD_HALT": "89c4557fa57e0046dcd3daaa626cd43f19b2a70f028bb1e6efe687088da1e82a",
    "SRC_IR_IT_PC_OF_EXACT": "04ee2f5a48d23eadf880468d4e9d33369ceb308e0f2c1f1ea508017e6aa79588",
    "SRC_IR_IT_PC_WITNESS_ITD": "c534819580c076e8238baff6dfeef0db199c84221feaab0e29169273b35ff630",
    "SRC_IR_IT_TOP_SSEG": "0ab4844557ecf39b2aae2c87483c446060246df93a35185adc0baea96a35fbe8",
    "SRC_IR_IT_TOP_SSEG_R1": "cef3494760df61c48ebce0ef8a61ec32b1b168557f671ac1cdaf942048ef4934",
    "SRC_IR_IT_TOP_SSEG_R2": "338c42a61c7216947b3eacc89a2d6b49c9778d6536633cce6c3b478530d781dc",
}


def committed() -> dict:
    found = {}
    for f in TARGETS:
        found.update(dict(re.findall(r'const (SRC_[A-Z0-9_]+): &str = "(.*?)";\n',
                                     f.read_text(), re.S)))
    return found


def registration_order(built: dict) -> list:
    """Every minted const a target declares must be registered in its DECLS
    exactly once, and in minted order: a segment lemma before the lemma that
    applies it."""
    out = []
    for f in TARGETS:
        src = f.read_text()
        declared = set(re.findall(r'const (SRC_[A-Z0-9_]+): &str = "', src))
        decls = src[src.index("const DECLS"):]
        decls = decls[:decls.index("\n];")]  # the DECLS table only, never a test's own list
        order = re.findall(r"\(\s*\n\s*(SRC_[A-Z0-9_]+),", decls)
        for k in built:
            if k in declared and order.count(k) != 1:
                out.append(f"REGISTRATION: {k} is registered {order.count(k)} times in {f.name}")
        seq = [k for k in order if k in built]
        want = [k for k in built if k in seq]
        if seq != want:
            out.append(f"REGISTRATION ORDER: {f.name} registers {seq}; dependency order is {want}")
    return out


def digests(built: dict) -> dict:
    return {k: hashlib.sha256(v.encode()).hexdigest() for k, v in built.items()}


def _coverage_invariant(built: dict) -> list:
    out = []
    for k in sorted(set(built) - set(PINNED_DIGESTS)):
        out.append(f"UNPINNED: {k} is minted but has no pinned digest")
    for k in sorted(set(PINNED_DIGESTS) - set(built)):
        out.append(f"ORPHAN DIGEST: {k} is pinned but no emitter produces it")
    return out


def _ascii_balanced(built: dict) -> list:
    out = []
    for k, v in built.items():
        if not v.isascii():
            out.append(f"NON-ASCII: {k}")
        if v.count("(") != v.count(")"):
            out.append(f"UNBALANCED: {k}")
        if '"' in v or "\\" in v:
            out.append(f"UNESCAPED: {k} would need escaping inside a Rust string literal")
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--print", dest="name")
    ap.add_argument("--emit", action="store_true")
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--self-test", dest="selftest", action="store_true")
    ap.add_argument("--pin", action="store_true")
    ap.add_argument("--legacy", action="store_true",
                    help="with --print: the nested 2026-09-24 form")
    a = ap.parse_args()
    built = legacy() if a.legacy else minted()
    if a.name:
        key = a.name if a.name.startswith("SRC_") else "SRC_" + a.name.upper()
        print(built[key])
        return 0
    if a.emit:
        bad = _ascii_balanced(built)
        for line in bad:
            print(line)
        if bad:
            return 1
        n = 0
        for f in TARGETS:
            src = f.read_text()
            for k, v in built.items():
                pat = re.compile(r'const %s: &str = ".*?";\n' % k, re.S)
                if pat.search(src):
                    src = pat.sub(lambda _m, k=k, v=v: f'const {k}: &str = "{v}";\n', src)
                    n += 1
            f.write_text(src)
        print(f"emitted {n} terms")
        return 0 if n == len(built) else 1
    if a.pin:
        body = "PINNED_DIGESTS: dict = {\n" + "".join(
            f'    "{k}": "{v}",\n' for k, v in sorted(digests(built).items())) + "}"
        me = Path(__file__)
        me.write_text(re.sub(r"PINNED_DIGESTS: dict = \{.*?\}", body, me.read_text(),
                             count=1, flags=re.S))
        print(f"pinned {len(built)} digests")
        return 0
    if a.selftest:
        have = digests(built)
        bad = [k for k, v in PINNED_DIGESTS.items() if have.get(k) != v]
        old = digests(legacy())
        moved = [k for k, v in LEGACY_DIGESTS.items() if old.get(k) != v]
        drift = _coverage_invariant(built) + _ascii_balanced(built)
        for k in bad:
            print(f"DIGEST MOVED: {k}")
        for k in moved:
            print(f"LEGACY NOT REPRODUCED: {k} (the nested form the kernel accepted 2026-09-24)")
        for line in drift:
            print(line)
        ok = not bad and not moved and not drift
        print("gen_it_sctr --self-test: " + ("OK" if ok else "FAILED"))
        return 0 if ok else 1
    if a.check:
        have = committed()
        bad = [k for k in built if have.get(k) != built[k]]
        for k in bad:
            print(f"DIFFERS: {k}")
        order = registration_order(built)
        for line in order:
            print(line)
        print("gen_it_sctr: " + ("OK" if not bad and not order else f"{len(bad) + len(order)} differ"))
        return 1 if bad or order else 0
    ap.print_help()
    return 2


if __name__ == "__main__":
    sys.exit(main())
