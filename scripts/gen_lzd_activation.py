#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Mint the three `ir_lzd_*_seg` activation-segment proof terms.

The sibling of `gen_lzb_activation.py`, for the module with NO AUTHORED
FUNCTION in it. Same mechanical chain over a list of execution SEGMENTS —
literal runs the machine computes, opaque runs a lemma discharges — and two
differences, both forced by the bodies the compiler actually emits:

  * the deref is FORTY steps, not seven, because it is four real bodies rather
    than one seven-node model; and
  * every deref ALLOCATES, so a segment has a STATE (heap, counter) that
    changes as the chain proceeds. `gen_lzb_activation.py` could write
    `ir_ret_to dests rest mem na` everywhere; here each segment threads its own
    pair, and every hypothesis about the original heap is re-framed to the
    current one through `ir_lzd_lookup_ext` / `ir_lzd_ltb_ext`.

The state is a TRIPLE — heap, counter, and a `MemExt mem na <heap> <counter>`
witness — so the framing term is composed as the chain is built rather than
reconstructed afterwards.

The terms are built without explicit prefixes; that is the shape `--self-test`
and `--pin` digest. What the tree registers is that text printed by
`scripts/explicit_prefix.py` with `@` before the heads in `EXPLICIT_HEADS`, less
the ones a const's committed source keeps bare (`KEPT_BARE`), and `--print`,
`--emit` and `--check` speak the printed text.

USAGE
    python3 scripts/gen_lzd_activation.py --print <name>
    python3 scripts/gen_lzd_activation.py --emit    # rewrite the Rust consts
    python3 scripts/gen_lzd_activation.py --check   # byte-compare with the tree
"""

from __future__ import annotations

import argparse
import importlib.util
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

ANSWERS_PINNED_INPUTS = True
HELPER_INPUTS = ('scripts/test_generator_source_helpers.py', 'scripts/resource_transport.py', 'scripts/explicit_prefix.py', 'crates/clean-verify/src/spec/core_spec/eval_ir_lzd_activation.rs', 'crates/clean-verify/src/spec/core_spec/eval_ir_lzd_correct.rs')


def _source_module(name, path):
    """Execute pinned source bytes; an accepted pyc is not a declared input."""
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise ValueError('source helper unavailable: ' + str(path))
    module = importlib.util.module_from_spec(spec)
    exec(compile(path.read_bytes(), str(path), 'exec', dont_inherit=True), module.__dict__)
    return module


def _helper_source_controls():
    controls = _source_module('generator_source_controls', REPO / 'scripts/test_generator_source_helpers.py')
    controls.self_test_generator(Path(__file__).name)


XP = _source_module("explicit_prefix", REPO / "scripts/explicit_prefix.py")
ACTIVATION_RS = REPO / "crates/clean-verify/src/spec/core_spec/eval_ir_lzd_activation.rs"

M = "ir_lzd_module"
SLOT_TY = "(IROption IRMemSlot)"
MEM_TY = "(IRList IRMemSlot)"

# Steps in one activation of the DERIVED deref, from its frame push to the
# caller's resumption — `ir_lzd_deref_activation`. Four bodies: the kernel's
# own `<LevelArc as Deref>::deref`, and `as_deref`, `expect` and
# `<Arc<Level>>::deref` as the callee sidecar derived them.
DEREF_STEPS = "ir_d40"


def child_of(b: str) -> str:
    """The cell the recursive call runs at, given a field holding `ptr (succ b)`.

    The field holds the Arc ALLOCATION base; the child `Level` sits past the
    strong and weak counts, which is where `<Arc<T>>::deref` points. The
    successor is the niche: a live `Arc` pointer is never the zero word.
    """
    return f"(Nat.add (Nat.succ {b}) ir_d16)"


def opt_of(b: str) -> str:
    """What one deref leaves in the return slot it allocated."""
    return (
        "(IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons "
        f"(IRScalar.ptr_ {child_of(b)}) IRScalar.vnil)))"
    )


def steps(n: str, c: str) -> str:
    return f"(ir_steps {n} {M} {c})"


def nat_add(a: str, b: str) -> str:
    return f"(Nat.add {a} {b})"


def eq_cfg(lhs: str, rhs: str) -> str:
    return f"Eq IRConfig {lhs} {rhs}"


def ret_to(dests: str, rest: str, mem: str, na: str, val: str) -> str:
    return f"(ir_ret_to {dests} {rest} {mem} {na} {val})"


def frames_after(cfg: str) -> str:
    return f"(ir_frames_tail (ir_config_frames {cfg}))"


def bool_val(b: str) -> str:
    return f"(ir_vl1 (IRScalar.bool_ {b}))"


def ptr_val(p: str) -> str:
    return f"(ir_vl1 {p})"


def mem_at(addr: str, val: str) -> str:
    return (
        f"Eq (IROption IRMemSlot) (ir_mem_lookup mem {addr}) "
        f"(IROption.some IRMemSlot (IRMemSlot.mk {addr} {val} Bool.true))"
    )


def lt_at(addr: str) -> str:
    return f"Eq Bool (ir_nat_ltb {addr} na) Bool.true"


class State:
    """Heap, counter, and the proof that it extends the entry heap."""

    def __init__(self, mem: str, na: str, ext: str):
        self.mem, self.na, self.ext = mem, na, ext

    def framed_lookup(self, addr: str, val: str, hlt: str, h: str) -> str:
        """`h`, re-stated at this state's heap."""
        known = f"(IROption.some IRMemSlot (IRMemSlot.mk {addr} {val} Bool.true))"
        return (
            f"(Eq.trans {SLOT_TY} (ir_mem_lookup {self.mem} {addr}) (ir_mem_lookup mem {addr}) "
            f"{known} (ir_lzd_lookup_ext mem na {self.mem} {self.na} {self.ext} {addr} {hlt}) {h})"
        )

    def framed_lt(self, addr: str, hlt: str) -> str:
        return f"(ir_lzd_ltb_ext mem na {self.mem} {self.na} {self.ext} {addr} {hlt})"

    def framed_borrow(self, addr: str, hlt: str, hcb: str) -> str:
        """`hcb`, re-stated at this state's heap."""
        val = f"(IRStepResult.value (IRScalar.ptr_ {addr}))"
        return (
            f"(Eq.trans IRStepResult (ir_borrow_eval {self.mem} (IRScalar.ptr_ {addr})) "
            f"(ir_borrow_eval mem (IRScalar.ptr_ {addr})) {val} "
            f"(ir_lzd_borrow_ext mem na {self.mem} {self.na} {self.ext} {addr} {hlt}) {hcb})"
        )


ENTRY = State("mem", "na", "(MemExt.refl mem na)")


class Lit:
    """A literal run of steps the kernel computes through."""

    opaque = False

    def __init__(self, count: str):
        self.count = count

    def after(self, st: State) -> State:
        return st


class Deref:
    """One activation of the DERIVED deref, at a field cell. Allocates one cell."""

    opaque = True

    def __init__(self, field: str, dest: str, base: str, hlt: str, h: str,
                 hcl: str, hcb: str):
        self.count = DEREF_STEPS
        self.field, self.dest, self.base = field, dest, base
        self.hlt, self.h, self.hcl, self.hcb = hlt, h, hcl, hcb

    def after(self, st: State) -> State:
        mem2 = f"(ir_cell {st.na} {opt_of(self.base)} {st.mem})"
        na2 = f"(Nat.succ {st.na})"
        ext = (
            f"(ir_mem_ext_trans mem na {st.mem} {st.na} {st.ext} {mem2} {na2} "
            f"(ir_mem_ext_one {st.mem} {st.na} {opt_of(self.base)}))"
        )
        return State(mem2, na2, ext)

    def result(self, cfg: str, st: State) -> str:
        nx = self.after(st)
        return ret_to(
            f"(ir_nl1 {self.dest})", frames_after(cfg), nx.mem, nx.na,
            ptr_val(f"(IRScalar.ptr_ {child_of(self.base)})"),
        )

    def lemma(self, cfg: str, st: State) -> str:
        h = st.framed_lookup(self.field, f"(IRScalar.ptr_ (Nat.succ {self.base}))",
                             self.hlt, self.h)
        ext = self.after(st)
        one = f"(ir_mem_ext_one {st.mem} {st.na} IRScalar.undef_)"
        cell0 = f"(ir_cell {st.na} IRScalar.undef_ {st.mem})"
        step = f"(ir_mem_ext_trans mem na {st.mem} {st.na} {st.ext} {cell0} (Nat.succ {st.na}) {one})"
        hcb = f"({self.hcb} {cell0} (Nat.succ {st.na}) {step})"
        return (
            f"(ir_lzd_deref_activation {st.mem} {self.field} {self.base} {st.na} "
            f"(ir_nl1 {self.dest}) {frames_after(cfg)} {st.framed_lt(self.field, self.hlt)} "
            f"{h} {hcb})"
        )


class Rec:
    """One activation of the body itself, discharged by a recursion hypothesis."""

    opaque = True

    def __init__(self, count: str, dest: str, answer: str, ih: str, out_mem: str,
                 out_na: str, out_ext: str):
        self.count, self.dest, self.answer, self.ih = count, dest, answer, ih
        self.out_mem, self.out_na, self.out_ext = out_mem, out_na, out_ext

    def after(self, st: State) -> State:
        ext = (
            f"(ir_mem_ext_trans mem na {st.mem} {st.na} {st.ext} {self.out_mem} "
            f"{self.out_na} {self.out_ext})"
        )
        return State(self.out_mem, self.out_na, ext)

    def result(self, cfg: str, st: State) -> str:
        return ret_to(f"(ir_nl1 {self.dest})", frames_after(cfg), self.out_mem,
                      self.out_na, bool_val(self.answer))

    def lemma(self, cfg: str, st: State) -> str:
        return f"({self.ih} (ir_nl1 {self.dest}) {frames_after(cfg)})"


def total(segs) -> str:
    expr = segs[-1].count
    for s in reversed(segs[:-1]):
        expr = nat_add(expr, s.count)
    return expr


def remaining(segs, i: int) -> str:
    return total(segs[i:])


def chain(segs, cfg: str, st: State, target: str) -> str:
    """The right-nested peel over `segs`, starting at config `cfg` in state `st`."""
    if len(segs) == 1:
        return f"(Eq.refl IRConfig {target})"
    head, rest = segs[0], segs[1:]
    after = remaining(segs, 1)
    stepped = steps(head.count, cfg)
    split = f"(ir_steps_add {M} {after} {head.count} {cfg})"
    if head.opaque:
        value = head.result(cfg, st)
        inner = chain(rest, value, head.after(st), target)
        body = (
            f"(Eq.subst IRConfig (fun (k : IRConfig) => {eq_cfg(steps(after, 'k'), target)}) "
            f"{value} {stepped} "
            f"(Eq.symm IRConfig {stepped} {value} {head.lemma(cfg, st)}) {inner})"
        )
    else:
        body = chain(rest, stepped, head.after(st), target)
    return (
        f"(Eq.trans IRConfig {steps(remaining(segs, 0), cfg)} {steps(after, stepped)} "
        f"{target} {split} {body})"
    )


def segment_lemma(name: str, binders: str, hyps: str, slot: str, segs, target: str) -> str:
    """One `ir_lzd_*_seg` declaration, statement and proof."""
    load, rest = segs[0], segs[1:]
    assert not load.opaque, "the first segment is the body's load"
    shortened = int(load.count[len("ir_d"):]) - 1
    body_segs = [Lit(f"ir_d{shortened}")] + rest

    stmt_cost = total([load] + rest)
    motive_cost = total(body_segs)
    cfg0 = "(ir_lzd_after_load mem a na dests rest o)"
    cfg_slot = f"(ir_lzd_after_load mem a na dests rest {slot})"
    lookup = "(ir_mem_lookup mem a)"

    proof = (
        f"Eq.subst {SLOT_TY} "
        f"(fun (o : {SLOT_TY}) => {eq_cfg(steps(motive_cost, cfg0), target)}) "
        f"{slot} {lookup} "
        f"(Eq.symm {SLOT_TY} {lookup} {slot} h) "
        f"{chain(body_segs, cfg_slot, ENTRY, target)}"
    )
    concl = eq_cfg(
        steps(stmt_cost,
              "(IRConfig.running (ir_lzd_mach0_s mem (IRScalar.ptr_ a) na dests rest))"),
        target,
    )
    return f"def {name} {binders}{hyps}: {concl} := {proof}"


def ih_hyp(name: str, cost: str, base: str, answer: str, st: State, out_mem: str,
           out_na: str) -> str:
    """A recursion hypothesis at ONE heap and counter, generic in the caller."""
    return (
        f"({name} : forall (d2 : IRList Nat) (r2 : IRList IRFrame), "
        + eq_cfg(
            steps(cost,
                  f"(IRConfig.running (ir_lzd_mach0_s {st.mem} (IRScalar.ptr_ {child_of(base)}) "
                  f"{st.na} d2 r2))"),
            ret_to("d2", "r2", out_mem, out_na, bool_val(answer)),
        )
        + ") "
    )


def slot_of(tag: str) -> str:
    pair = "(ir_sp2 (IRScalar.ptr_ (Nat.succ b1)) (IRScalar.ptr_ (Nat.succ b2)))"
    return f"(IROption.some IRMemSlot (IRMemSlot.mk a (ir_var {tag} {pair}) Bool.true))"


PAIR = "(ir_sp2 (IRScalar.ptr_ (Nat.succ b1)) (IRScalar.ptr_ (Nat.succ b2)))"
MAX_SLOT = slot_of("ir_d2")
IMAX_SLOT = slot_of("ir_d3")

def common(tag: str, with_first: bool) -> str:
    """The hypotheses a two-child segment lemma takes.

    `with_first` is FALSE for imax, and that is a measurement rather than a
    taste: `Level::is_zero`'s imax path (block 5 of the committed core) geps
    ONLY +16, because `level_is_zero (imax l1 l2)` is `level_is_zero l2` and the
    left child is never read. The three premises dropped here -- the +8 cell,
    its bound, and the left child's borrow -- were passed in and used ZERO
    times, measured by counting their occurrences in the emitted body.
    """
    first = (
        f"(h8 : {mem_at(nat_add('a', 'ir_d8'), '(IRScalar.ptr_ (Nat.succ b1))')}) "
        if with_first else ""
    )
    first_lt = f"(hlt8 : {lt_at(nat_add('a', 'ir_d8'))}) " if with_first else ""
    first_cb = (
        f"(hcb1 : forall (mx : IRList IRMemSlot) (nx : Nat), MemExt mem na mx nx -> "
        f"Eq IRStepResult (ir_borrow_eval mx (IRScalar.ptr_ {child_of('b1')})) "
        f"(IRStepResult.value (IRScalar.ptr_ {child_of('b1')}))) "
        if with_first else ""
    )
    return (
        f"(h : {mem_at('a', f'(ir_var {tag} {PAIR})')}) "
        + first
        + f"(h16 : {mem_at(nat_add('a', 'ir_d16'), '(IRScalar.ptr_ (Nat.succ b2))')}) "
        + first_lt
        + f"(hlt16 : {lt_at(nat_add('a', 'ir_d16'))}) "
        + first_cb
        + f"(hcb2 : forall (mx : IRList IRMemSlot) (nx : Nat), MemExt mem na mx nx -> "
        f"Eq IRStepResult (ir_borrow_eval mx (IRScalar.ptr_ {child_of('b2')})) "
        f"(IRStepResult.value (IRScalar.ptr_ {child_of('b2')}))) "
    )


def max_true_seg() -> str:
    d1 = Deref(nat_add("a", "ir_d8"), "ir_d12", "b1", "hlt8", "h8", "hcl1", "hcb1")
    s1 = d1.after(ENTRY)
    r1 = Rec("c1", "ir_d13", "Bool.true", "ih1", "mA", "nA",
             f"(ir_mem_ext_trans mem na {s1.mem} {s1.na} {s1.ext} mA nA eA)")
    # `eA` relates s1 to (mA, nA); the composed witness above is what `after`
    # would build, so hand `Rec` the RAW one and let it compose.
    r1 = Rec("c1", "ir_d13", "Bool.true", "ih1", "mA", "nA", "eA")
    s2 = r1.after(s1)
    d2 = Deref(nat_add("a", "ir_d16"), "ir_d18", "b2", "hlt16", "h16", "hcl2", "hcb2")
    s3 = d2.after(s2)
    r2 = Rec("c2", "ir_d19", "ans2", "ih2", "mB", "nB", "eB")
    segs = [Lit("ir_d8"), d1, Lit("ir_d1"), r1, Lit("ir_d2"), d2, Lit("ir_d1"), r2, Lit("ir_d3")]
    binders = (
        f"(mem : {MEM_TY}) (a : Nat) (b1 : Nat) (b2 : Nat) "
        f"(c1 : Nat) (c2 : Nat) (ans2 : Bool) (na : Nat) (dests : IRList Nat) "
        f"(rest : IRList IRFrame) (mA : {MEM_TY}) (nA : Nat) (mB : {MEM_TY}) (nB : Nat) "
    )
    hyps = (
        common("ir_d2", True)
        + f"(eA : MemExt {s1.mem} {s1.na} mA nA) "
        + f"(eB : MemExt {s3.mem} {s3.na} mB nB) "
        + ih_hyp("ih1", "c1", "b1", "Bool.true", s1, "mA", "nA")
        + ih_hyp("ih2", "c2", "b2", "ans2", s3, "mB", "nB")
    )
    return segment_lemma("ir_lzd_max_true_seg", binders, hyps, MAX_SLOT, segs,
                         ret_to("dests", "rest", "mB", "nB", bool_val("ans2")))


def max_false_seg() -> str:
    d1 = Deref(nat_add("a", "ir_d8"), "ir_d12", "b1", "hlt8", "h8", "hcl1", "hcb1")
    s1 = d1.after(ENTRY)
    r1 = Rec("c1", "ir_d13", "Bool.false", "ih1", "mA", "nA", "eA")
    segs = [Lit("ir_d8"), d1, Lit("ir_d1"), r1, Lit("ir_d5")]
    binders = (
        f"(mem : {MEM_TY}) (a : Nat) (b1 : Nat) (b2 : Nat) "
        f"(c1 : Nat) (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame) "
        f"(mA : {MEM_TY}) (nA : Nat) "
    )
    hyps = (
        common("ir_d2", True)
        + f"(eA : MemExt {s1.mem} {s1.na} mA nA) "
        + ih_hyp("ih1", "c1", "b1", "Bool.false", s1, "mA", "nA")
    )
    return segment_lemma("ir_lzd_max_false_seg", binders, hyps, MAX_SLOT, segs,
                         ret_to("dests", "rest", "mA", "nA", bool_val("Bool.false")))


def imax_seg() -> str:
    d2 = Deref(nat_add("a", "ir_d16"), "ir_d16", "b2", "hlt16", "h16", "hcl2", "hcb2")
    s1 = d2.after(ENTRY)
    r2 = Rec("c2", "ir_d17", "ans2", "ih2", "mA", "nA", "eA")
    segs = [Lit("ir_d6"), d2, Lit("ir_d1"), r2, Lit("ir_d2")]
    binders = (
        f"(mem : {MEM_TY}) (a : Nat) (b1 : Nat) (b2 : Nat) "
        f"(c2 : Nat) (ans2 : Bool) (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame) "
        f"(mA : {MEM_TY}) (nA : Nat) "
    )
    hyps = (
        common("ir_d3", False)
        + f"(eA : MemExt {s1.mem} {s1.na} mA nA) "
        + ih_hyp("ih2", "c2", "b2", "ans2", s1, "mA", "nA")
    )
    return segment_lemma("ir_lzd_imax_seg", binders, hyps, IMAX_SLOT, segs,
                         ret_to("dests", "rest", "mA", "nA", bool_val("ans2")))



# ------------------------------------------------- the derived deref, in full
#
# Seven rewrites, every one a heap operation the emitted code really performs.
# The two BORROWS are stated as `ir_borrow_eval` equations rather than as cell
# lookups, and that is not cosmetic: the representation relation is indexed by
# an IRScalar, not by an address, so "the cell at the child's address" is not a
# statement it can make about a general index — while `ir_borrow_eval mem s` is.
# `ir_lzd_live` produces exactly that form.

DCELL0 = "(ir_cell na IRScalar.undef_ mem)"
DK1 = "(IROption.some IRMemSlot (IRMemSlot.mk p (IRScalar.ptr_ (Nat.succ b)) Bool.true))"
DCA = "(Nat.add (Nat.succ b) ir_d16)"
DVAL = f"(IRStepResult.value (IRScalar.ptr_ {DCA}))"
DOPT = (
    "(IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d1) (IRScalar.vcons "
    f"(IRScalar.ptr_ {DCA}) IRScalar.vnil)))"
)
DCELLV = f"(ir_cell na {DOPT} mem)"
DKNA = "(IROption.some IRMemSlot (IRMemSlot.mk na IRScalar.undef_ Bool.true))"
DKNAV = f"(IROption.some IRMemSlot (IRMemSlot.mk na {DOPT} Bool.true))"
DTARGET = f"(ir_ret_to dests rest {DCELLV} (Nat.succ na) (ir_vl1 (IRScalar.ptr_ {DCA})))"
DARGS = "mem p na dests rest"
DARGSB = "mem p b na dests rest"


def _dsub(ty: str, body: str, known: str, actual: str, pf: str, inner: str) -> str:
    return (
        f"Eq.subst {ty} (fun (o : {ty}) => {body}) {known} {actual} "
        f"(Eq.symm {ty} {actual} {known} {pf}) ({inner})"
    )


def deref_activation() -> str:
    hf = (
        f"(Eq.trans {SLOT_TY} (ir_mem_lookup {DCELL0} p) (ir_mem_lookup mem p) {DK1} "
        f"(ir_mem_lookup_fresh_cell mem na p IRScalar.undef_ hlt) h)"
    )
    hfc = "hcb"
    t = f"Eq.refl IRConfig {DTARGET}"
    t = _dsub(SLOT_TY, f"Eq IRConfig (ir_steps ir_d12 {M} (ir_lzd_dload3 {DARGSB} o)) {DTARGET}",
              DKNAV, f"(ir_mem_lookup {DCELLV} na)",
              f"(ir_mem_lookup_head na {DOPT} Bool.true mem)", t)
    t = (f"Eq.subst {MEM_TY} (fun (o : {MEM_TY}) => Eq IRConfig "
         f"(ir_steps ir_d14 {M} (ir_lzd_dstored {DARGSB} o)) {DTARGET}) {DCELLV} "
         f"(ir_mem_update {DCELL0} na {DOPT}) (Eq.symm {MEM_TY} "
         f"(ir_mem_update {DCELL0} na {DOPT}) {DCELLV} "
         f"(ir_mem_update_head na IRScalar.undef_ Bool.true mem {DOPT})) ({t})")
    t = _dsub(SLOT_TY, f"Eq IRConfig (ir_steps ir_d14 {M} (ir_lzd_dstore {DARGSB} o)) {DTARGET}",
              DKNA, f"(ir_mem_lookup {DCELL0} na)",
              "(ir_mem_lookup_head na IRScalar.undef_ Bool.true mem)", t)
    t = _dsub("IRStepResult",
              f"Eq IRConfig (ir_steps ir_d19 {M} (ir_lzd_dborrow2 {DARGSB} o)) {DTARGET}",
              DVAL, f"(ir_borrow_eval {DCELL0} (IRScalar.ptr_ {DCA}))", hfc, t)
    t = _dsub(SLOT_TY, f"Eq IRConfig (ir_steps ir_d25 {M} (ir_lzd_dload2 {DARGSB} o)) {DTARGET}",
              DK1, f"(ir_mem_lookup {DCELL0} p)", hf, t)
    t = _dsub(SLOT_TY, f"Eq IRConfig (ir_steps ir_d31 {M} (ir_lzd_dborrow1 {DARGSB} o)) {DTARGET}",
              DK1, f"(ir_mem_lookup {DCELL0} p)", hf, t)
    t = _dsub(SLOT_TY, f"Eq IRConfig (ir_steps ir_d37 {M} (ir_lzd_dload1 {DARGS} o)) {DTARGET}",
              DK1, f"(ir_mem_lookup {DCELL0} p)", hf, t)
    return (
        "def ir_lzd_deref_activation (mem : IRList IRMemSlot) (p : Nat) (b : Nat) (na : Nat) "
        "(dests : IRList Nat) (rest : IRList IRFrame) "
        "(hlt : Eq Bool (ir_nat_ltb p na) Bool.true) "
        f"(h : Eq {SLOT_TY} (ir_mem_lookup mem p) {DK1}) "
        f"(hcb : Eq IRStepResult (ir_borrow_eval {DCELL0} (IRScalar.ptr_ {DCA})) {DVAL}) : "
        + eq_cfg(steps(DEREF_STEPS, f"(ir_lzd_dcfg0 {DARGS})"), DTARGET)
        + f" := {t}"
    )

# LEMMAS is assembled ONCE, at the bottom of this file, after every emitter is
# defined. It used to be a literal here with four entries and four
# `LEMMAS[...] = ...` assignments 340 lines below, and on 2026-09-13 an
# adversarial reader who actually opened the file concluded from the literal
# that the gate did not cover A4. It did — `--check` resolves LEMMAS at RUN
# time, not at the literal — but a gate whose coverage a careful reader
# mis-reads is a gate that will eventually be mis-maintained. One place now,
# plus `_coverage_invariant()` below, which refuses if the pinned digest set and
# LEMMAS ever stop naming the same terms.


CORRECT_RS = REPO / "crates/clean-verify/src/spec/core_spec/eval_ir_lzd_correct.rs"

# The terms a kernel accepted. `--self-test` recomputes them and compares these
# digests, so a refactor of this generator that changes the emitted SHAPE fails
# here, in a second, rather than in a twelve-minute spec build.
PINNED_DIGESTS: dict = {
    "SRC_IR_LZD_ACTIVATION": "f460a2c165fa388555a17f6f0ce49b0c343856bfc35f5ad91fb5ce1f1e14c0e4",
    "SRC_IR_LZD_CORRECT": "cef2368592d5465d0c07bd8b1e3c5a382ce698010e1247026f32416e869f641a",
    "SRC_IR_LZD_DEREF_ACTIVATION": "99f65a0de83f4b74e0e70378cf575f762b8d81979e65dd5a5df8e70681052d5e",
    "SRC_IR_LZD_FRAME_AGREE": "013743d4da41337d30d022f1cf8abf92bf2fcf73661e8075368145902d0ccbe6",
    "SRC_IR_LZD_IMAX_SEG": "2c86deb4b0b64d04c8ebb5c52571a6a79e3dc5b9e213bd060093a35954f1cb2e",
    "SRC_IR_LZD_MACHINE_SOUND": "f03269829401c692f94ac6eac5724a03033b6a20726a0b03858c9f89a48f5c20",
    "SRC_IR_LZD_MAX_FALSE_SEG": "4fa3755e824ecb655fd1462ef9c4d583feebf38e3403b3f693c379193749d7ab",
    "SRC_IR_LZD_MAX_TRUE_SEG": "ea4e70c1076505113363c38c30acd8aa2f6d5d5c10264561019dd6dd458009cb",
    "SRC_IR_LZD_NEVER_FAULTS": "f65f13441145365e227599b725de966ba32a8ee416cebd97ad0ab7bd769534c3",
}


def committed() -> dict:
    found = {}
    for f in (ACTIVATION_RS, CORRECT_RS):
        found.update(dict(re.findall(r'const (SRC_[A-Z0-9_]+): &str = "(.*?)";\n',
                                     f.read_text(), re.S)))
    return {k: v for k, v in found.items() if k in LEMMAS}


def digests() -> dict:
    import hashlib
    return {k: hashlib.sha256(f().encode()).hexdigest() for k, f in LEMMAS.items()}


# The heads the committed consts name with an explicit `@` (the spelling
# 1b6b65dc83 and the EvalIR commits after it gave them).
EXPLICIT_HEADS = frozenset({
    "Bool.rec", "EncodesLevelArcD.imax", "EncodesLevelArcD.max", "EncodesLevelArcD.param",
    "EncodesLevelArcD.rec", "EncodesLevelArcD.succ", "EncodesLevelArcD.zero",
    "EncodesLiveLevelRefD.rec", "Eq", "Eq.refl", "Eq.subst", "Eq.symm", "Eq.trans",
    "IRList.nil", "IROption.some", "MemExt.refl",
})

# Heads a const's committed source names bare at every occurrence, though it
# prefixes the rest. Recorded, not chosen: the printer reproduces the committed
# spelling, and making these consts uniform is a source change the EvalIR
# initializer would have to accept first.
KEPT_BARE = {
    "SRC_IR_LZD_FRAME_AGREE": frozenset({"Eq.trans"}),
    "SRC_IR_LZD_ACTIVATION": frozenset({"Eq.subst", "Eq.symm", "Eq.trans"}),
    "SRC_IR_LZD_CORRECT": frozenset({"Eq.subst", "Eq.symm", "Eq.trans"}),
    "SRC_IR_LZD_MACHINE_SOUND": frozenset({"Eq.symm", "Eq.trans"}),
}


def spell(name: str, term: str) -> str:
    """One built term as the tree registers it."""
    return XP.respell(term, EXPLICIT_HEADS - KEPT_BARE.get(name, frozenset()))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--print", dest="name")
    ap.add_argument("--emit", action="store_true")
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--self-test", dest="selftest", action="store_true")
    ap.add_argument("--digests", action="store_true")
    ap.add_argument("--pin", action="store_true")
    ap.add_argument("--pinned-inputs", action="store_true", help="list exact source/control inputs")
    a = ap.parse_args()
    actions = [a.name is not None, a.emit, a.check, a.selftest, a.digests, a.pin, a.pinned_inputs]
    if sum(actions) > 1:
        ap.error("primary actions cannot be combined")
    if a.pinned_inputs:
        print("\n".join(HELPER_INPUTS))
        return 0
    if a.name == "":
        ap.error("--print requires a nonempty const name")
    built = {k: spell(k, f()) for k, f in LEMMAS.items()}
    if a.name:
        key = a.name if a.name.startswith("SRC_") else "SRC_" + a.name.upper()
        print(built[key])
        return 0
    if a.emit:
        sources = {f: f.read_text() for f in (ACTIVATION_RS, CORRECT_RS)}
        edits = {f: [] for f in sources}
        for k, v in built.items():
            pat = re.compile(r'const %s: &str = ".*?";\n' % re.escape(k), re.S)
            matches = [(f, m) for f, src in sources.items() for m in pat.finditer(src)]
            if len(matches) != 1:
                ap.error(f"--emit requires exactly one binding for {k}; found {len(matches)}")
            for f, match in matches:
                edits[f].append((match.start(), match.end(), f'const {k}: &str = "{v}";\n'))
        rendered = {}
        for f, src in sources.items():
            cursor = 0
            pieces = []
            for start, end, replacement in sorted(edits[f]):
                if start < cursor:
                    ap.error("--emit bindings overlap")
                pieces.extend((src[cursor:start], replacement))
                cursor = end
            rendered[f] = "".join((*pieces, src[cursor:]))
        for f, src in rendered.items():
            f.write_text(src)
        print(f"emitted {len(built)} terms")
        return 0
    if a.pin:
        import re as _re
        body = "PINNED_DIGESTS: dict = {\n" + "".join(
            f'    "{k}": "{v}",\n' for k, v in sorted(digests().items())) + "}"
        src = Path(__file__).read_text()
        src = _re.sub(r"PINNED_DIGESTS: dict = \{.*?\}", body, src, count=1, flags=_re.S)
        Path(__file__).write_text(src)
        print(f"pinned {len(digests())} digests")
        return 0
    if a.digests:
        for k, v in sorted(digests().items()):
            print(f'    "{k}": "{v}",')
        return 0
    if a.selftest:
        have = digests()
        bad = [k for k, v in PINNED_DIGESTS.items() if have.get(k) != v]
        drift = _coverage_invariant() + XP.self_test()
        drift += [f"KEPT_BARE: {k} is not a minted const" for k in sorted(set(KEPT_BARE) - set(LEMMAS))]
        for k in bad:
            print(f"DIGEST MOVED: {k}")
        for line in drift:
            print(line)
        ok = not bad and not drift
        if ok:
            _helper_source_controls()
        print("gen_lzd_activation --self-test: " + ("OK" if ok else "FAILED"))
        return 0 if ok else 1
    if a.check:
        have = committed()
        bad = [k for k in built if have.get(k) != built[k]]
        for k in bad:
            print(f"DIFFERS: {k}")
        print("gen_lzd_activation: " + ("OK" if not bad else f"{len(bad)} differ"))
        return 1 if bad else 0
    ap.print_help()
    return 2




# ----------------------------------------------------------- the induction
#
# `ir_lzd_activation` in CONTINUATION-PASSING form, and the form is forced.
# Every earlier chain's activation could name its final heap, because its body
# performed no Store and no Alloca. This one allocates once per deref and the
# number of derefs depends on the Level being walked, so the final heap is a
# function of the DATA. CPS says "there are an `m2` and an `n2`, extending what
# we started from, for which the run ends here" without anybody having to
# compute them — and the recursion hypothesis arrives in the same shape, which
# is what lets the max arm chain two subtrees and two allocations.

def _cost(l: str) -> str:
    return f"(ir_lzd_cost {l})"


def _liz(l: str) -> str:
    return f"(level_is_zero {l})"


def _eq(m1: str, s0: str, n1: str, l0: str, m2: str, n2: str, ans: str = None) -> str:
    a = ans if ans is not None else _liz(l0)
    return (
        f"Eq IRConfig (ir_steps {_cost(l0)} {M} (IRConfig.running "
        f"(ir_lzd_mach0_s {m1} {s0} {n1} dests rest))) "
        f"(ir_ret_to dests rest {m2} {n2} (ir_vl1 (IRScalar.bool_ {a})))"
    )


def _fa(m1: str, s0: str, n1: str, l0: str, m2: str, n2: str) -> str:
    return f"forall (dests : IRList Nat) (rest : IRList IRFrame), {_eq(m1, s0, n1, l0, m2, n2)}"


def _kty(s0: str, l0: str, m1: str, n1: str) -> str:
    return (
        f"forall (m2 : IRList IRMemSlot) (n2 : Nat), MemExt {m1} {n1} m2 n2 -> "
        f"({_fa(m1, s0, n1, l0, 'm2', 'n2')}) -> C"
    )


def _cps(s0: str, l0: str) -> str:
    return (
        "forall (m1 : IRList IRMemSlot) (n1 : Nat), MemExt mem n m1 n1 -> forall (C : Prop), "
        f"({_kty(s0, l0, 'm1', 'n1')}) -> C"
    )


def _sl(a: str, v: str) -> str:
    return f"(IROption.some IRMemSlot (IRMemSlot.mk {a} {v} Bool.true))"


def _lk(a: str, v: str) -> str:
    return f"Eq {SLOT_TY} (ir_mem_lookup mem {a}) {_sl(a, v)}"


def _lt(a: str) -> str:
    return f"Eq Bool (ir_nat_ltb {a} n) Bool.true"


def _framed(a: str, v: str, hyp: str) -> str:
    return (
        f"(Eq.trans {SLOT_TY} (ir_mem_lookup m1 {a}) (ir_mem_lookup mem {a}) {_sl(a, v)} "
        f"(ir_lzd_lookup_ext mem n m1 n1 e {a} {'hlt' if a == 'a' else ('hlt8' if 'ir_d8' in a else 'hlt16')}) {hyp})"
    )


_A, _A8, _A16 = "a", "(Nat.add a ir_d8)", "(Nat.add a ir_d16)"
_PB = "(IRScalar.ptr_ (Nat.succ b))"
_P1, _P2 = "(IRScalar.ptr_ (Nat.succ b1))", "(IRScalar.ptr_ (Nat.succ b2))"
_C1 = f"(IRScalar.ptr_ {child_of('b1')})"
_C2 = f"(IRScalar.ptr_ {child_of('b2')})"
_CB = f"(IRScalar.ptr_ {child_of('b')})"
_V0 = "(ir_var ir_d0 ir_sp0)"
_V1 = f"(ir_var ir_d1 (ir_sp1 {_PB}))"
_V2 = f"(ir_var ir_d2 (ir_sp2 {_P1} {_P2}))"
_V3 = f"(ir_var ir_d3 (ir_sp2 {_P1} {_P2}))"
_V4 = "(ir_var ir_d4 (ir_sp1 w))"
_HEAD = "fun (m1 : IRList IRMemSlot) (n1 : Nat) (e : MemExt mem n m1 n1) (C : Prop)"


def _leaf(fields: str, s0: str, l0: str, call: str) -> str:
    return (
        f"(fun {fields} => {_HEAD} (k : {_kty(s0, l0, 'm1', 'n1')}) => "
        f"k m1 n1 (MemExt.refl m1 n1) "
        f"(fun (dests : IRList Nat) (rest : IRList IRFrame) => {call}))"
    )


def _two_arm(tag_v: str, seg_body, with8: bool = True):
    """The shared head of the max and imax minors.

    `with8` is FALSE for imax: the relation no longer carries a +8 cell on that
    arm, because the emitted body never geps +8 on the imax path.
    """
    h8 = f"(hlt8 : {_lt(_A8)}) " if with8 else ""
    m8 = f"(hm8 : {_lk(_A8, _P1)}) " if with8 else ""
    return (
        f"(fun (a : Nat) (b1 : Nat) (b2 : Nat) (l1 : Level) (l2 : Level) (hlt : {_lt(_A)}) "
        + h8
        + f"(hlt16 : {_lt(_A16)}) (hm : {_lk(_A, tag_v)}) "
        + m8
        + f"(hm16 : {_lk(_A16, _P2)}) "
        f"(_r1 : EncodesLevelArcD mem n {_C1} l1) (_r2 : EncodesLevelArcD mem n {_C2} l2) "
        f"(ih1 : {_cps(_C1, 'l1')}) (ih2 : {_cps(_C2, 'l2')}) => {seg_body})"
    )


def _hcb(child: str, lvl: str, rel: str) -> str:
    return f"(ir_lzd_live_ext m1 n1 {child} {lvl} (ir_lzd_frame_ext mem n {child} {lvl} {rel} m1 n1 e))"


def _ext_one(m: str, nn: str, opt: str) -> str:
    return f"(ir_mem_ext_one {m} {nn} {opt})"


def activation() -> str:
    opt1, opt2 = opt_of("b1"), opt_of("b2")
    cell1, cell2 = f"(ir_cell n1 {opt1} m1)", f"(ir_cell nA {opt2} mA)"
    # ---- imax: one subtree, one allocation
    ext_a = (
        f"(ir_mem_ext_trans mem n m1 n1 e (ir_cell n1 {opt2} m1) (Nat.succ n1) "
        f"{_ext_one('m1', 'n1', opt2)})"
    )
    ext_b = (
        f"(ir_mem_ext_trans m1 n1 (ir_cell n1 {opt2} m1) (Nat.succ n1) "
        f"{_ext_one('m1', 'n1', opt2)} mA nA eA)"
    )
    imax_call = (
        f"ir_lzd_imax_seg m1 a b1 b2 {_cost('l2')} {_liz('l2')} n1 dests rest mA nA "
        f"{_framed(_A, _V3, 'hm')} {_framed(_A16, _P2, 'hm16')} "
        f"(ir_lzd_ltb_ext mem n m1 n1 e {_A16} hlt16) "
        f"{_hcb(_C2, 'l2', '_r2')} eA eq2"
    )
    imax_body = (
        f"{_HEAD} (k : {_kty(f'(IRScalar.ptr_ a)', '(Level.imax l1 l2)', 'm1', 'n1')}) => "
        f"ih2 (ir_cell n1 {opt2} m1) (Nat.succ n1) {ext_a} C "
        f"(fun (mA : IRList IRMemSlot) (nA : Nat) "
        f"(eA : MemExt (ir_cell n1 {opt2} m1) (Nat.succ n1) mA nA) "
        f"(eq2 : {_fa(f'(ir_cell n1 {opt2} m1)', _C2, '(Nat.succ n1)', 'l2', 'mA', 'nA')}) => "
        f"k mA nA {ext_b} (fun (dests : IRList Nat) (rest : IRList IRFrame) => {imax_call}))"
    )
    # ---- max: two subtrees, two allocations, and a convoy on the left answer
    ext1a = (
        f"(ir_mem_ext_trans mem n m1 n1 e {cell1} (Nat.succ n1) {_ext_one('m1', 'n1', opt1)})"
    )
    ext2a = (
        f"(ir_mem_ext_trans m1 n1 {cell1} (Nat.succ n1) {_ext_one('m1', 'n1', opt1)} mA nA eA)"
    )
    ext1b = (
        f"(ir_mem_ext_trans mem n mA nA (ir_mem_ext_trans mem n m1 n1 e mA nA {ext2a}) "
        f"{cell2} (Nat.succ nA) {_ext_one('mA', 'nA', opt2)})"
    )
    ext2b = (
        f"(ir_mem_ext_trans m1 n1 mA nA {ext2a} mB nB "
        f"(ir_mem_ext_trans mA nA {cell2} (Nat.succ nA) {_ext_one('mA', 'nA', opt2)} mB nB eB))"
    )
    # ih1's equation, with its answer rewritten to the branch's literal
    def eq1_at(lit: str, hyp: str) -> str:
        p = (
            f"(fun (bv : Bool) => {_fa(cell1, _C1, '(Nat.succ n1)', 'l1', 'mA', 'nA').replace(_liz('l1'), 'bv')})"
        )
        return (
            f"(Eq.subst Bool {p} {_liz('l1')} {lit} {hyp} eq1)"
        )
    common_hyps = (
        f"{_framed(_A, _V2, 'hm')} {_framed(_A8, _P1, 'hm8')} {_framed(_A16, _P2, 'hm16')} "
        f"(ir_lzd_ltb_ext mem n m1 n1 e {_A8} hlt8) (ir_lzd_ltb_ext mem n m1 n1 e {_A16} hlt16) "
        f"{_hcb(_C1, 'l1', '_r1')} {_hcb(_C2, 'l2', '_r2')}"
    )
    false_call = (
        f"ir_lzd_max_false_seg m1 a b1 b2 {_cost('l1')} n1 dests rest mA nA "
        f"{common_hyps} eA {eq1_at('Bool.false', 'hf')}"
    )
    true_call = (
        f"ir_lzd_max_true_seg m1 a b1 b2 {_cost('l1')} {_cost('l2')} {_liz('l2')} n1 dests rest "
        f"mA nA mB nB {common_hyps} eA eB {eq1_at('Bool.true', 'ht')} eq2"
    )
    # the convoy motive: the goal is opaque `C`, so the branch's LITERAL answer is
    # transported into k's argument rather than into the goal.
    def max_cost(v: str) -> str:
        """`ir_lzd_cost (Level.max l1 l2)` with the left answer left ABSTRACT.

        The convoy has to abstract `v` in the COST as well as in the answer: the
        cost function's max arm is a `Bool.rec` on `level_is_zero l1`, and a
        motive that wrote `ir_lzd_cost (Level.max l1 l2)` would mention `v`
        nowhere, so its `Bool.false` instance would still carry the full
        two-deref cost and no segment lemma would match it.
        """
        inner = (
            f"(Nat.add (Nat.add (Nat.add (Nat.add ir_d3 {_cost('l2')}) ir_d1) ir_d40) ir_d2)"
        )
        picked = f"(Bool.rec (fun (_ : Bool) => Nat) ir_d5 {inner} {v})"
        return (
            f"(Nat.add (Nat.add (Nat.add (Nat.add {picked} {_cost('l1')}) ir_d1) ir_d40) ir_d8)"
        )

    def k_arg(lit: str, hyp: str, m2: str, n2: str, call: str) -> str:
        p = (
            f"(fun (v : Bool) => forall (dests : IRList Nat) (rest : IRList IRFrame), "
            f"Eq IRConfig (ir_steps {max_cost('v')} {M} (IRConfig.running "
            f"(ir_lzd_mach0_s m1 (IRScalar.ptr_ a) n1 dests rest))) "
            f"(ir_ret_to dests rest {m2} {n2} "
            f"(ir_vl1 (IRScalar.bool_ (Bool.and v {_liz('l2')})))))"
        )
        return (
            f"(Eq.subst Bool {p} {lit} {_liz('l1')} (Eq.symm Bool {_liz('l1')} {lit} {hyp}) "
            f"(fun (dests : IRList Nat) (rest : IRList IRFrame) => {call}))"
        )
    max_body = (
        f"{_HEAD} (k : {_kty('(IRScalar.ptr_ a)', '(Level.max l1 l2)', 'm1', 'n1')}) => "
        f"ih1 {cell1} (Nat.succ n1) {ext1a} C "
        f"(fun (mA : IRList IRMemSlot) (nA : Nat) "
        f"(eA : MemExt {cell1} (Nat.succ n1) mA nA) "
        f"(eq1 : {_fa(cell1, _C1, '(Nat.succ n1)', 'l1', 'mA', 'nA')}) => "
        f"Bool.rec (fun (v : Bool) => Eq Bool {_liz('l1')} v -> C) "
        f"(fun (hf : Eq Bool {_liz('l1')} Bool.false) => "
        f"k mA nA {ext2a} {k_arg('Bool.false', 'hf', 'mA', 'nA', false_call)}) "
        f"(fun (ht : Eq Bool {_liz('l1')} Bool.true) => "
        f"ih2 {cell2} (Nat.succ nA) {ext1b} C "
        f"(fun (mB : IRList IRMemSlot) (nB : Nat) "
        f"(eB : MemExt {cell2} (Nat.succ nA) mB nB) "
        f"(eq2 : {_fa(cell2, _C2, '(Nat.succ nA)', 'l2', 'mB', 'nB')}) => "
        f"k mB nB {ext2b} {k_arg('Bool.true', 'ht', 'mB', 'nB', true_call)})) "
        f"{_liz('l1')} (Eq.refl Bool {_liz('l1')}))"
    )
    motive = (
        "(fun (s0 : IRScalar) (l0 : Level) (_ : EncodesLevelArcD mem n s0 l0) => "
        f"{_cps('s0', 'l0')})"
    )
    m_zero = _leaf(f"(a : Nat) (hlt : {_lt(_A)}) (hm : {_lk(_A, _V0)})",
                   "(IRScalar.ptr_ a)", "Level.zero",
                   f"ir_lzd_activation_zero m1 a n1 dests rest {_framed(_A, _V0, 'hm')}")
    m_succ = _leaf(
        f"(a : Nat) (b : Nat) (l0 : Level) (hlt : {_lt(_A)}) "
        f"(hm : {_lk(_A, _V1)}) "
        f"(_r : EncodesLevelArcD mem n {_CB} l0) (_ih : {_cps(_CB, 'l0')})",
        "(IRScalar.ptr_ a)", "(Level.succ l0)",
        f"ir_lzd_activation_succ m1 a n1 dests rest b {_framed(_A, _V1, 'hm')}")
    m_param = _leaf(
        f"(a : Nat) (w : IRScalar) (nm : Name) (hlt : {_lt(_A)}) (hm : {_lk(_A, _V4)})",
        "(IRScalar.ptr_ a)", "(Level.param nm)",
        f"ir_lzd_activation_param m1 a n1 dests rest w {_framed(_A, _V4, 'hm')}")
    return (
        "def ir_lzd_activation (mem : IRList IRMemSlot) (n : Nat) (s : IRScalar) (l : Level) "
        f"(d : EncodesLevelArcD mem n s l) : {_cps('s', 'l')} := EncodesLevelArcD.rec mem n "
        f"{motive} {m_zero} {m_succ} {_two_arm(_V2, max_body)} {_two_arm(_V3, imax_body, False)} "
        f"{m_param} s l d"
    )






# --------------------------------------------------------------- A4 and A5


def a4() -> str:
    """`ir_lzd_correct` — A4 over the module with no authored function in it.

    The representation premise is stated at `ir_lzd_init_mem mem`, not at `mem`,
    and the difference is the module's own GLOBAL: `ir_init` materialises one
    cell per global before the first instruction runs (a global's id IS its
    address), so the heap the program executes against is the caller's heap with
    the `expect` message consed on. `ir_lzb_module` has no global and could keep
    the two apart; this one cannot, and saying so is the honest statement rather
    than an inconvenience -- a Level represented only in a heap the machine never
    sees would be a premise about nothing.
    """
    IM = "(ir_lzd_init_mem mem)"
    S = "(IRScalar.ptr_ a)"
    ans = f"(ir_vl1 (IRScalar.bool_ {_liz('l0')}))"
    ret = f"(IROutcome.ret {ans})"
    init = f"(ir_init {M} ir_d0 (ir_vl1 {S}) mem na)"
    cost = _cost("l0")
    fin = f"(ir_ret_to (IRList.nil Nat) (IRList.nil IRFrame) m2 n2 {ans})"
    inner = (
        f"(ir_run_le_ret {M} {cost} fuel hle {init} {ans} "
        f"(Eq.trans IROutcome (ir_run {cost} {M} {init}) "
        f"(ir_config_outcome (ir_steps {cost} {M} {init})) {ret} "
        f"(ir_run_of_steps {M} {cost} {init}) "
        f"(Eq.subst IRConfig (fun (kk : IRConfig) => "
        f"Eq IROutcome (ir_config_outcome kk) {ret}) {fin} "
        f"(ir_steps {cost} {M} {init}) "
        f"(Eq.symm IRConfig (ir_steps {cost} {M} {init}) {fin} "
        f"(eqf (IRList.nil Nat) (IRList.nil IRFrame))) "
        f"(Eq.refl IROutcome {ret}))))"
    )
    cont = (
        f"(fun (m2 : IRList IRMemSlot) (n2 : Nat) (_ext : MemExt {IM} na m2 n2) "
        f"(eqf : {_fa(IM, S, 'na', 'l0', 'm2', 'n2')}) => {inner})"
    )
    minor = (
        f"(fun (a : Nat) (l0 : Level) (arc : EncodesLevelArcD {IM} na {S} l0) "
        f"(hle : Le {cost} fuel) => ir_lzd_activation {IM} na {S} l0 arc {IM} na "
        f"(MemExt.refl {IM} na) (Eq IROutcome (ir_eval fuel {M} ir_d0 (ir_vl1 {S}) mem na) "
        f"{ret}) {cont})"
    )
    return (
        "def ir_lzd_correct (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (r : IRScalar) "
        f"(l : Level) (href : EncodesLiveLevelRefD {IM} na r l) : "
        f"Le {_cost('l')} fuel -> Eq IROutcome (ir_eval fuel {M} ir_d0 (ir_vl1 r) mem na) "
        f"(IROutcome.ret (ir_vl1 (IRScalar.bool_ {_liz('l')}))) := "
        f"EncodesLiveLevelRefD.rec {IM} na (fun (s0 : IRScalar) (l1 : Level) "
        f"(_ : EncodesLiveLevelRefD {IM} na s0 l1) => "
        f"Le {_cost('l1')} fuel -> Eq IROutcome (ir_eval fuel {M} ir_d0 (ir_vl1 s0) mem na) "
        f"(IROutcome.ret (ir_vl1 (IRScalar.bool_ {_liz('l1')})))) "
        f"{minor} r l href"
    )


def a5() -> str:
    ret_l = f"(IROutcome.ret (ir_vl1 (IRScalar.bool_ {_liz('l')})))"
    ret_t = "(IROutcome.ret (ir_vl1 (IRScalar.bool_ Bool.true)))"
    run = f"(ir_eval fuel {M} ir_d0 (ir_vl1 r) mem na)"
    return (
        "def ir_lzd_machine_sound (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) "
        "(r : IRScalar) (l : Level) (href : EncodesLiveLevelRefD (ir_lzd_init_mem mem) na r l) "
        f"(hle : Le {_cost('l')} fuel) (hret : Eq IROutcome {run} {ret_t}) : "
        "forall (rho : Name -> Nat), Eq Nat (level_eval rho l) Nat.zero := "
        f"level_is_zero_sound l (Eq.cong IROutcome Bool ir_outcome_bool {ret_l} {ret_t} "
        f"(Eq.trans IROutcome {ret_l} {run} {ret_t} "
        f"(Eq.symm IROutcome {run} {ret_l} (ir_lzd_correct mem fuel na r l href hle)) hret))"
    )


def never_faults() -> str:
    ret_l = f"(IROutcome.ret (ir_vl1 (IRScalar.bool_ {_liz('l')})))"
    run = f"(ir_eval fuel {M} ir_d0 (ir_vl1 r) mem na)"
    return (
        "def ir_lzd_never_faults (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) "
        "(r : IRScalar) (l : Level) (href : EncodesLiveLevelRefD (ir_lzd_init_mem mem) na r l) "
        f"(hle : Le {_cost('l')} fuel) : Eq Bool (ir_outcome_is_ret {run}) Bool.true := "
        f"Eq.cong IROutcome Bool ir_outcome_is_ret {run} {ret_l} "
        f"(ir_lzd_correct mem fuel na r l href hle)"
    )


# ---------------------------------------------------------------- the registry
#
# Every term this generator mints, in one place. Adding an emitter without
# adding it here would leave a claim-bearing constant that nothing re-derives —
# the exact class the gate exists to close — so `_coverage_invariant` refuses
# any drift between this table and the pinned digests.

# ------------------------------------------------ the general framing rule
#
# ONE induction that subsumes every framing shape this chain has. The relation
# `EncodesLevelArcD mem n` depends on the heap in exactly one way -- a set of
# `ir_mem_lookup mem <addr>` equations, each guarded by `ltb <addr> n = true` --
# so it survives ANY heap that agrees with `mem` below the bound, under ANY
# bound that is at least as large. Say that once and the three framing lemmas
# this file's chain used to prove separately are readings of it:
#
#   ir_lzd_frame            mem2 = ir_cell n v mem,      n2 = Nat.succ n
#   ir_lzd_frame_store      mem2 = ir_mem_update mem n v, n2 = n
#   ir_lzd_frame_store_at   mem2 = ir_mem_update mem a v, n2 = n,  ltb a n = false
#
# and so is every future one, including the shape `TypeChecker`'s fourteen
# in-place `RefCell` caches need, which is a store at an address the
# representation never mentions. That case is `ir_lzd_frame_store_disjoint`:
# it takes the disequality as a PREMISE rather than deriving it from a bound,
# which is the difference between "this heap grew" and "this heap changed".

AGREE_BINDERS = (
    "(mem : IRList IRMemSlot) (mem2 : IRList IRMemSlot) (n : Nat) (n2 : Nat) "
    "(hb : forall (x : Nat), Eq Bool (ir_nat_ltb x n) Bool.true -> "
    "Eq Bool (ir_nat_ltb x n2) Bool.true) "
    "(hag : forall (x : Nat), Eq Bool (ir_nat_ltb x n) Bool.true -> "
    f"Eq {SLOT_TY} (ir_mem_lookup mem2 x) (ir_mem_lookup mem x)) "
    "(s : IRScalar) (l : Level) (d : EncodesLevelArcD mem n s l)"
)

A8 = "(Nat.add a ir_d8)"
A16 = "(Nat.add a ir_d16)"
PTR1 = "(IRScalar.ptr_ (Nat.succ b1))"
PTR2 = "(IRScalar.ptr_ (Nat.succ b2))"
KID1 = "(IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16))"
KID2 = "(IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16))"


def _ag_lt(addr: str) -> str:
    return f"Eq Bool (ir_nat_ltb {addr} n) Bool.true"


def _ag_slot(addr: str, val: str) -> str:
    return f"(IROption.some IRMemSlot (IRMemSlot.mk {addr} {val} Bool.true))"


def _ag_look(addr: str, rhs: str) -> str:
    return f"Eq {SLOT_TY} (ir_mem_lookup mem {addr}) {rhs}"


def _moved(addr: str, h: str, hm: str, rhs: str) -> str:
    """The one transport: the same lookup, read in mem2 instead of mem."""
    return (f"(Eq.trans {SLOT_TY} (ir_mem_lookup mem2 {addr}) (ir_mem_lookup mem {addr}) "
            f"{rhs} (hag {addr} {h}) {hm})")


def _pair_arm(ctor: str, tag: str, with8: bool = True) -> str:
    """The max and imax arms. imax carries no +8 cell -- the body never geps it."""
    sl = f"(ir_var {tag} (ir_sp2 {PTR1} {PTR2}))"
    r0, r8, r16 = _ag_slot("a", sl), _ag_slot(A8, PTR1), _ag_slot(A16, PTR2)
    b8 = f"(hlt8 : {_ag_lt(A8)}) " if with8 else ""
    m8 = f"(hm8 : {_ag_look(A8, r8)}) " if with8 else ""
    hb8 = f"(hb {A8} hlt8) " if with8 else ""
    mv8 = f"{_moved(A8, 'hlt8', 'hm8', r8)} " if with8 else ""
    return (
        "(fun (a : Nat) (b1 : Nat) (b2 : Nat) (l1 : Level) (l2 : Level) "
        f"(hlt : {_ag_lt('a')}) " + b8 + f"(hlt16 : {_ag_lt(A16)}) "
        f"(hm : {_ag_look('a', r0)}) " + m8 + f"(hm16 : {_ag_look(A16, r16)}) "
        f"(_r1 : EncodesLevelArcD mem n {KID1} l1) (_r2 : EncodesLevelArcD mem n {KID2} l2) "
        f"(ih1 : EncodesLevelArcD mem2 n2 {KID1} l1) (ih2 : EncodesLevelArcD mem2 n2 {KID2} l2) => "
        f"EncodesLevelArcD.{ctor} mem2 n2 a b1 b2 l1 l2 (hb a hlt) " + hb8
        + f"(hb {A16} hlt16) "
        f"{_moved('a', 'hlt', 'hm', r0)} " + mv8
        + f"{_moved(A16, 'hlt16', 'hm16', r16)} ih1 ih2)"
    )


def frame_agree() -> str:
    zs = _ag_slot("a", "(ir_var ir_d0 ir_sp0)")
    zero = (f"(fun (a : Nat) (hlt : {_ag_lt('a')}) (hm : {_ag_look('a', zs)}) => "
            f"EncodesLevelArcD.zero mem2 n2 a (hb a hlt) {_moved('a', 'hlt', 'hm', zs)})")
    ss = _ag_slot("a", "(ir_var ir_d1 (ir_sp1 (IRScalar.ptr_ (Nat.succ b))))")
    kid = "(IRScalar.ptr_ (Nat.add (Nat.succ b) ir_d16))"
    succ = (
        f"(fun (a : Nat) (b : Nat) (l0 : Level) (hlt : {_ag_lt('a')}) "
        f"(hm : {_ag_look('a', ss)}) "
        f"(_r : EncodesLevelArcD mem n {kid} l0) (ihb : EncodesLevelArcD mem2 n2 {kid} l0) => "
        f"EncodesLevelArcD.succ mem2 n2 a b l0 (hb a hlt) "
        f"{_moved('a', 'hlt', 'hm', ss)} ihb)"
    )
    ps = _ag_slot("a", "(ir_var ir_d4 (ir_sp1 w))")
    param = (f"(fun (a : Nat) (w : IRScalar) (nm : Name) (hlt : {_ag_lt('a')}) "
             f"(hm : {_ag_look('a', ps)}) => EncodesLevelArcD.param mem2 n2 a w nm (hb a hlt) "
             f"{_moved('a', 'hlt', 'hm', ps)})")
    motive = ("(fun (s0 : IRScalar) (l0 : Level) (_ : EncodesLevelArcD mem n s0 l0) => "
              "EncodesLevelArcD mem2 n2 s0 l0)")
    return (f"def ir_lzd_frame_agree {AGREE_BINDERS} : EncodesLevelArcD mem2 n2 s l := "
            f"EncodesLevelArcD.rec mem n {motive} {zero} {succ} "
            f"{_pair_arm('max', 'ir_d2')} {_pair_arm('imax', 'ir_d3', False)} {param} s l d")


LEMMAS = {
    "SRC_IR_LZD_FRAME_AGREE": frame_agree,
    "SRC_IR_LZD_DEREF_ACTIVATION": deref_activation,
    "SRC_IR_LZD_MAX_TRUE_SEG": max_true_seg,
    "SRC_IR_LZD_MAX_FALSE_SEG": max_false_seg,
    "SRC_IR_LZD_IMAX_SEG": imax_seg,
    "SRC_IR_LZD_ACTIVATION": activation,
    "SRC_IR_LZD_CORRECT": a4,
    "SRC_IR_LZD_MACHINE_SOUND": a5,
    "SRC_IR_LZD_NEVER_FAULTS": never_faults,
}


def _coverage_invariant() -> list:
    """Refusals if the registry and the pinned digests disagree.

    A term in LEMMAS with no pinned digest is unguarded by `--self-test`; a
    pinned digest with no emitter is a name the generator no longer produces.
    Either is silent coverage loss, so both are hard refusals rather than
    warnings.
    """
    out = []
    for k in sorted(set(LEMMAS) - set(PINNED_DIGESTS)):
        out.append(f"UNPINNED: {k} is minted but has no pinned digest")
    for k in sorted(set(PINNED_DIGESTS) - set(LEMMAS)):
        out.append(f"ORPHAN DIGEST: {k} is pinned but no emitter produces it")
    return out


if __name__ == "__main__":
    sys.exit(main())
