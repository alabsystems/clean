#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Mint the three STEP-INDEXED `ir_lzd_*_sseg` local obligations (E2).

The step-indexed twin of `gen_lzd_activation.py` (E2 of the Crystal lane;
statements settled in `designs/2026-09-24-e2-contract-soundness.md`). Same
bodies, same segment list -- literal runs the machine computes, a deref, a
recursive call -- and the same heap/counter/MemExt state threaded through it,
but every CALL is now discharged by a CONTRACT instead of an exact run:

  * the deref by `ir_lzd_deref_ctr` -- `ir_lzd_deref_activation` through the
    adapter `ir_ctr_exact` -- whose post is an EXACT triple, consumed by
    substitution (`ir_post_exact` is Leibniz equality);
  * the recursive call by the recursion-group hypothesis `ih1` / `ih2`, a
    step-indexed contract at the STRICTLY SMALLER budget `n`, whose post
    (`ir_lzd_zpost`) says only that the heap grew and the answer is a Bool --
    the final heap is known only inside the continuation.

Each obligation proves the body's contract at `Nat.succ n`. The one step that
separates `succ n` from `n` is the body's first instruction (the load);
everything else -- literal runs and the exact deref -- is padded for free
(`ir_safe_pad`), so both recursive calls consume their contract at exactly
`n`. That is the whole reason no strong induction is needed.

ONE LEMMA PER CALL (D5's re-decided remedy, 2026-09-25). Each obligation is
minted as a CHAIN of resume-segment lemmas rather than one nested term. The
obligation's own proof walks the body up to its first call and hands that
call's continuation to `<obligation>_r1`; `_r<i>` is the safety of the
configuration the body resumes at after call `i`, and its proof walks the
next literal run and call `i + 1`, whose continuation applies `_r<i+1>`. The
last `_r<k>` ends at the body's `ret`. So no term nests a call's continuation
inside another call's, and each lemma is checked at binder depth one --
`designs/2026-09-24-e2-contract-soundness.md` section 8.5 measured the nested
shape at a log-log slope of ~2.1 in the number of calls and this shape at ~0.9.
Each segment takes exactly the binders its statement and proof mention (closed
under mention in their types); the continuation-bound heap, counter and
`MemExt` witness of an earlier recursive call are ordinary binders there.
Two more things would make a segment's TEXT grow with the calls before it, and
both are cut: the frame stack each call returns into is a named def
`<obligation>_st<i>` over the previous stack's name (spelled out it is
`frames_after(cfg)` with the whole execution history inside), and the state's
`MemExt` witness is a binder `ex<i>` the caller supplies. Measured on the real
bodies (report 2026-09-25-one-lemma-per-call): segments alone took the 4-call
obligation from 7.3 s to 3.6 s but kept a slope of ~1.4 against the 2-call
ones; with the stacks named it is 2.4 s and the slope is ~1.0.
The OBLIGATION's statement is byte-identical to the nested form's -- only its
proof changes -- so every consumer and census pins it unchanged. `--self-test`
still reproduces the nested terms the kernel accepted on 2026-09-24
(`LEGACY_DIGESTS`, with `SEGMENTED = False`), so the segment vocabulary is
shown to be the one those terms were built from.

USAGE
    python3 scripts/gen_lzd_sctr.py --print <name>
    python3 scripts/gen_lzd_sctr.py --emit       # rewrite the Rust consts
    python3 scripts/gen_lzd_sctr.py --check      # byte-compare with the tree
    python3 scripts/gen_lzd_sctr.py --self-test  # pinned digests + coverage
    python3 scripts/gen_lzd_sctr.py --pin        # re-pin (only after the kernel accepted)

The obligations are built without explicit prefixes; that is the shape
`--self-test` and `--pin` digest. What the tree registers is that text printed
by `scripts/explicit_prefix.py` (through gen_lzd_activation, which loads it) with
`@` before the heads in `EXPLICIT_HEADS`, less those a const keeps bare
(`KEPT_BARE`); `--print`, `--emit` and `--check` speak the printed text, except
`--legacy`, which prints the 2026-09-24 nested form as it was accepted.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

ANSWERS_PINNED_INPUTS = True
HELPER_INPUTS = ('scripts/test_generator_source_helpers.py', 'scripts/resource_transport.py', 'scripts/gen_lzd_activation.py', 'scripts/explicit_prefix.py', 'crates/clean-verify/src/spec/core_spec/eval_ir_lzd_sctr.rs', 'crates/clean-verify/src/spec/core_spec/eval_ir_lzd_pc.rs')


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
    controls.run_generator_controls(Path(__file__).name)

SCTR_RS = REPO / "crates/clean-verify/src/spec/core_spec/eval_ir_lzd_sctr.rs"

# The exact-chain generator is the single source of the segment vocabulary:
# the module, the heap state, the deref's framing, the hypotheses a segment
# takes. Importing it (rather than copying) is what keeps the step-indexed
# obligations reading the SAME bodies the exact A4 read.
_act = _source_module("gen_lzd_activation", REPO / "scripts/gen_lzd_activation.py")

M = _act.M
SLOT_TY = _act.SLOT_TY
MEM_TY = _act.MEM_TY
State = _act.State
ENTRY = _act.ENTRY
Lit = _act.Lit
child_of = _act.child_of
opt_of = _act.opt_of
steps = _act.steps
nat_add = _act.nat_add
ret_to = _act.ret_to
frames_after = _act.frames_after
bool_val = _act.bool_val
ptr_val = _act.ptr_val
common = _act.common
MAX_SLOT = _act.MAX_SLOT
IMAX_SLOT = _act.IMAX_SLOT


def safe(cfg: str) -> str:
    """The goal every chain node proves: safety of `cfg` for `n` steps."""
    return f"ir_safe G {M} n {cfg}"


# ------------------------------------------------ one lemma per call
#
# `SEGMENTED = False` reproduces the nested terms the kernel accepted on
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
    kept binders' types, in scope order. Over-inclusion is harmless (an unused
    binder); under-inclusion would leave a name unbound, and a token scan
    cannot miss a mention, so it errs only the harmless way."""
    names = [n for n, _ in scope]
    assert len(names) == len(set(names)), f"shadowed binder in scope: {names}"
    want, keep = set(_TOKEN.findall(text)), set()
    grew = True
    while grew:
        grew = False
        for name, ty in scope:
            if name in want and name not in keep:
                keep.add(name)
                want |= set(_TOKEN.findall(ty))
                grew = True
    return [(n, t) for n, t in scope if n in keep]


def render(binders: list) -> str:
    return "".join(f"({n} : {t}) " for n, t in binders)


class Mint:
    """Collects one obligation's segment declarations, dependencies first.

    Every declaration it mints has O(1) text in the number of calls before it,
    which is what makes the chain linear (measured: section 9 of the design
    note). Three things would otherwise grow with the call index, and each is
    cut here:

      * the continuation of a call -- `resume` makes the rest of the body its
        own lemma `<base>_r<i>`;
      * the frame stack a call returns to, `frames_after(cfg)`, whose `cfg`
        spells out the whole execution history -- `stack` names it as
        `<base>_st<i>`, a def over the PREVIOUS stack's name;
      * the heap-extension witness the state threads through every call --
        `resume` takes it as a binder `ex<i>` and the caller passes it.
    """

    def __init__(self, base: str, scope: list):
        self.base, self.scope = base, list(scope)
        self.count = 0
        self.nstacks = 0
        self.stacks: list = []
        self.lemmas: list = []

    def stack(self, cfg: str) -> str:
        """The frames beneath the callee a call at `cfg` pushed: spelled out
        (legacy), or named, applied to exactly the binders it needs."""
        body = frames_after(cfg)
        if not SEGMENTED:
            return body
        self.nstacks += 1
        name = f"{self.base}_st{self.nstacks}"
        binders = needed(self.scope, body)
        self.stacks.append((name, f"def {name} {render(binders)}: IRList IRFrame := {body[1:-1]}"))
        return f"({name} {' '.join(n for n, _ in binders)})"

    def resume(self, rest, cfg: str, st: State, bound: list) -> str:
        """`ir_safe G M n cfg` for the body from `cfg` on: nested (legacy), or
        ONE named lemma applied to exactly the binders it needs."""
        if not SEGMENTED:
            return chain(rest, cfg, st, self)
        self.count += 1
        name = f"{self.base}_r{self.count}"
        ext = f"ex{self.count}"
        outer = self.scope
        self.scope = outer + bound + [(ext, f"MemExt mem na {st.mem} {st.na}")]
        proof = chain(rest, cfg, st.__class__(st.mem, st.na, ext), self)
        stmt = safe(cfg)
        binders = needed(self.scope, f"{stmt} {proof}")
        self.scope = outer
        self.lemmas.append((name, f"def {name} {render(binders)}: {stmt} := {proof}"))
        args = [st.ext if n == ext else n for n, _ in binders]
        return f"({name} {' '.join(args)})"

    def minted(self) -> list:
        """Stacks first (each names the previous one), then the segments."""
        return self.stacks + self.lemmas


def ctr(entry: str, post: str, budget: str) -> str:
    return f"ir_ctr_at {M} {entry} {post} {budget}"


def zpost(mem: str, na: str, ans: str) -> str:
    return f"(ir_lzd_zpost {mem} {na} {ans})"


def entry0(mem: str, s: str, na: str) -> str:
    """Function 0's entry machine, curried over the caller (dests, stack)."""
    return f"(ir_lzd_mach0_s {mem} {s} {na})"


class DerefC:
    """One deref, discharged by its CONTRACT (`ir_lzd_deref_ctr`)."""

    def __init__(self, tag: str, field: str, dest: str, base: str, hlt: str, h: str,
                 hcb: str):
        self.tag = tag
        self.field, self.dest, self.base = field, dest, base
        self.hlt, self.h, self.hcb = hlt, h, hcb

    def after(self, st: State) -> State:
        mem2 = f"(ir_cell {st.na} {opt_of(self.base)} {st.mem})"
        na2 = f"(Nat.succ {st.na})"
        ext = (
            f"(ir_mem_ext_trans mem na {st.mem} {st.na} {st.ext} {mem2} {na2} "
            f"(ir_mem_ext_one {st.mem} {st.na} {opt_of(self.base)}))"
        )
        return State(mem2, na2, ext)

    def args(self, st: State) -> str:
        """The contract's premises at this state -- exactly the exact chain's."""
        h = st.framed_lookup(self.field, f"(IRScalar.ptr_ (Nat.succ {self.base}))",
                             self.hlt, self.h)
        one = f"(ir_mem_ext_one {st.mem} {st.na} IRScalar.undef_)"
        cell0 = f"(ir_cell {st.na} IRScalar.undef_ {st.mem})"
        step = (f"(ir_mem_ext_trans mem na {st.mem} {st.na} {st.ext} {cell0} "
                f"(Nat.succ {st.na}) {one})")
        hcb = f"({self.hcb} {cell0} (Nat.succ {st.na}) {step})"
        return (f"{st.mem} {self.field} {self.base} {st.na} "
                f"{st.framed_lt(self.field, self.hlt)} {h} {hcb}")

    def proof(self, cfg: str, st: State, rest, mint: Mint) -> str:
        d, r = f"(ir_nl1 {self.dest})", mint.stack(cfg)
        nx = self.after(st)
        v = ptr_val(f"(IRScalar.ptr_ {child_of(self.base)})")
        m3, n3, v3, hq = (f"m{self.tag}", f"n{self.tag}", f"v{self.tag}", f"hq{self.tag}")
        # The post is EXACT, so the resume point is known outside the
        # continuation and the segment binds nothing new.
        inner = mint.resume(rest, ret_to(d, r, nx.mem, nx.na, v), nx, [])
        motive = (f"(fun ({m3} : {MEM_TY}) ({n3} : Nat) ({v3} : IRList IRScalar) => "
                  f"{safe(ret_to(d, r, m3, n3, v3))})")
        k = (f"(fun ({m3} : {MEM_TY}) ({n3} : Nat) ({v3} : IRList IRScalar) "
             f"({hq} : ir_post_exact {nx.mem} {nx.na} {v} {m3} {n3} {v3}) => "
             f"{hq} {motive} {inner})")
        return f"(ir_lzd_deref_ctr {self.args(st)} n G {d} {r} {k})"


class RecC:
    """One recursive activation, discharged by the group hypothesis at `n`."""

    def __init__(self, tag: str, dest: str, answer: str, ih: str):
        self.tag, self.dest, self.answer, self.ih = tag, dest, answer, ih

    def names(self):
        t = self.tag
        return f"m{t}", f"n{t}", f"e{t}", f"vs{t}", f"hq{t}", f"hv{t}"

    def after(self, st: State) -> State:
        mo, no, eo, *_ = self.names()
        return State(mo, no, f"(ir_mem_ext_trans mem na {st.mem} {st.na} {st.ext} {mo} {no} {eo})")

    def proof(self, cfg: str, st: State, rest, mint: Mint) -> str:
        d, r = f"(ir_nl1 {self.dest})", mint.stack(cfg)
        mo, no, eo, vs, hq, hv = self.names()
        val = bool_val(self.answer)
        # The returned heap is known only inside the continuation: the segment
        # binds it, its counter, and the MemExt witness the post hands over.
        bound = [(mo, MEM_TY), (no, "Nat"), (eo, f"MemExt {st.mem} {st.na} {mo} {no}")]
        inner = mint.resume(rest, ret_to(d, r, mo, no, val), self.after(st), bound)
        motive = f"(fun (v : IRList IRScalar) => {safe(ret_to(d, r, mo, no, 'v'))})"
        k = (
            f"(fun ({mo} : {MEM_TY}) ({no} : Nat) ({vs} : IRList IRScalar) "
            f"({hq} : ir_lzd_zpost {st.mem} {st.na} {self.answer} {mo} {no} {vs}) => "
            f"{hq} ({safe(ret_to(d, r, mo, no, vs))}) "
            f"(fun ({eo} : MemExt {st.mem} {st.na} {mo} {no}) "
            f"({hv} : Eq (IRList IRScalar) {vs} {val}) => "
            f"Eq.subst (IRList IRScalar) {motive} {val} {vs} "
            f"(Eq.symm (IRList IRScalar) {vs} {val} {hv}) {inner}))"
        )
        return f"({self.ih} G {d} {r} {k})"


class Final:
    """The body's own `ret`: the last literal run lands on the caller's continuation."""

    def __init__(self, count: str, answer: str):
        self.count, self.answer = count, answer

    def proof(self, cfg: str, st: State) -> str:
        val = bool_val(self.answer)
        landed = ret_to("dests", "rest", st.mem, st.na, val)
        post = f"(ir_lzd_zpost_intro mem na {self.answer} {st.mem} {st.na} {st.ext})"
        return (
            f"(ir_safe_pad G {M} n {self.count} {cfg} "
            f"(ir_safe_down G {M} n {landed} (hK {st.mem} {st.na} {val} {post})))"
        )


def chain(segs, cfg: str, st: State, mint: Mint) -> str:
    """A proof of `ir_safe G M n cfg`, walking `segs` from `cfg` in state `st`
    up to and including the next call; what follows it is `mint`'s."""
    head, rest = segs[0], segs[1:]
    if isinstance(head, Final):
        assert not rest, "the body's ret ends the chain"
        return head.proof(cfg, st)
    if isinstance(head, Lit):
        return f"(ir_safe_pad G {M} n {head.count} {cfg} {chain(rest, steps(head.count, cfg), st, mint)})"
    return head.proof(cfg, st, rest, mint)


def sseg(name: str, binders: str, hyps: str, slot: str, first: int, segs, answer: str) -> list:
    """One step-indexed local obligation: the body's contract at `Nat.succ n`,
    as `[(name, source)]` -- its resume segments first, then the obligation.

    The first literal run starts with the body's load; the budget pays for
    exactly that one step (`ir_safe` at `succ n` of a running machine IS
    `ir_safe` at `n` of its successor), and the load's slot is substituted
    exactly as the exact chain does.
    """
    goal_post = zpost("mem", "na", answer)
    kty = (
        f"forall (mem2 : {MEM_TY}) (na2 : Nat) (vs : IRList IRScalar), "
        f"ir_lzd_zpost mem na {answer} mem2 na2 vs -> "
        f"ir_safe G {M} (Nat.succ n) (ir_ret_to dests rest mem2 na2 vs)"
    )
    cfg0 = "(ir_lzd_after_load mem a na dests rest o)"
    cfg_slot = f"(ir_lzd_after_load mem a na dests rest {slot})"
    lookup = "(ir_mem_lookup mem a)"
    body = [Lit(f"ir_d{first - 1}")] + segs
    intro = [("G", "IROutcome -> Prop"), ("dests", "IRList Nat"), ("rest", "IRList IRFrame"),
             ("hK", kty)]
    mint = Mint(name, split_binders(binders + hyps) + intro)
    proof = (
        f"fun (G : IROutcome -> Prop) (dests : IRList Nat) (rest : IRList IRFrame) "
        f"(hK : {kty}) => "
        f"Eq.subst {SLOT_TY} (fun (o : {SLOT_TY}) => {safe(cfg0)}) {slot} {lookup} "
        f"(Eq.symm {SLOT_TY} {lookup} {slot} h) {chain(body, cfg_slot, ENTRY, mint)}"
    )
    concl = ctr(entry0("mem", "(IRScalar.ptr_ a)", "na"), goal_post, "(Nat.succ n)")
    return mint.minted() + [(name, f"def {name} {binders}{hyps}: {concl} := {proof}")]


def rec_hyp(name: str, st: State, base: str, answer: str) -> str:
    kid = f"(IRScalar.ptr_ {child_of(base)})"
    return f"({name} : {ctr(entry0(st.mem, kid, st.na), zpost(st.mem, st.na, answer), 'n')}) "


def max_true_sseg() -> str:
    d1 = DerefC("1", nat_add("a", "ir_d8"), "ir_d12", "b1", "hlt8", "h8", "hcb1")
    s1 = d1.after(ENTRY)
    r1 = RecC("A", "ir_d13", "Bool.true", "ih1")
    s2 = r1.after(s1)
    d2 = DerefC("2", nat_add("a", "ir_d16"), "ir_d18", "b2", "hlt16", "h16", "hcb2")
    s3 = d2.after(s2)
    r2 = RecC("B", "ir_d19", "ans2", "(ih2 mA nA eA)")
    segs = [d1, Lit("ir_d1"), r1, Lit("ir_d2"), d2, Lit("ir_d1"), r2, Final("ir_d3", "ans2")]
    kid2 = f"(IRScalar.ptr_ {child_of('b2')})"
    ih2 = (
        f"(ih2 : forall (mA : {MEM_TY}) (nA : Nat), MemExt {s1.mem} {s1.na} mA nA -> "
        f"{ctr(entry0(s3.mem, kid2, s3.na), zpost(s3.mem, s3.na, 'ans2'), 'n')}) "
    )
    binders = (f"(mem : {MEM_TY}) (a : Nat) (b1 : Nat) (b2 : Nat) (ans2 : Bool) (na : Nat) "
               f"(n : Nat) ")
    hyps = common("ir_d2", True) + rec_hyp("ih1", s1, "b1", "Bool.true") + ih2
    return sseg("ir_lzd_max_true_sseg", binders, hyps, MAX_SLOT, 8, segs, "ans2")


def max_false_sseg() -> str:
    d1 = DerefC("1", nat_add("a", "ir_d8"), "ir_d12", "b1", "hlt8", "h8", "hcb1")
    s1 = d1.after(ENTRY)
    r1 = RecC("A", "ir_d13", "Bool.false", "ih1")
    segs = [d1, Lit("ir_d1"), r1, Final("ir_d5", "Bool.false")]
    binders = f"(mem : {MEM_TY}) (a : Nat) (b1 : Nat) (b2 : Nat) (na : Nat) (n : Nat) "
    hyps = common("ir_d2", True) + rec_hyp("ih1", s1, "b1", "Bool.false")
    return sseg("ir_lzd_max_false_sseg", binders, hyps, MAX_SLOT, 8, segs, "Bool.false")


def imax_sseg() -> str:
    d2 = DerefC("2", nat_add("a", "ir_d16"), "ir_d16", "b2", "hlt16", "h16", "hcb2")
    s1 = d2.after(ENTRY)
    r2 = RecC("A", "ir_d17", "ans2", "ih2")
    segs = [d2, Lit("ir_d1"), r2, Final("ir_d2", "ans2")]
    binders = (f"(mem : {MEM_TY}) (a : Nat) (b1 : Nat) (b2 : Nat) (ans2 : Bool) (na : Nat) "
               f"(n : Nat) ")
    hyps = common("ir_d3", False) + rec_hyp("ih2", s1, "b2", "ans2")
    return sseg("ir_lzd_imax_sseg", binders, hyps, IMAX_SLOT, 6, segs, "ans2")


# ------------------------------------------------ the Full-bundle assembly
#
# The recursion group {Level::is_zero} as a contract TABLE: index `IRLzdIn`
# (heap, counter, the pointer argument, the Level it represents), precondition
# `EncodesLevelArcD`, entry `ir_lzd_mach0_s`, post `ir_lzd_zpost` at
# `level_is_zero`. The local obligation is a CASE ANALYSIS on the
# representation -- never an induction on it: the recursion is on the BUDGET,
# carried by `ir_ctr_group_sound`, and the children's contracts come from the
# group hypothesis `ih` at the strictly smaller budget `n`, at the heaps the
# derefs allocate (framed with `ir_lzd_frame` / `ir_lzd_frame_ext`).

MEMT = "IRList IRMemSlot"
PC_RS = REPO / "crates/clean-verify/src/spec/core_spec/eval_ir_lzd_pc.rs"


def _lz(lvl: str) -> str:
    return f"(level_is_zero {lvl})"


def _ctr_n(mem: str, s: str, na: str, ans: str, budget: str) -> str:
    return f"ir_ctr_at {M} (ir_lzd_mach0_s {mem} {s} {na}) (ir_lzd_zpost {mem} {na} {ans}) {budget}"


def _in_ctr(x: str, budget: str) -> str:
    return f"ir_ctr_at {M} (ir_lzd_in_entry {x}) (ir_lzd_in_post {x}) {budget}"


IH_TY = f"forall (a : IRLzdIn), ir_lzd_in_pre a -> {_in_ctr('a', 'n')}"


def _slot(a: str, v: str) -> str:
    return f"(IROption.some IRMemSlot (IRMemSlot.mk {a} {v} Bool.true))"


def _look(a: str, v: str) -> str:
    return f"Eq {SLOT_TY} (ir_mem_lookup mem {a}) {_slot(a, v)}"


def _ltb(a: str) -> str:
    return f"Eq Bool (ir_nat_ltb {a} na) Bool.true"


def local_obligation() -> str:
    a8, a16 = nat_add("a0", "ir_d8"), nat_add("a0", "ir_d16")
    p1, p2 = "(IRScalar.ptr_ (Nat.succ b1))", "(IRScalar.ptr_ (Nat.succ b2))"
    kid1, kid2 = f"(IRScalar.ptr_ {child_of('b1')})", f"(IRScalar.ptr_ {child_of('b2')})"
    kidb = f"(IRScalar.ptr_ {child_of('b')})"
    opt1, opt2 = opt_of("b1"), opt_of("b2")
    cell1, cell2 = f"(ir_cell na {opt1} mem)", f"(ir_cell na {opt2} mem)"
    succ_n = "(Nat.succ n)"
    motive = (f"(fun (s0 : IRScalar) (l0 : Level) (_ : EncodesLevelArcD mem na s0 l0) => "
              f"{_ctr_n('mem', 's0', 'na', _lz('l0'), succ_n)})")

    def ih_at(mem: str, na: str, s: str, lvl: str, deriv: str) -> str:
        return f"(ih (IRLzdIn.mk {mem} {na} {s} {lvl}) {deriv})"

    def at_bool(mem: str, s: str, na: str, lvl: str, lit: str, hyp: str, term: str) -> str:
        mot = f"(fun (v : Bool) => {_ctr_n(mem, s, na, 'v', 'n')})"
        return f"(Eq.subst Bool {mot} {_lz(lvl)} {lit} {hyp} {term})"

    v2 = f"(ir_var ir_d2 (ir_sp2 {p1} {p2}))"
    v3 = f"(ir_var ir_d3 (ir_sp2 {p1} {p2}))"
    zero = (f"(fun (a0 : Nat) (hlt : {_ltb('a0')}) (hm : {_look('a0', '(ir_var ir_d0 ir_sp0)')}) => "
            f"ir_lzd_zero_ctr mem a0 na hm {succ_n})")
    vb = f"(ir_var ir_d1 (ir_sp1 (IRScalar.ptr_ (Nat.succ b))))"
    succ = (f"(fun (a0 : Nat) (b : Nat) (l0 : Level) (hlt : {_ltb('a0')}) (hm : {_look('a0', vb)}) "
            f"(_r : EncodesLevelArcD mem na {kidb} l0) (_ih : {_ctr_n('mem', kidb, 'na', _lz('l0'), succ_n)}) => "
            f"ir_lzd_succ_ctr mem a0 na b hm {succ_n})")
    param = (f"(fun (a0 : Nat) (w : IRScalar) (nm : Name) (hlt : {_ltb('a0')}) "
             f"(hm : {_look('a0', '(ir_var ir_d4 (ir_sp1 w))')}) => ir_lzd_param_ctr mem a0 na w hm {succ_n})")
    kids = (f"(r1 : EncodesLevelArcD mem na {kid1} l1) (r2 : EncodesLevelArcD mem na {kid2} l2) "
            f"(_ih1 : {_ctr_n('mem', kid1, 'na', _lz('l1'), succ_n)}) "
            f"(_ih2 : {_ctr_n('mem', kid2, 'na', _lz('l2'), succ_n)})")
    hcb1 = f"(ir_lzd_live_ext mem na {kid1} l1 r1)"
    hcb2 = f"(ir_lzd_live_ext mem na {kid2} l2 r2)"
    ih1 = ih_at(cell1, "(Nat.succ na)", kid1, "l1", f"(ir_lzd_frame mem na {opt1} {kid1} l1 r1)")
    ext_a = f"(ir_mem_ext_trans mem na {cell1} (Nat.succ na) (ir_mem_ext_one mem na {opt1}) mA nA eA)"
    ih2 = (f"(fun (mA : {MEMT}) (nA : Nat) (eA : MemExt {cell1} (Nat.succ na) mA nA) => "
           + ih_at(f"(ir_cell nA {opt2} mA)", "(Nat.succ nA)", kid2, "l2",
                   f"(ir_lzd_frame mA nA {opt2} {kid2} l2 "
                   f"(ir_lzd_frame_ext mem na {kid2} l2 r2 mA nA {ext_a}))") + ")")
    common_args = f"hm hm8 hm16 hlt8 hlt16 {hcb1} {hcb2}"
    false_arm = (f"(fun (hf : Eq Bool {_lz('l1')} Bool.false) => ir_lzd_max_false_sseg mem a0 b1 b2 na n "
                 f"{common_args} {at_bool(cell1, kid1, '(Nat.succ na)', 'l1', 'Bool.false', 'hf', ih1)})")
    true_arm = (f"(fun (ht : Eq Bool {_lz('l1')} Bool.true) => ir_lzd_max_true_sseg mem a0 b1 b2 {_lz('l2')} "
                f"na n {common_args} {at_bool(cell1, kid1, '(Nat.succ na)', 'l1', 'Bool.true', 'ht', ih1)} {ih2})")
    anded = f"(Bool.and v {_lz('l2')})"
    max_body = (
        f"Bool.rec (fun (v : Bool) => Eq Bool {_lz('l1')} v -> "
        f"{_ctr_n('mem', '(IRScalar.ptr_ a0)', 'na', anded, succ_n)}) "
        f"{false_arm} {true_arm} {_lz('l1')} (Eq.refl Bool {_lz('l1')})"
    )
    mx = (f"(fun (a0 : Nat) (b1 : Nat) (b2 : Nat) (l1 : Level) (l2 : Level) (hlt : {_ltb('a0')}) "
          f"(hlt8 : {_ltb(a8)}) (hlt16 : {_ltb(a16)}) (hm : {_look('a0', v2)}) "
          f"(hm8 : {_look(a8, p1)}) (hm16 : {_look(a16, p2)}) {kids} => {max_body})")
    ih2i = ih_at(cell2, "(Nat.succ na)", kid2, "l2", f"(ir_lzd_frame mem na {opt2} {kid2} l2 r2)")
    imx = (f"(fun (a0 : Nat) (b1 : Nat) (b2 : Nat) (l1 : Level) (l2 : Level) (hlt : {_ltb('a0')}) "
           f"(hlt16 : {_ltb(a16)}) (hm : {_look('a0', v3)}) (hm16 : {_look(a16, p2)}) {kids} => "
           f"ir_lzd_imax_sseg mem a0 b1 b2 {_lz('l2')} na n hm hm16 hlt16 {hcb2} {ih2i})")
    inner = (f"(fun (mem : {MEMT}) (na : Nat) (s : IRScalar) (l : Level) "
             f"(d : EncodesLevelArcD mem na s l) => EncodesLevelArcD.rec mem na {motive} "
             f"{zero} {succ} {mx} {imx} {param} s l d)")
    return (
        f"def ir_lzd_local (n : Nat) (ih : {IH_TY}) : forall (x : IRLzdIn), ir_lzd_in_pre x -> "
        f"{_in_ctr('x', succ_n)} := fun (x : IRLzdIn) => IRLzdIn.rec "
        f"(fun (x0 : IRLzdIn) => ir_lzd_in_pre x0 -> {_in_ctr('x0', succ_n)}) {inner} x"
    )


def partial_correctness() -> str:
    im = "(ir_lzd_init_mem mem)"
    s = "(IRScalar.ptr_ a)"
    ans = _lz("l0")
    val = f"(ir_vl1 (IRScalar.bool_ {ans}))"
    goal = f"(fun (o2 : IROutcome) => Eq IROutcome o2 (IROutcome.ret {val}))"
    hq = (
        f"(fun (mem2 : {MEMT}) (na2 : Nat) (vs : IRList IRScalar) "
        f"(hz : ir_lzd_zpost {im} na {ans} mem2 na2 vs) => "
        f"hz (Eq IROutcome (IROutcome.ret vs) (IROutcome.ret {val})) "
        f"(fun (_ : MemExt {im} na mem2 na2) (hv : Eq (IRList IRScalar) vs {val}) => "
        f"ir_eq_cong (IRList IRScalar) IROutcome IROutcome.ret vs {val} hv))"
    )
    minor = (
        f"(fun (a : Nat) (l0 : Level) (arc : EncodesLevelArcD {im} na {s} l0) => "
        f"ir_ctr_run {M} (ir_lzd_mach0_s {im} {s} na) (ir_lzd_zpost {im} na {ans}) fuel "
        f"(ir_lzd_ctr fuel (IRLzdIn.mk {im} na {s} l0) arc) {goal} (IRList.nil Nat) {hq})"
    )
    return (
        "def ir_lzd_pc (mem : IRList IRMemSlot) (fuel : Nat) (na : Nat) (r : IRScalar) (l : Level) "
        f"(href : EncodesLiveLevelRefD {im} na r l) : "
        f"ir_lzd_pc_ok {_lz('l')} (ir_eval fuel {M} ir_d0 (ir_vl1 r) mem na) := "
        f"EncodesLiveLevelRefD.rec {im} na (fun (s0 : IRScalar) (l1 : Level) "
        f"(_ : EncodesLiveLevelRefD {im} na s0 l1) => "
        f"ir_lzd_pc_ok {_lz('l1')} (ir_eval fuel {M} ir_d0 (ir_vl1 s0) mem na)) {minor} r l href"
    )


# The three body obligations mint FAMILIES -- their resume segments, then the
# obligation -- in the order the Rust stage registers them (a segment before
# every lemma that applies it). The table's two terms are single declarations.
FAMILIES = (imax_sseg, max_false_sseg, max_true_sseg)
SINGLES = {
    "SRC_IR_LZD_LOCAL": local_obligation,
    "SRC_IR_LZD_PC": partial_correctness,
}
TARGETS = (SCTR_RS, PC_RS)


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


# The terms a kernel accepted. `--self-test` recomputes them and compares these
# digests, so a refactor that changes the emitted SHAPE fails in a second
# rather than in a bundle build.
PINNED_DIGESTS: dict = {
    "SRC_IR_LZD_IMAX_SSEG": "96b669708eced313eb4f8a782fda876763beb247ac4b06d624707762a9b06d81",
    "SRC_IR_LZD_IMAX_SSEG_R1": "a4ad2946751fccdd9595f7e7cacb7fcde1228bb6c82b8d67d6e2d2ac3eb91c88",
    "SRC_IR_LZD_IMAX_SSEG_R2": "e2515a321e9d1d58fc2c3ced1a0c7e1375f9486ea783bbcc51b82f3024ab043c",
    "SRC_IR_LZD_IMAX_SSEG_ST1": "34e267ce6fedf7c9b3f72414e97038081c2a627e7a4a49cd25285deb36b83924",
    "SRC_IR_LZD_IMAX_SSEG_ST2": "cbc2195a88f4dfe00c0cb710172f49df6c88c7be7c9faab4533681b5f0251d5b",
    "SRC_IR_LZD_LOCAL": "92223a99584172d95cce427a2a0d4b57fa297d24f3665b9e971ed29eb908d77a",
    "SRC_IR_LZD_MAX_FALSE_SSEG": "b9231efdb7e80d3e86c4423bf0061dd2279c8ec54792fa7998b0dd43c305609c",
    "SRC_IR_LZD_MAX_FALSE_SSEG_R1": "9f75b9ea46190844556fb537405db7021c9620c24323e79b8facfe154be6707e",
    "SRC_IR_LZD_MAX_FALSE_SSEG_R2": "2ad6300ccbbc125ee6abbc31fa64f7d7c8826ad4cbbdf6fd7c0975dc215cae85",
    "SRC_IR_LZD_MAX_FALSE_SSEG_ST1": "bd779d2f175387af596694723b7a1daaec9e7192fe58593fb6f213c3a9661f4d",
    "SRC_IR_LZD_MAX_FALSE_SSEG_ST2": "88de8549c29c64f184885fdfea0c468ae4fd06cc66aef44a13d37a17477b3482",
    "SRC_IR_LZD_MAX_TRUE_SSEG": "cb71e67a83466eb951ba0b13fde8762aafa43379565dd5368274cbb80dada2ad",
    "SRC_IR_LZD_MAX_TRUE_SSEG_R1": "4465a2e8ae30f6cb1461cba47d58b2f6d0bc703a3910e1a2ed54cc862244d66b",
    "SRC_IR_LZD_MAX_TRUE_SSEG_R2": "ac6effac081354fda5a09a067c4185cbcb16875b4c8b60d2d7cf37e3033e5ad1",
    "SRC_IR_LZD_MAX_TRUE_SSEG_R3": "c987d72e2ec7860f1e998bb549f44794c08ba6fb94afcc820e6fc3aa3532dd84",
    "SRC_IR_LZD_MAX_TRUE_SSEG_R4": "6734a7ee4674958b71ce3687ff139bf58dd40f90a74dffe7058d681d76efdf50",
    "SRC_IR_LZD_MAX_TRUE_SSEG_ST1": "c666cae3fc9182c95ff11069a90b9df8c30e649c40140ba86a0a318fba826daa",
    "SRC_IR_LZD_MAX_TRUE_SSEG_ST2": "8e6eeb3f98e9b65c58cebc3dfce4c7400bd3303f3472e330a5263cde1e3f4a1c",
    "SRC_IR_LZD_MAX_TRUE_SSEG_ST3": "2f0f0a7a1406b0175bf58c9a40294fffde21a192371d27ebcae7f88489ea8e6e",
    "SRC_IR_LZD_MAX_TRUE_SSEG_ST4": "c851c5c4817c9e7569cc818636ba119e29755e35c48ba24d7db5d3c59d042aea",
    "SRC_IR_LZD_PC": "ea2be291148ea94500cf6087aaa10941a838de8ac12cdf152d7da56aaae3b8d6",
}

# The NESTED obligations the kernel accepted on 2026-09-24 (E2), before they
# were minted one lemma per call. With `SEGMENTED = False` the emitter must
# still reproduce them byte for byte: the segmented terms are cut from the
# same vocabulary, and this is what says so.
LEGACY_DIGESTS: dict = {
    "SRC_IR_LZD_IMAX_SSEG": "0c59269f6684df7a4fc9a9ba018c09390d057b60bb04920be0144680040b6d95",
    "SRC_IR_LZD_MAX_FALSE_SSEG": "c65d5a8bec81fb5b825ede3a01011ab01600aabfe8d327af5acd5ad298c3ee23",
    "SRC_IR_LZD_MAX_TRUE_SSEG": "268c14939808368b697f8bd39d7e9df1f359cf55a35044cf53932f0e84c88884",
}


def legacy() -> dict:
    """The nested obligations, as the 2026-09-24 emitter wrote them."""
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


# The heads the committed consts name with an explicit `@` (the spelling the
# explicit-prefix EvalIR commits, 1b6b65dc83 and after, gave them), and the one
# const whose committed source keeps a head bare. Recorded, not chosen: making
# it uniform is a source change the EvalIR initializer would have to accept.
XP = _act.XP
EXPLICIT_HEADS = frozenset({
    "Bool.rec", "EncodesLevelArcD.rec", "EncodesLiveLevelRefD.rec", "Eq", "Eq.refl",
    "Eq.subst", "Eq.symm", "Eq.trans", "IRList.nil", "IRLzdIn.rec", "IROption.some",
    "MemExt.refl",
})
KEPT_BARE = {
    "SRC_IR_LZD_LOCAL": frozenset({"Eq.subst"}),
}


def spell(name: str, term: str) -> str:
    """One built obligation as the tree registers it."""
    return XP.respell(term, EXPLICIT_HEADS - KEPT_BARE.get(name, frozenset()))


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
    ap.add_argument("--pinned-inputs", action="store_true", help="list exact source/control inputs")
    a = ap.parse_args()
    if a.pinned_inputs:
        if any(value for key, value in vars(a).items() if key != "pinned_inputs"):
            ap.error("--pinned-inputs cannot be combined with another action")
        print("\n".join(HELPER_INPUTS))
        return 0
    built = legacy() if a.legacy else minted()
    printed = built if a.legacy else {k: spell(k, v) for k, v in built.items()}
    if a.name:
        key = a.name if a.name.startswith("SRC_") else "SRC_" + a.name.upper()
        print(printed[key])
        return 0
    if a.emit:
        bad = _ascii_balanced(printed)
        for line in bad:
            print(line)
        if bad:
            return 1
        n = 0
        for f in TARGETS:
            src = f.read_text()
            for k, v in printed.items():
                pat = re.compile(r'const %s: &str = ".*?";\n' % k, re.S)
                if pat.search(src):
                    src = pat.sub(lambda _m, k=k, v=v: f'const {k}: &str = "{v}";\n', src)
                    n += 1
            f.write_text(src)
        print(f"emitted {n} terms")
        return 0 if n == len(printed) else 1
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
        drift = _coverage_invariant(built) + _ascii_balanced(built) + XP.self_test()
        drift += [f"KEPT_BARE: {k} is not a minted const" for k in sorted(set(KEPT_BARE) - set(built))]
        for k in bad:
            print(f"DIGEST MOVED: {k}")
        for k in moved:
            print(f"LEGACY NOT REPRODUCED: {k} (the nested form the kernel accepted 2026-09-24)")
        for line in drift:
            print(line)
        ok = not bad and not moved and not drift
        if ok:
            _helper_source_controls()
        print("gen_lzd_sctr --self-test: " + ("OK" if ok else "FAILED"))
        return 0 if ok else 1
    if a.check:
        have = committed()
        bad = [k for k in printed if have.get(k) != printed[k]]
        for k in bad:
            print(f"DIFFERS: {k}")
        order = registration_order(printed)
        for line in order:
            print(line)
        print("gen_lzd_sctr: " + ("OK" if not bad and not order else f"{len(bad) + len(order)} differ"))
        return 1 if bad or order else 0
    ap.print_help()
    return 2


if __name__ == "__main__":
    sys.exit(main())
