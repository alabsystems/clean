#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Mint the three `ir_lzb_*_seg` activation-segment proof terms.

WHY THIS EXISTS
---------------
`crates/clean-verify/src/spec/core_spec/eval_ir_lzb_activation.rs` carries three
proof terms totalling ~42k characters — `ir_lzb_max_true_seg`,
`ir_lzb_max_false_seg`, `ir_lzb_imax_seg`. They are not hand-reasoned prose:
each is one mechanical chain over a list of execution SEGMENTS, alternating
literal runs the machine computes with opaque runs discharged by a lemma
(the deref-model activation, or a recursion hypothesis).

Hand-editing them is how an off-by-one gets into a kernel-checked chain and is
found an hour later in a spec build. This script states the segments as DATA and
emits the terms, so a change to the deref model's cost is a change to one
number.

THE PROOF SHAPE, ONCE
---------------------
A segment lemma proves, for the emitted `Level::is_zero` body entered at `a`:

    ir_steps (((sN + ...) + s2) + s1) M (running (mach0 mem a na dests rest))
      = ir_ret_to dests rest mem na <answer>

`s1` executes FIRST (`ir_steps (x+y) M c = ir_steps x M (ir_steps y M c)`).
Step one of the whole run is the body's `load`, so the proof rewrites the root
memory lookup with `Eq.subst` and then works over `ir_lzb_after_load`, whose
first segment is one step shorter.

Then, per segment, right-nested:

  * split it off the front with `ir_steps_add`;
  * a LITERAL segment needs nothing more — the config `ir_steps s M c` is left
    unevaluated and carried forward, and the kernel computes through it;
  * an OPAQUE segment (a callee activation) is replaced by its lemma's RHS with
    `Eq.subst` + `Eq.symm`, and THAT becomes the config carried forward.

The final segment is discharged by `Eq.refl`: the machine computes it.

The frame stack each callee sits on is never written out — it is named
`ir_frames_tail (ir_config_frames <the config so far>)`, exact by construction.

THE SPELLING
------------
The lemmas are built without explicit prefixes; that is the shape the self-test
pins. What the tree registers is that text printed by `scripts/explicit_prefix.py`
with `@` before every head in `EXPLICIT_HEADS` (the spelling 1b6b65dc83 gave
these consts), and `--print`, `--emit` and `--check` speak the printed text.

USAGE
-----
    python3 scripts/gen_lzb_activation.py --check   # byte-compare with the tree
    python3 scripts/gen_lzb_activation.py --print <name>
    python3 scripts/gen_lzb_activation.py --emit    # rewrite the Rust consts
"""

from __future__ import annotations

import argparse
import importlib.util
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

ANSWERS_PINNED_INPUTS = True
HELPER_INPUTS = ('scripts/test_generator_source_helpers.py', 'scripts/resource_transport.py', 'scripts/explicit_prefix.py', 'crates/clean-verify/src/spec/core_spec/eval_ir_lzb_activation.rs')


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

ACTIVATION_RS = REPO / "crates/clean-verify/src/spec/core_spec/eval_ir_lzb_activation.rs"

XP = _source_module("explicit_prefix", REPO / "scripts/explicit_prefix.py")

M = "ir_lzb_module"
SLOT_TY = "(IROption IRMemSlot)"
TARGET_FRAMES = "dests rest mem na"

# --------------------------------------------------------------- the deref model
#
# Both numbers below describe ONE thing: the authored `<LevelArc as Deref>::deref`
# model at function 1 of `ir_lzb_module`. Change them together with the model.

# Steps in one activation of the deref model, from its frame push to the
# caller's resumption. Seven nodes: load, const null, icmp, assert, const 16,
# gep, ret.
DEREF_STEPS = "ir_d7"

# What the deref model returns, given a field cell holding `IRScalar.ptr_ b`.
# The Arc's DATA address: the stored word plus the `ArcInner` header
# (strong + weak, 8 bytes each on this target) — ledger row
# A-CLZ-DEREF-ARC-DATA-OFFSET, measured 16 by
# `deref_model_arc_data_offset_is_what_the_model_assumes`.
def deref_result(b: str) -> str:
    return f"(IRScalar.ptr_ (Nat.add {b} ir_d16))"


def child_of(b: str) -> str:
    """The cell the recursive call runs at, given a field holding `ptr b`."""
    return f"(Nat.add {b} ir_d16)"


# ------------------------------------------------------------------- primitives


def steps(n: str, c: str) -> str:
    return f"(ir_steps {n} {M} {c})"


def nat_add(a: str, b: str) -> str:
    return f"(Nat.add {a} {b})"


def eq_cfg(lhs: str, rhs: str) -> str:
    return f"Eq IRConfig {lhs} {rhs}"


def ret_to(dests: str, rest: str, val: str) -> str:
    return f"(ir_ret_to {dests} {rest} mem na {val})"


def frames_after(cfg: str) -> str:
    return f"(ir_frames_tail (ir_config_frames {cfg}))"


def bool_val(b: str) -> str:
    return f"(ir_vl1 (IRScalar.bool_ {b}))"


def ptr_val(p: str) -> str:
    return f"(ir_vl1 {p})"


# --------------------------------------------------------------------- segments


class Lit:
    """A literal run of steps the kernel computes through."""

    def __init__(self, count: str):
        self.count = count
        self.opaque = False


class Deref:
    """One activation of the authored deref model, at a field cell."""

    def __init__(self, field: str, dest: str, base: str, hyp: str):
        self.count = DEREF_STEPS
        self.opaque = True
        self.field = field
        self.dest = dest
        self.base = base
        self.hyp = hyp

    def result(self, cfg: str) -> str:
        return ret_to(f"(ir_nl1 {self.dest})", frames_after(cfg), ptr_val(deref_result(self.base)))

    def lemma(self, cfg: str) -> str:
        return (
            f"(ir_lzb_deref_activation mem {self.field} na (ir_nl1 {self.dest}) "
            f"{frames_after(cfg)} {self.base} {self.hyp})"
        )


class Rec:
    """One activation of the body itself, discharged by a recursion hypothesis."""

    def __init__(self, count: str, dest: str, answer: str, ih: str):
        self.count = count
        self.opaque = True
        self.dest = dest
        self.answer = answer
        self.ih = ih

    def result(self, cfg: str) -> str:
        return ret_to(f"(ir_nl1 {self.dest})", frames_after(cfg), bool_val(self.answer))

    def lemma(self, cfg: str) -> str:
        return f"({self.ih} na (ir_nl1 {self.dest}) {frames_after(cfg)})"


def total(segs) -> str:
    """The cost expression: last-executed outermost, first-executed rightmost."""
    expr = segs[-1].count
    for s in reversed(segs[:-1]):
        expr = nat_add(expr, s.count)
    return expr


def remaining(segs, i: int) -> str:
    """Cost of segments i..n-1, i.e. everything not yet peeled."""
    return total(segs[i:])


def chain(segs, cfg: str, target: str) -> str:
    """The right-nested peel over `segs`, starting at config `cfg`."""
    if len(segs) == 1:
        return f"(Eq.refl IRConfig {target})"
    head, rest = segs[0], segs[1:]
    after = remaining(segs, 1)
    stepped = steps(head.count, cfg)
    split = f"(ir_steps_add {M} {after} {head.count} {cfg})"
    if head.opaque:
        value = head.result(cfg)
        inner = chain(rest, value, target)
        body = (
            f"(Eq.subst IRConfig (fun (k : IRConfig) => {eq_cfg(steps(after, 'k'), target)}) "
            f"{value} {stepped} "
            f"(Eq.symm IRConfig {stepped} {value} {head.lemma(cfg)}) {inner})"
        )
    else:
        body = chain(rest, stepped, target)
    return (
        f"(Eq.trans IRConfig {steps(remaining(segs, 0), cfg)} {steps(after, stepped)} "
        f"{target} {split} {body})"
    )


def segment_lemma(name: str, binders: str, hyps: str, slot: str, segs, target: str) -> str:
    """One `ir_lzb_*_seg` declaration, statement and proof.

    `segs[0]` is the body's own `load`, which the head rewrite consumes: the
    statement counts it, the chain does not.
    """
    load, rest = segs[0], segs[1:]
    assert not load.opaque, "the first segment is the body's load"
    assert load.count.startswith("ir_d"), "the load segment is a literal run"
    shortened = int(load.count[len("ir_d"):]) - 1
    body_segs = [Lit(f"ir_d{shortened}")] + rest

    stmt_cost = total([load] + rest)
    motive_cost = total(body_segs)
    cfg0 = "(ir_lzb_after_load mem a na dests rest o)"
    cfg_slot = f"(ir_lzb_after_load mem a na dests rest {slot})"
    lookup = "(ir_mem_lookup mem a)"

    proof = (
        f"Eq.subst {SLOT_TY} "
        f"(fun (o : {SLOT_TY}) => {eq_cfg(steps(motive_cost, cfg0), target)}) "
        f"{slot} {lookup} "
        f"(Eq.symm {SLOT_TY} {lookup} {slot} h) "
        f"{chain(body_segs, cfg_slot, target)}"
    )
    concl = eq_cfg(
        steps(stmt_cost, "(IRConfig.running (ir_lzb_mach0 mem a na dests rest))"), target
    )
    return f"def {name} {binders}{hyps}: {concl} := {proof}"


# ------------------------------------------------------------------ the lemmas

MEM_AT = (
    "Eq (IROption IRMemSlot) (ir_mem_lookup mem {addr}) "
    "(IROption.some IRMemSlot (IRMemSlot.mk {addr} {val} Bool.true))"
)


def field_hyp(name: str, off: str, val: str) -> str:
    addr = nat_add("a", off)
    return f"({name} : {MEM_AT.format(addr=addr, val=val)}) "


def ih_hyp(name: str, cost: str, base: str, answer: str) -> str:
    """A recursion hypothesis, quantified over the caller's whole continuation.

    It is about the CHILD cell — the Arc's data address — because that is what
    the deref hands to the recursive call.
    """
    return (
        f"({name} : forall (na2 : Nat) (d2 : IRList Nat) (r2 : IRList IRFrame), "
        + eq_cfg(
            steps(cost, f"(IRConfig.running (ir_lzb_mach0 mem {child_of(base)} na2 d2 r2))"),
            ret_to("d2", "r2", bool_val(answer)).replace("mem na ", "mem na2 "),
        )
        + ") "
    )


def slot_of(tag: str, payload: str) -> str:
    return f"(IROption.some IRMemSlot (IRMemSlot.mk a (ir_var {tag} {payload}) Bool.true))"


PAIR = "(ir_sp2 (IRScalar.ptr_ b1) (IRScalar.ptr_ b2))"
MAX_SLOT = slot_of("ir_d2", PAIR)
IMAX_SLOT = slot_of("ir_d3", PAIR)

H8 = field_hyp("h8", "ir_d8", "(IRScalar.ptr_ b1)")
H16 = field_hyp("h16", "ir_d16", "(IRScalar.ptr_ b2)")
H_ROOT_MAX = f"(h : {MEM_AT.format(addr='a', val=f'(ir_var ir_d2 {PAIR})')}) "
H_ROOT_IMAX = f"(h : {MEM_AT.format(addr='a', val=f'(ir_var ir_d3 {PAIR})')}) "


def max_true_seg() -> str:
    segs = [
        Lit("ir_d8"),
        Deref(nat_add("a", "ir_d8"), "ir_d12", "b1", "h8"),
        Lit("ir_d1"),
        Rec("c1", "ir_d13", "Bool.true", "ih1"),
        Lit("ir_d2"),
        Deref(nat_add("a", "ir_d16"), "ir_d18", "b2", "h16"),
        Lit("ir_d1"),
        Rec("c2", "ir_d19", "ans2", "ih2"),
        Lit("ir_d3"),
    ]
    binders = (
        "(mem : IRList IRMemSlot) (a : Nat) (b1 : Nat) (b2 : Nat) (c1 : Nat) (c2 : Nat) "
        "(ans2 : Bool) (na : Nat) (dests : IRList Nat) (rest : IRList IRFrame) "
    )
    hyps = (
        H_ROOT_MAX
        + H8
        + H16
        + ih_hyp("ih1", "c1", "b1", "Bool.true")
        + ih_hyp("ih2", "c2", "b2", "ans2")
    )
    return segment_lemma(
        "ir_lzb_max_true_seg", binders, hyps, MAX_SLOT, segs, ret_to("dests", "rest", bool_val("ans2"))
    )


def max_false_seg() -> str:
    segs = [
        Lit("ir_d8"),
        Deref(nat_add("a", "ir_d8"), "ir_d12", "b1", "h8"),
        Lit("ir_d1"),
        Rec("c1", "ir_d13", "Bool.false", "ih1"),
        Lit("ir_d5"),
    ]
    binders = (
        "(mem : IRList IRMemSlot) (a : Nat) (b1 : Nat) (b2 : Nat) (c1 : Nat) (na : Nat) "
        "(dests : IRList Nat) (rest : IRList IRFrame) "
    )
    hyps = H_ROOT_MAX + H8 + ih_hyp("ih1", "c1", "b1", "Bool.false")
    return segment_lemma(
        "ir_lzb_max_false_seg",
        binders,
        hyps,
        MAX_SLOT,
        segs,
        ret_to("dests", "rest", bool_val("Bool.false")),
    )


def imax_seg() -> str:
    segs = [
        Lit("ir_d6"),
        Deref(nat_add("a", "ir_d16"), "ir_d16", "b2", "h16"),
        Lit("ir_d1"),
        Rec("c2", "ir_d17", "ans2", "ih2"),
        Lit("ir_d2"),
    ]
    binders = (
        "(mem : IRList IRMemSlot) (a : Nat) (b1 : Nat) (b2 : Nat) (c2 : Nat) (ans2 : Bool) "
        "(na : Nat) (dests : IRList Nat) (rest : IRList IRFrame) "
    )
    hyps = H_ROOT_IMAX + H16 + ih_hyp("ih2", "c2", "b2", "ans2")
    return segment_lemma(
        "ir_lzb_imax_seg", binders, hyps, IMAX_SLOT, segs, ret_to("dests", "rest", bool_val("ans2"))
    )


def deref_activation() -> str:
    """The assumed callee, frame-generic: one activation of the deref model.

    Its ONE hypothesis is that the field cell holds a live pointer — the Arc
    allocation base. What it returns is `deref_result` of that base, so this
    lemma and the model it describes move together.
    """
    slot = (
        "(IROption.some IRMemSlot (IRMemSlot.mk p (IRScalar.ptr_ b) Bool.true))"
    )
    lookup = "(ir_mem_lookup mem p)"
    out = ptr_val(deref_result("b"))
    target = ret_to("dests", "rest", out)
    inner = int(DEREF_STEPS[len("ir_d"):]) - 1
    cfg = "(ir_lzb_dafter_load mem p na dests rest o)"
    return (
        "def ir_lzb_deref_activation (mem : IRList IRMemSlot) (p : Nat) (na : Nat) "
        "(dests : IRList Nat) (rest : IRList IRFrame) (b : Nat) "
        f"(h : Eq (IROption IRMemSlot) {lookup} {slot}) : "
        + eq_cfg(
            steps(DEREF_STEPS, "(IRConfig.running (ir_lzb_dmach mem p na dests rest))"), target
        )
        + f" := Eq.subst {SLOT_TY} "
        f"(fun (o : {SLOT_TY}) => {eq_cfg(steps(f'ir_d{inner}', cfg), target)}) "
        f"{slot} {lookup} (Eq.symm {SLOT_TY} {lookup} {slot} h) "
        f"(Eq.refl IRConfig {target})"
    )


LEMMAS = {
    "SRC_IR_LZB_DEREF_ACTIVATION": deref_activation,
    "SRC_IR_LZB_MAX_TRUE_SEG": max_true_seg,
    "SRC_IR_LZB_MAX_FALSE_SEG": max_false_seg,
    "SRC_IR_LZB_IMAX_SEG": imax_seg,
}

# The heads the committed consts name with an explicit `@`, in every const.
EXPLICIT_HEADS = frozenset({"Eq", "Eq.refl", "Eq.subst", "Eq.symm", "Eq.trans", "IROption.some"})


def spelled() -> dict:
    """Every lemma as the tree registers it: the built term, printed with its prefixes."""
    return {name: XP.respell(fn(), EXPLICIT_HEADS) for name, fn in LEMMAS.items()}


def committed() -> dict:
    src = ACTIVATION_RS.read_text()
    found = dict(re.findall(r'const (SRC_[A-Z0-9_]+): &str = "(.*?)";\n', src, re.S))
    return {k: v for k, v in found.items() if k in LEMMAS}


# ------------------------------------------------------------------- self-test
#
# The generator's own correctness argument, and it is not an assertion about the
# code: with the PRE-strengthening deref parameters — five steps, and the stored
# field word returned unchanged — it reproduces, byte for byte, the three terms
# that were hand-written and kernel-checked at `fc350b9c4` (2026-08-26).
# Those digests are of terms a kernel accepted. If a refactor here changes the
# emitted shape, this fails before any spec build does.

LEGACY_DIGESTS = {
    "SRC_IR_LZB_DEREF_ACTIVATION": "b054b998ea04aa4874b94f15266a0837409bfc9224ca1c9755ba0d6cdc1db068",
    "SRC_IR_LZB_MAX_TRUE_SEG": "bcf8c09f31b91dd172c8b2feffe281d0de7ec6d38bfe1bdc5c2875717cb87284",
    "SRC_IR_LZB_MAX_FALSE_SEG": "c83179373ede6ce0a5164c56888b178f7f1721e32d32ba290fea471000f9e182",
    "SRC_IR_LZB_IMAX_SEG": "548cbb39103ebed18d403ec85379011aeb8889246dc16a30c62afea1e8073110",
}


def self_test() -> int:
    import hashlib

    global DEREF_STEPS, deref_result, child_of
    keep = (DEREF_STEPS, deref_result, child_of)
    DEREF_STEPS = "ir_d5"
    deref_result = lambda b: f"(IRScalar.ptr_ {b})"  # noqa: E731
    child_of = lambda b: b  # noqa: E731
    try:
        bad = 0
        for name, fn in LEMMAS.items():
            got = hashlib.sha256(fn().encode()).hexdigest()
            want = LEGACY_DIGESTS[name]
            if got == want:
                print(f"ok {name}: legacy shape reproduced ({want[:12]}…)")
            else:
                print(f"FAIL {name}: legacy shape is {got[:12]}…, pinned {want[:12]}…")
                bad += 1
        printer = XP.self_test()
        for line in printer:
            print(f"FAIL {line}")
        if bad or printer:
            print(
                "gen_lzb_activation: the emitter no longer reproduces the "
                "kernel-checked 2026-08-26 terms, or its printer fails its arms",
                file=sys.stderr,
            )
            return 1
        print(f"gen_lzb_activation self-test: {len(LEMMAS)}/{len(LEMMAS)} legacy terms reproduced")
        return 0
    finally:
        DEREF_STEPS, deref_result, child_of = keep


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=(__doc__ or "EvalIR term generator").splitlines()[0])
    ap.add_argument("--check", action="store_true", help="byte-compare with the committed consts")
    ap.add_argument("--print", dest="show", help="print one lemma by const name")
    ap.add_argument("--emit", action="store_true", help="rewrite the consts in place")
    ap.add_argument("--self-test", action="store_true",
                    help="reproduce the pre-strengthening terms the kernel accepted")
    ap.add_argument("--pinned-inputs", action="store_true", help="list exact source/control inputs")
    args = ap.parse_args(argv)
    actions = [args.check, args.show is not None, args.emit, args.self_test, args.pinned_inputs]
    if sum(actions) > 1:
        ap.error("primary actions cannot be combined")
    if args.pinned_inputs:
        print("\n".join(HELPER_INPUTS))
        return 0
    if args.show == "":
        ap.error("--print requires a nonempty const name")

    if args.self_test:
        code = self_test()
        if code == 0:
            _helper_source_controls()
        return code

    minted = spelled()

    if args.show:
        print(minted[args.show])
        return 0

    if args.emit:
        src = ACTIVATION_RS.read_text()
        for name, body in minted.items():
            pat = re.compile(r'(const ' + name + r': &str = ")(.*?)(";\n)', re.S)
            if not pat.search(src):
                print(f"gen_lzb_activation: {name} not found in {ACTIVATION_RS}", file=sys.stderr)
                return 1
            src = pat.sub(lambda m: m.group(1) + body + m.group(3), src, count=1)
        ACTIVATION_RS.write_text(src)
        print(f"gen_lzb_activation: emitted {len(minted)} lemma(s) into {ACTIVATION_RS.name}")
        return 0

    have = committed()
    bad = 0
    for name, body in minted.items():
        if name not in have:
            print(f"MISSING {name}")
            bad += 1
        elif have[name] != body:
            print(f"DIFFERS {name}: committed {len(have[name])} chars, minted {len(body)} chars")
            for i, (x, y) in enumerate(zip(have[name], body)):
                if x != y:
                    print(f"  first difference at {i}:")
                    print(f"    committed: ...{have[name][max(0,i-90):i+90]}...")
                    print(f"    minted:    ...{body[max(0,i-90):i+90]}...")
                    break
            bad += 1
        else:
            print(f"ok {name} ({len(body)} chars)")
    if bad:
        print(f"gen_lzb_activation: {bad} lemma(s) differ", file=sys.stderr)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
