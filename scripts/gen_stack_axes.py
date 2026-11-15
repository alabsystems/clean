#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Mint `eval_ir_stack_axes_minted.rs` -- the two axes E1's split left open (decision
memo §6 Phase E / §11 item 8; statements settled in `designs/2026-09-25-e1-axes.md`).

E1 (`eval_ir_stack_split.rs`) left two items open, both named in its design note:

  1. DESTS PRESERVATION OVER AN ABSTRACT BODY. `ir_stk_activation_dests` takes the
     standalone run in a shape that already CARRIES the entry frame's dests to the
     returning frame (`forall d`, the same `d` at both ends), so it holds only for
     bodies whose run is computed at an abstract `d`. What is needed is the general
     fact: the machine never reads the BOTTOM frame's dests (the only reader, a
     `ret`, reads it only to write into a caller -- and the bottom frame has none),
     so a run COMMUTES with rewriting that field. Stated here as parametricity:

         ir_step m (ir_mach_set_bot s d) = ir_config_set_bot (ir_step m s) d

     for EVERY module and EVERY machine -- no premise at all. This file mints the
     per-arm family that proves it at a single frame (the `ir_bdst` family: the
     frame whose dests change is the frame that EXECUTES), and the one term that
     proves it when the executing frame is NOT the bottom one (`ir_bdst_step_cons`,
     which REUSES E1's node-keyed arms `ir_stkn_arm_*` at an empty tail: a head over
     any tail is the one-frame machine stacked over it). The multi-step theorem and
     the general `ir_stk_activation_dests_gen` are hand-authored above it
     (`eval_ir_stack_axes.rs`).

  2. THE MODULE AXIS FOR F. `ir_mext_step` transports a step to an extension module
     only while the step stays RUNNING, so a callee that HALTS (E1's F case) could not
     cross modules. The running premise is consumed in exactly the four module-lookup
     misses -- the function fetch, a jump's function, a call's callee, a global --
     and each of those halts with one of exactly TWO outcomes: `stuck no_func` and
     `type_error no_global`. So the premise is replaced by `ir_mext_ok`: the step is
     running, or halted with any outcome but those two. The outcome-keyed twin
     `ir_mexto_*` is the running-keyed `ir_mext_*` family with that ONE predicate
     substituted; the proof terms are otherwise character-identical, which is the
     machine-checked form of the claim that the old premise was only ever used at a
     lookup miss. `--self-test` holds the twin to that: undoing the substitution must
     give back gen_stack_lemmas.py's term, byte for byte.

EVERY TABLE IS READ FROM SOURCE: this script imports gen_stack_lemmas.py (the IRInst /
IRScalar / IRTy / IRFault constructor tables, the machine helpers' signatures and
bodies, the recursor emitters) rather than copying it, so a new IRInst constructor
re-mints both families here exactly as it re-mints E1's.

WHAT --check SAYS. That the committed Rust file is byte-for-byte what --emit produces.
NOT that the terms are true -- the kernel says that, per declaration, in the EvalIr
bundle build.

USAGE
    python3 scripts/gen_stack_axes.py --emit
    python3 scripts/gen_stack_axes.py --check
    python3 scripts/gen_stack_axes.py --self-test
    python3 scripts/gen_stack_axes.py --print ir_bdst_step1
    python3 scripts/gen_stack_axes.py --list
    python3 scripts/gen_stack_axes.py --scratch [--only REGEX]   # data/spec_scratch_evalir.json
    python3 scripts/gen_stack_axes.py --digests | --pin
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
CORE = REPO / "crates/clean-verify/src/spec/core_spec"
MINTED_RS = CORE / "eval_ir_stack_axes_minted.rs"
SCRATCH = REPO / "data/spec_scratch_evalir.json"

_spec = importlib.util.spec_from_file_location("gen_stack_lemmas", REPO / "scripts/gen_stack_lemmas.py")
G = importlib.util.module_from_spec(_spec)
assert _spec.loader is not None
_spec.loader.exec_module(G)

D = "DerivedProved, zero axiom_deps."
VS = "(IRList IRScalar)"
NILF = "(IRList.nil IRFrame)"

# ==========================================================================
# AXIS 1 -- bottom-frame dests (the ir_bdst family)
# ==========================================================================
#
# The single-frame block: the executing frame IS the bottom frame, spelled as a
# constructor so every frame writer reduces on it. H0 carries the OLD dests `bds`,
# H1 the NEW dests `bdn`; everything else is shared, so every read (locals, func,
# block, pc) is the same term on both sides after one iota.

HB = ("(bfi : Nat) (bbl : Nat) (bpc : Nat) (bloc : IRList IRBinding) (bds : IRList Nat) "
      "(bdn : IRList Nat) (mem : IRList IRMemSlot) (na : Nat)")
HARGS = "bfi bbl bpc bloc bds bdn mem na"
HNAMES = {"bfi", "bbl", "bpc", "bloc", "bds", "bdn", "mem", "na"}


def fr(x: str) -> str:
    return f"(IRFrame.mk bfi bbl bpc bloc {x})"


F0, F1 = fr("bds"), fr("bdn")
H0 = f"(IRMachine.mk (IRList.cons IRFrame {F0} {NILF}) mem na)"
H1 = f"(IRMachine.mk (IRList.cons IRFrame {F1} {NILF}) mem na)"


def hgoal(tpl: str) -> str:
    """`Eq IRConfig (H H1 ..) (ir_config_set_bot (H H0 ..) bdn)` for a template over {S}."""
    return f"Eq IRConfig {G.at(tpl, H1)} (ir_config_set_bot {G.at(tpl, H0)} bdn)"


def one(frame: str) -> str:
    return G.cons(frame, NILF)


def sig_h(helper: str) -> tuple[str, list[str], str]:
    """(binders, args, template) of `<helper>_bdst`: the helper's own binders with
    `(s : IRMachine)` expanded to the single-frame block."""
    d = G.machine(helper)
    binders, args = [], []
    for n, ty in d.binders:
        if n == "s":
            assert ty == "IRMachine", (helper, n, ty)
            binders.append(HB)
            args.append("{S}")
        else:
            nn = G.rn(n)
            assert nn not in HNAMES, (helper, nn)
            binders.append(f"({nn} : {ty})")
            args.append(nn)
    assert "{S}" in args, helper
    return " ".join(binders), args, f"({helper} {' '.join(args)})"


def hify(rhs: str) -> tuple[str, list[str]]:
    """Rewrite a machine-helper application over `s` into the application of its
    `_bdst` lemma: head reads become reads of the OLD frame (the same term on both
    sides after iota), `(ir_resolve s x)` is reported for the caller to transport."""
    r = re.sub(r"\(ir_getd s (\w+)\)", lambda m: f"(ir_frame_get {F0} {m.group(1)})", rhs)
    r = r.replace("(ir_mach_mem s)", "mem").replace("(ir_load_eval s ", "(ir_load_at mem ")
    resolves = re.findall(r"\(ir_resolve s (\w+)\)", r)
    r = re.sub(r"\(ir_resolve s (\w+)\)", lambda m: f"(ir_resolve {H0} {m.group(1)})", r)
    head, *args = G.top_tokens(r)
    assert head.startswith("ir_") and "s" in args, rhs
    out = f"{head}_bdst {' '.join(HARGS if a == 's' else a for a in args)}"
    assert not re.search(r"\bs\b", out), out
    return out, resolves


def resolve_subst_h(x: str, motive_body, inner: str) -> str:
    r0, r1 = f"(ir_resolve {H0} {x})", f"(ir_resolve {H1} {x})"
    return (f"Eq.subst {VS} (fun (vs : IRList IRScalar) => {motive_body('vs')}) {r0} {r1} "
            f"(Eq.symm {VS} {r1} {r0} (ir_resolve_bdst {HARGS} {x})) ({inner})")


# ---- definitions and their pins ------------------------------------------

DEFS_BDST = [
    ("SRC_FRAME_SET_DESTS", "ir_frame_set_dests",
     "def ir_frame_set_dests (f : IRFrame) (d : IRList Nat) : IRFrame := IRFrame.mk (ir_frame_func f) (ir_frame_block f) (ir_frame_pc f) (ir_frame_locals f) d",
     "ir_frame_set_dests: the frame with its dests field replaced. Built from the four PROJECTIONS rather than by IRFrame.rec, so every other field of the result reduces to the same field of `f` by one iota even at an ABSTRACT frame -- which is what lets the fetch, the operand reads and the locals of a rewritten frame be the same terms as the original's. " + D),
    ("SRC_FRAMES_SET_BOT", "ir_frames_set_bot",
     "def ir_frames_set_bot (fs : IRList IRFrame) (d : IRList Nat) : IRList IRFrame := IRList.rec IRFrame (fun (_ : IRList IRFrame) => IRList IRFrame) (IRList.nil IRFrame) (fun (x : IRFrame) (t : IRList IRFrame) (ih : IRList IRFrame) => IRList.rec IRFrame (fun (_ : IRList IRFrame) => IRList IRFrame) (IRList.cons IRFrame (ir_frame_set_dests x d) (IRList.nil IRFrame)) (fun (_ : IRFrame) (_ : IRList IRFrame) (_ : IRList IRFrame) => IRList.cons IRFrame x ih) t) fs",
     "ir_frames_set_bot: *** THE TRANSFORMATION THE AXIS IS ABOUT. *** Rewrite the dests of the LAST frame of a frame list -- the bottom frame, the one a single-frame run was entered at -- and leave every other frame, and the list's length, alone. The empty list is left empty. IRList.rec with an inner case on the tail: a frame whose tail is empty IS the bottom one. " + D),
    ("SRC_MACH_SET_BOT", "ir_mach_set_bot",
     "def ir_mach_set_bot (s : IRMachine) (d : IRList Nat) : IRMachine := IRMachine.rec (fun (_ : IRMachine) => IRMachine) (fun (fs : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) => IRMachine.mk (ir_frames_set_bot fs d) mem na) s",
     "ir_mach_set_bot: ir_frames_set_bot on a machine's frame list; heap and counter unchanged. " + D),
    ("SRC_CONFIG_SET_BOT", "ir_config_set_bot",
     "def ir_config_set_bot (c : IRConfig) (d : IRList Nat) : IRConfig := IRConfig.rec (fun (_ : IRConfig) => IRConfig) (fun (s : IRMachine) => IRConfig.running (ir_mach_set_bot s d)) (fun (o : IROutcome) => IRConfig.halted o) c",
     "ir_config_set_bot: the same on a configuration; the IDENTITY on a halted one -- an outcome carries no frame, so a run that halts has nothing left to rewrite. " + D),
]

PINS_BDST = [
    ("SRC_FRAMES_SET_BOT_NIL", "ir_frames_set_bot_nil", "(d : IRList Nat)",
     "(IRList IRFrame)", "(ir_frames_set_bot (IRList.nil IRFrame) d)", "(IRList.nil IRFrame)",
     "the empty list is left empty"),
    ("SRC_FRAMES_SET_BOT_ONE", "ir_frames_set_bot_one", "(x : IRFrame) (d : IRList Nat)",
     "(IRList IRFrame)", "(ir_frames_set_bot (IRList.cons IRFrame x (IRList.nil IRFrame)) d)",
     "(IRList.cons IRFrame (ir_frame_set_dests x d) (IRList.nil IRFrame))",
     "a single frame IS the bottom frame and is rewritten"),
    ("SRC_FRAMES_SET_BOT_TWO", "ir_frames_set_bot_two",
     "(x : IRFrame) (y : IRFrame) (t : IRList IRFrame) (d : IRList Nat)", "(IRList IRFrame)",
     "(ir_frames_set_bot (IRList.cons IRFrame x (IRList.cons IRFrame y t)) d)",
     "(IRList.cons IRFrame x (ir_frames_set_bot (IRList.cons IRFrame y t) d))",
     "a frame with a caller beneath it is NOT the bottom frame and is kept verbatim"),
    ("SRC_FRAME_SET_DESTS_MK", "ir_frame_set_dests_mk",
     "(fi : Nat) (bl : Nat) (pc : Nat) (loc : IRList IRBinding) (ds : IRList Nat) (d : IRList Nat)", "IRFrame",
     "(ir_frame_set_dests (IRFrame.mk fi bl pc loc ds) d)", "(IRFrame.mk fi bl pc loc d)",
     "at a constructor, exactly the dests field changes"),
    ("SRC_FRAME_DESTS_SET_DESTS", "ir_frame_dests_set_dests", "(f : IRFrame) (d : IRList Nat)",
     "(IRList Nat)", "(ir_frame_dests (ir_frame_set_dests f d))", "d",
     "the rewritten frame's dests are the new ones, at an ABSTRACT frame"),
    ("SRC_FRAME_FUNC_SET_DESTS", "ir_frame_func_set_dests", "(f : IRFrame) (d : IRList Nat)",
     "Nat", "(ir_frame_func (ir_frame_set_dests f d))", "(ir_frame_func f)",
     "and its function id is the original's, at an ABSTRACT frame -- so a fetch keyed on it is the original fetch"),
    ("SRC_CONFIG_SET_BOT_HALTED", "ir_config_set_bot_halted", "(o : IROutcome) (d : IRList Nat)",
     "IRConfig", "(ir_config_set_bot (IRConfig.halted o) d)", "(IRConfig.halted o)",
     "a halted configuration is left alone"),
]


def pin_term(name: str, binders: str, ty: str, lhs: str, rhs: str) -> str:
    return G.defn(name, binders, f"Eq {ty} {lhs} {rhs}", G.refl(ty, rhs))


# ---- C. head-only read ---------------------------------------------------


def c_resolve() -> str:
    mot = lambda v: f"Eq {VS} (ir_resolve {H1} {v}) (ir_resolve {H0} {v})"
    body = (f"IRList.rec Nat (fun (ids0 : IRList Nat) => {mot('ids0')}) "
            f"({G.refl(VS, '(IRList.nil IRScalar)')}) "
            f"(fun (i : Nat) (ids2 : IRList Nat) (ih : {mot('ids2')}) => "
            f"ir_eq_cong {VS} {VS} (fun (vs : IRList IRScalar) => IRList.cons IRScalar (ir_frame_get {F0} i) vs) "
            f"(ir_resolve {H1} ids2) (ir_resolve {H0} ids2) ih) ids")
    return G.defn("ir_resolve_bdst", f"{HB} (ids : IRList Nat)", mot("ids"), body)


# ---- D. writers ----------------------------------------------------------


def _refl_writer(helper: str, normal_form: str) -> str:
    binders, _, tpl = sig_h(helper)
    return G.defn(f"{helper}_bdst", binders, hgoal(tpl), G.refl("IRConfig", normal_form))


def d_bind() -> str:
    return _refl_writer("ir_bind", G.running(one(f"(ir_frame_bind {F1} rs v)")))


def d_bind_result() -> str:
    binders, _, _ = sig_h("ir_bind_result")
    mot = lambda r: hgoal(f"(ir_bind_result {{S}} rs {r})")
    body = (f"IRStepResult.rec (fun (r0 : IRStepResult) => {mot('r0')}) "
            f"(fun (v : IRScalar) => ir_bind_bdst {HARGS} rs v) "
            f"(fun (o : IROutcome) => {G.refl('IRConfig', G.halted('o'))}) r")
    return G.defn("ir_bind_result_bdst", binders, mot("r"), body)


def d_bind2() -> str:
    return _refl_writer("ir_bind2", G.running(one(f"(ir_frame_bind2 {F1} rs v u)")))


def d_advance() -> str:
    return _refl_writer("ir_advance", G.running(one(f"(ir_frame_advance {F1})")))


def d_advance_set_mem() -> str:
    tpl = "(ir_advance (ir_set_mem {S} m2))"
    return G.defn("ir_advance_set_mem_bdst", f"{HB} (m2 : IRList IRMemSlot)", hgoal(tpl),
                  G.refl("IRConfig", G.running(one(f"(ir_frame_advance {F1})"), mem="m2")))


def d_alloca_k() -> str:
    return _refl_writer("ir_alloca_k", G.running(one(f"(ir_frame_bind {F1} rs (IRScalar.ptr_ na))"),
                                                 mem="(ir_alloc_cells na k mem)", na="(Nat.add na k)"))


def d_goto() -> str:
    return _refl_writer("ir_goto", G.running(one(
        f"(ir_frame_goto {F1} tgt (ir_bind_params ps vs (ir_frame_locals {F1})))")))


def d_push() -> str:
    callee = ("(IRFrame.mk (ir_func_id g) (ir_func_entry g) Nat.zero "
              "(ir_bind_params (ir_func_params g) vs (IRList.nil IRBinding)) rs)")
    return _refl_writer("ir_push", G.running(G.cons(callee, one(f"(ir_frame_advance {F1})"))))


def d_ret_vals() -> str:
    # The bottom ret: ir_ret_to at an EMPTY caller list halts with the values and
    # never looks at the dests -- the one read of the field, discarded.
    return _refl_writer("ir_ret_vals", G.halted("(IROutcome.ret vs)"))


# ---- E. branching helpers ------------------------------------------------


def _scalar_default(fault: str):
    return lambda fs, ihs: G.refl("IRConfig", G.tyerr(fault))


def e_store_live() -> str:
    binders, _, _ = sig_h("ir_store_live")
    mot = lambda b: hgoal(f"(ir_store_live {{S}} a v {b})")
    body = G.bool_rec("b0", mot, G.refl("IRConfig", G.ub("bad_addr")),
                      f"ir_advance_set_mem_bdst {HARGS} (ir_mem_update mem a v)", "live")
    return G.defn("ir_store_live_bdst", binders, mot("live"), body)


def e_store_checked() -> str:
    binders, _, _ = sig_h("ir_store_checked")
    mot = lambda o: hgoal(f"(ir_store_checked {{S}} a v {o})")
    body = G.opt_rec("IRMemSlot", "o0", mot, G.refl("IRConfig", G.ub("bad_addr")), ("c", "IRMemSlot"),
                     f"ir_store_live_bdst {HARGS} a v (ir_slot_live c)", "o")
    return G.defn("ir_store_checked_bdst", binders, mot("o"), body)


def e_store_exec() -> str:
    binders, _, _ = sig_h("ir_store_exec")
    mot = lambda p: hgoal(f"(ir_store_exec {{S}} {p} v)")
    through = lambda fs, ihs: f"ir_store_checked_bdst {HARGS} {fs[0]} v (ir_mem_lookup mem {fs[0]})"
    arms = {"ptr_": through, "fat_": through,
            "nullptr_": lambda fs, ihs: G.refl("IRConfig", G.ub("null_deref"))}
    body = G.fam_rec("IRScalar", "p0", mot, arms, _scalar_default("not_ptr"), "p", G.SCALAR_NAMES, "p")
    return G.defn("ir_store_exec_bdst", binders, mot("p"), body)


def e_jump_block() -> str:
    binders, _, _ = sig_h("ir_jump_block")
    mot = lambda ob: hgoal(f"(ir_jump_block {{S}} tgt vs {ob})")
    body = G.opt_rec("IRBlock", "o0", mot, G.refl("IRConfig", G.stuck("no_block")), ("b", "IRBlock"),
                     f"ir_goto_bdst {HARGS} tgt (ir_block_params b) vs", "ob")
    return G.defn("ir_jump_block_bdst", binders, mot("ob"), body)


def e_jump_func() -> str:
    binders, _, _ = sig_h("ir_jump_func")
    mot = lambda of: hgoal(f"(ir_jump_func {{S}} tgt vs {of})")
    body = G.opt_rec("IRFunc", "o0", mot, G.refl("IRConfig", G.stuck("no_func")), ("g", "IRFunc"),
                     f"ir_jump_block_bdst {HARGS} tgt vs (ir_block_find (ir_func_blocks g) tgt)", "of")
    return G.defn("ir_jump_func_bdst", binders, mot("of"), body)


def e_jump() -> str:
    binders, _, tpl = sig_h("ir_jump")
    cur = f"(ir_cur_func m {H0})"
    mot = lambda vs: f"Eq IRConfig (ir_jump_func {H1} tgt {vs} {cur}) (ir_config_set_bot {G.at(tpl, H0)} bdn)"
    body = resolve_subst_h("args", mot, f"ir_jump_func_bdst {HARGS} tgt (ir_resolve {H0} args) {cur}")
    return G.defn("ir_jump_bdst", binders, hgoal(tpl), body)


def e_condbr_b() -> str:
    binders, _, _ = sig_h("ir_condbr_b")
    mot = lambda b: hgoal(f"(ir_condbr_b m {{S}} tt targs et eargs {b})")
    body = G.bool_rec("b0", mot, f"ir_jump_bdst m {HARGS} et eargs", f"ir_jump_bdst m {HARGS} tt targs", "b")
    return G.defn("ir_condbr_b_bdst", binders, mot("b"), body)


def e_condbr_exec() -> str:
    binders, _, _ = sig_h("ir_condbr_exec")
    mot = lambda c: hgoal(f"(ir_condbr_exec m {{S}} {c} tt targs et eargs)")
    arms = {"bool_": lambda fs, ihs: f"ir_condbr_b_bdst m {HARGS} tt targs et eargs {fs[0]}"}
    body = G.fam_rec("IRScalar", "c0", mot, arms, _scalar_default("not_bool"), "c", G.SCALAR_NAMES, "c")
    return G.defn("ir_condbr_exec_bdst", binders, mot("c"), body)


def e_switch_n() -> str:
    binders, _, tpl = sig_h("ir_switch_n")
    mot = lambda o: (f"Eq IRConfig {G.switch_n_body('m', H1, o)} "
                     f"(ir_config_set_bot {G.switch_n_body('m', H0, o)} bdn)")
    body = G.neutral_opt_rec("IRSwitchCase", "o0", mot, f"ir_jump_bdst m {HARGS} dflt dargs",
                             ("c", "IRSwitchCase"),
                             f"ir_jump_bdst m {HARGS} (ir_case_target c) (ir_case_args c)",
                             "(ir_case_find cases n)", hgoal(tpl))
    return G.defn("ir_switch_n_bdst", binders, hgoal(tpl), body)


def e_switch_exec() -> str:
    binders, _, _ = sig_h("ir_switch_exec")
    mot = lambda v: hgoal(f"(ir_switch_exec m {{S}} {v} dflt dargs cases)")
    arms = {"int_": lambda fs, ihs: f"ir_switch_n_bdst m {HARGS} dflt dargs cases {fs[0]}"}
    body = G.fam_rec("IRScalar", "v0", mot, arms, _scalar_default("not_int"), "v", G.SCALAR_NAMES, "v")
    return G.defn("ir_switch_exec_bdst", binders, mot("v"), body)


def e_call_exec() -> str:
    binders, _, tpl = sig_h("ir_call_exec")
    mot = lambda o: (f"Eq IRConfig {G.call_exec_body(H1, o)} "
                     f"(ir_config_set_bot {G.call_exec_body(H0, o)} bdn)")
    some_mot = lambda vs: (f"Eq IRConfig (ir_push {H1} rs g {vs}) "
                           f"(ir_config_set_bot (ir_push {H0} rs g (ir_resolve {H0} args)) bdn)")
    some_case = resolve_subst_h("args", some_mot, f"ir_push_bdst {HARGS} rs g (ir_resolve {H0} args)")
    body = G.neutral_opt_rec("IRFunc", "o0", mot, G.refl("IRConfig", G.stuck("no_func")), ("g", "IRFunc"),
                             some_case, "(ir_func_find (ir_mod_funcs m) fid)", hgoal(tpl))
    return G.defn("ir_call_exec_bdst", binders, hgoal(tpl), body)


def e_callind_exec() -> str:
    binders, _, _ = sig_h("ir_callind_exec")
    mot = lambda cv: hgoal(f"(ir_callind_exec m {{S}} rs {cv} args)")
    arms = {"fnptr_": lambda fs, ihs: f"ir_call_exec_bdst m {HARGS} rs {fs[0]} args",
            "nullptr_": lambda fs, ihs: G.refl("IRConfig", G.ub("null_deref"))}
    body = G.fam_rec("IRScalar", "cv0", mot, arms, _scalar_default("not_fnptr"), "cv", G.SCALAR_NAMES, "cv")
    return G.defn("ir_callind_exec_bdst", binders, mot("cv"), body)


def e_assert_b() -> str:
    binders, _, _ = sig_h("ir_assert_b")
    mot = lambda b: hgoal(f"(ir_assert_b {{S}} {b})")
    body = G.bool_rec("b0", mot, G.refl("IRConfig", G.ub("assert_failed")), f"ir_advance_bdst {HARGS}", "b")
    return G.defn("ir_assert_b_bdst", binders, mot("b"), body)


def e_assert_exec() -> str:
    binders, _, _ = sig_h("ir_assert_exec")
    mot = lambda c: hgoal(f"(ir_assert_exec {{S}} {c})")
    arms = {"bool_": lambda fs, ihs: f"ir_assert_b_bdst {HARGS} {fs[0]}"}
    body = G.fam_rec("IRScalar", "c0", mot, arms, _scalar_default("not_bool"), "c", G.SCALAR_NAMES, "c")
    return G.defn("ir_assert_exec_bdst", binders, mot("c"), body)


def e_alloca_exec() -> str:
    binders, _, _ = sig_h("ir_alloca_exec")
    mot = lambda c: hgoal(f"(ir_alloca_exec {{S}} rs {c})")
    inner_mot = lambda o: (f"Eq IRConfig {G.alloca_exec_body(H1, o)} "
                           f"(ir_config_set_bot {G.alloca_exec_body(H0, o)} bdn)")
    inner = G.neutral_opt_rec("Nat", "o1", inner_mot, G.refl("IRConfig", G.tyerr("not_int")), ("k", "Nat"),
                              f"ir_alloca_k_bdst {HARGS} rs k", f"(ir_as_int (ir_frame_get {F0} i))",
                              mot("(IROption.some Nat i)"))
    body = G.opt_rec("Nat", "c0", mot, f"ir_alloca_k_bdst {HARGS} rs (Nat.succ Nat.zero)", ("i", "Nat"),
                     inner, "c")
    return G.defn("ir_alloca_exec_bdst", binders, mot("c"), body)


def e_overflow_ints() -> str:
    binders, _, tpl = sig_h("ir_overflow_ints")
    proof, resolves = hify(G.machine("ir_overflow_ints").body)
    assert not resolves and proof.startswith("ir_bind2_bdst ")
    return G.defn("ir_overflow_ints_bdst", binders, hgoal(tpl), proof)


def e_overflow_vals() -> str:
    binders, _, _ = sig_h("ir_overflow_vals")
    mot_a = lambda a: hgoal(f"(ir_overflow_vals {{S}} rs op sgn w {a} b)")
    dflt = _scalar_default("not_int")

    def int_arm(fs, ihs):
        x = fs[0]
        mot_b = lambda b: hgoal(f"(ir_overflow_vals {{S}} rs op sgn w (IRScalar.int_ {x}) {b})")
        arms_b = {"int_": lambda fs2, ihs2: f"ir_overflow_ints_bdst {HARGS} rs op sgn w {x} {fs2[0]}"}
        return G.fam_rec("IRScalar", "b0", mot_b, arms_b, dflt, "b", G.SCALAR_NAMES, "b")

    body = G.fam_rec("IRScalar", "a0", mot_a, {"int_": int_arm}, dflt, "a", G.SCALAR_NAMES, "a")
    return G.defn("ir_overflow_vals_bdst", binders, mot_a("a"), body)


def e_overflow_exec() -> str:
    binders, _, _ = sig_h("ir_overflow_exec")
    mot = lambda ty: hgoal(f"(ir_overflow_exec {{S}} rs op {ty} a b)")
    arms = {"int_": lambda fs, ihs: f"ir_overflow_vals_bdst {HARGS} rs op Bool.true {fs[0]} a b",
            "uint_": lambda fs, ihs: f"ir_overflow_vals_bdst {HARGS} rs op Bool.false {fs[0]} a b"}
    body = G.fam_rec("IRTy", "ty0", mot, arms, lambda fs, ihs: G.refl("IRConfig", G.tyerr("not_int")), "ty",
                     G.TY_NAMES, "ty")
    return G.defn("ir_overflow_exec_bdst", binders, mot("ty"), body)


# ---- F. per-constructor arms (NO premise: the axis needs none) -----------


def arm_proof_h(ctor: str, names: list[str], rhs: str, tpl: str) -> str:
    if rhs.startswith("IRConfig.halted "):
        return G.refl("IRConfig", f"({rhs})")
    if G.is_ret_rhs(rhs):
        (ids,) = rhs.split()[2:]
        mot = lambda vs: f"Eq IRConfig (ir_ret_vals {H1} {vs}) (ir_config_set_bot {G.at(tpl, H0)} bdn)"
        return resolve_subst_h(ids, mot, f"ir_ret_vals_bdst {HARGS} (ir_resolve {H0} {ids})")
    term, resolves = hify(rhs)
    if not resolves:
        return term
    (x,) = resolves
    assert term.startswith(f"ir_bind_result_bdst {HARGS} rs "), (ctor, term)
    evaluator = term[len(f"ir_bind_result_bdst {HARGS} rs "):]
    mot = lambda vs: (f"Eq IRConfig (ir_bind_result {H1} rs {evaluator.replace(f'(ir_resolve {H0} {x})', vs)}) "
                      f"(ir_config_set_bot {G.at(tpl, H0)} bdn)")
    return resolve_subst_h(x, mot, term)


def arm_lemma_h(ctor: str, names: list[str], types: list[str], rhs: str) -> str:
    tpl = f"(ir_exec m {G.inst_app(ctor, names)} rs {{S}})"
    fields = " ".join(f"({n} : {ty})" for n, ty in zip(names, types))
    assert not (set(names) & HNAMES), (ctor, names)
    binders = f"(m : IRModule) {HB} (rs : IRList Nat){' ' + fields if fields else ''}"
    return G.defn(f"ir_bdst_arm_{ctor}", binders, hgoal(tpl), arm_proof_h(ctor, names, rhs, tpl))


# ---- G1. the single-frame step -------------------------------------------


def g_step1() -> str:
    step_f = lambda S, o: f"(ir_step_f m {S} bbl bpc {o})"
    step_b = lambda S, o: f"(ir_step_b m {S} bpc {o})"
    step_n = lambda S, o: f"(ir_step_n m {S} {o})"
    exec_node = lambda S, n0: f"(ir_exec_node m {n0} {S})"
    exec_i = lambda S, i0: f"(ir_exec m {i0} rs {S})"
    layer = lambda step: (lambda o: f"Eq IRConfig {step(H1, o)} (ir_config_set_bot {step(H0, o)} bdn)")
    mot_f, mot_b, mot_n, mot_nd, mot_i = (layer(step_f), layer(step_b), layer(step_n),
                                          layer(exec_node), layer(exec_i))
    inst_minors = []
    for ctor, names, types, _ in G.ARMS:
        call = f"ir_bdst_arm_{ctor} m {HARGS} rs {' '.join(names)}".rstrip()
        if names:
            fields = " ".join(f"({n} : {ty})" for n, ty in zip(names, types))
            inst_minors.append(f"(fun {fields} => {call})")
        else:
            inst_minors.append(f"({call})")
    inst_rec = f"IRInst.rec (fun (i0 : IRInst) => {mot_i('i0')}) {' '.join(inst_minors)} i"
    node_rec = f"IRNode.rec (fun (n0 : IRNode) => {mot_nd('n0')}) (fun (i : IRInst) (rs : IRList Nat) => {inst_rec}) nd"
    n_scrut = "(ir_nodes_get (ir_block_nodes bk) bpc)"
    n_rec = G.neutral_opt_rec("IRNode", "on", mot_n, G.refl("IRConfig", G.stuck("fetch_past_end")),
                              ("nd", "IRNode"), node_rec, n_scrut, mot_n(n_scrut))
    b_scrut = "(ir_block_find (ir_func_blocks fn) bbl)"
    b_rec = G.neutral_opt_rec("IRBlock", "ob", mot_b, G.refl("IRConfig", G.stuck("no_block")),
                              ("bk", "IRBlock"), n_rec, b_scrut, mot_b(b_scrut))
    f_scrut = "(ir_func_find (ir_mod_funcs m) bfi)"
    f_rec = G.neutral_opt_rec("IRFunc", "o", mot_f, G.refl("IRConfig", G.stuck("no_func")),
                              ("fn", "IRFunc"), b_rec, f_scrut, mot_f(f_scrut))
    return G.defn("ir_bdst_step1", f"(m : IRModule) {HB}",
                  f"Eq IRConfig (ir_step m {H1}) (ir_config_set_bot (ir_step m {H0}) bdn)", f_rec)


# ---- the non-bottom head: stacking, reused -------------------------------
#
# A head `fh` over a nonempty tail `gb :: tb` is the ONE-frame machine [fh] stacked
# over that tail. E1's node-keyed arms state exactly that for every non-ret arm (at
# t = nil the stacked machine IS `fh :: rest`), so the non-ret minors are two
# applications of ir_stkn_arm_<ctor> -- at the rewritten tail and at the original --
# joined by ir_bdst_of_stk; the ret minor is ir_bdst_ret_cons. The tail vocabulary
# (fh gb tb dn) avoids every IRInst field name (ptrfromparts has a field `d`).

T0 = "(IRList.cons IRFrame gb tb)"
T1 = f"(ir_frames_set_bot {T0} dn)"
C0 = f"(IRMachine.mk (IRList.cons IRFrame fh {T0}) mem na)"
C1 = f"(IRMachine.mk (IRList.cons IRFrame fh {T1}) mem na)"
C1F = f"(IRMachine.mk (IRList.cons IRFrame fh {NILF}) mem na)"

SUPPORT = [
    ("SRC_FRAMES_APP_SET_BOT_PRE", "ir_frames_app_set_bot_pre",
     "def ir_frames_app_set_bot_pre (gb : IRFrame) (tb : IRList IRFrame) (dn : IRList Nat) (fs : IRList IRFrame) : forall (x : IRFrame), Eq (IRList IRFrame) (ir_frames_set_bot (IRList.cons IRFrame x (ir_frames_app fs (IRList.cons IRFrame gb tb))) dn) (IRList.cons IRFrame x (ir_frames_app fs (ir_frames_set_bot (IRList.cons IRFrame gb tb) dn))) := IRList.rec IRFrame (fun (fs0 : IRList IRFrame) => forall (x : IRFrame), Eq (IRList IRFrame) (ir_frames_set_bot (IRList.cons IRFrame x (ir_frames_app fs0 (IRList.cons IRFrame gb tb))) dn) (IRList.cons IRFrame x (ir_frames_app fs0 (ir_frames_set_bot (IRList.cons IRFrame gb tb) dn)))) (fun (x : IRFrame) => Eq.refl (IRList IRFrame) (IRList.cons IRFrame x (ir_frames_set_bot (IRList.cons IRFrame gb tb) dn))) (fun (y : IRFrame) (fs2 : IRList IRFrame) (ih : forall (x : IRFrame), Eq (IRList IRFrame) (ir_frames_set_bot (IRList.cons IRFrame x (ir_frames_app fs2 (IRList.cons IRFrame gb tb))) dn) (IRList.cons IRFrame x (ir_frames_app fs2 (ir_frames_set_bot (IRList.cons IRFrame gb tb) dn)))) => fun (x : IRFrame) => ir_eq_cong (IRList IRFrame) (IRList IRFrame) (fun (l : IRList IRFrame) => IRList.cons IRFrame x l) (ir_frames_set_bot (IRList.cons IRFrame y (ir_frames_app fs2 (IRList.cons IRFrame gb tb))) dn) (IRList.cons IRFrame y (ir_frames_app fs2 (ir_frames_set_bot (IRList.cons IRFrame gb tb) dn))) (ih y)) fs",
     "ir_frames_app_set_bot_pre: rewriting the bottom dests of `x :: fs ++ (gb :: tb)` rewrites them in the appended tail -- the frames stacked above a nonempty tail are never the bottom ones. IRList.rec on fs generalised over the head x, because the bottom-frame case split in ir_frames_set_bot is on the TAIL and needs the tail to be a visible cons at every stage; the cons case is ir_eq_cong of IRList.cons x over the induction hypothesis at the next head. " + D),
    ("SRC_FRAMES_APP_SET_BOT", "ir_frames_app_set_bot",
     "def ir_frames_app_set_bot (gb : IRFrame) (tb : IRList IRFrame) (dn : IRList Nat) (fs : IRList IRFrame) : Eq (IRList IRFrame) (ir_frames_app fs (ir_frames_set_bot (IRList.cons IRFrame gb tb) dn)) (ir_frames_set_bot (ir_frames_app fs (IRList.cons IRFrame gb tb)) dn) := IRList.rec IRFrame (fun (fs0 : IRList IRFrame) => Eq (IRList IRFrame) (ir_frames_app fs0 (ir_frames_set_bot (IRList.cons IRFrame gb tb) dn)) (ir_frames_set_bot (ir_frames_app fs0 (IRList.cons IRFrame gb tb)) dn)) (Eq.refl (IRList IRFrame) (ir_frames_set_bot (IRList.cons IRFrame gb tb) dn)) (fun (x : IRFrame) (fs2 : IRList IRFrame) (_ : Eq (IRList IRFrame) (ir_frames_app fs2 (ir_frames_set_bot (IRList.cons IRFrame gb tb) dn)) (ir_frames_set_bot (ir_frames_app fs2 (IRList.cons IRFrame gb tb)) dn)) => Eq.symm (IRList IRFrame) (ir_frames_set_bot (IRList.cons IRFrame x (ir_frames_app fs2 (IRList.cons IRFrame gb tb))) dn) (IRList.cons IRFrame x (ir_frames_app fs2 (ir_frames_set_bot (IRList.cons IRFrame gb tb) dn))) (ir_frames_app_set_bot_pre gb tb dn fs2 x)) fs",
     "ir_frames_app_set_bot: stacking commutes with rewriting the bottom dests of a NONEMPTY tail -- `fs ++ set_bot (gb :: tb) = set_bot (fs ++ (gb :: tb))` for every frame list fs. Case on fs: empty is Eq.refl, a cons is ir_frames_app_set_bot_pre. The tail must be nonempty: over an EMPTY tail the bottom frame would be the last of fs, which stacking does not touch. " + D),
    ("SRC_BDST_STACK_CONS", "ir_bdst_stack_cons",
     "def ir_bdst_stack_cons (c : IRConfig) (gb : IRFrame) (tb : IRList IRFrame) (dn : IRList Nat) : Eq IRConfig (ir_config_stack c (ir_frames_set_bot (IRList.cons IRFrame gb tb) dn)) (ir_config_set_bot (ir_config_stack c (IRList.cons IRFrame gb tb)) dn) := IRConfig.rec (fun (c0 : IRConfig) => Eq IRConfig (ir_config_stack c0 (ir_frames_set_bot (IRList.cons IRFrame gb tb) dn)) (ir_config_set_bot (ir_config_stack c0 (IRList.cons IRFrame gb tb)) dn)) (fun (s : IRMachine) => IRMachine.rec (fun (s0 : IRMachine) => Eq IRConfig (ir_config_stack (IRConfig.running s0) (ir_frames_set_bot (IRList.cons IRFrame gb tb) dn)) (ir_config_set_bot (ir_config_stack (IRConfig.running s0) (IRList.cons IRFrame gb tb)) dn)) (fun (fs : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) => ir_eq_cong (IRList IRFrame) IRConfig (fun (l : IRList IRFrame) => IRConfig.running (IRMachine.mk l mem na)) (ir_frames_app fs (ir_frames_set_bot (IRList.cons IRFrame gb tb) dn)) (ir_frames_set_bot (ir_frames_app fs (IRList.cons IRFrame gb tb)) dn) (ir_frames_app_set_bot gb tb dn fs)) s) (fun (o : IROutcome) => Eq.refl IRConfig (IRConfig.halted o)) c",
     "ir_bdst_stack_cons: the configuration-level form -- stacking a configuration over the REWRITTEN tail is rewriting the bottom dests of it stacked over the original tail, for every configuration (a halted one on both sides by Eq.refl). " + D),
    ("SRC_BDST_OF_STK", "ir_bdst_of_stk",
     "def ir_bdst_of_stk (x : IRConfig) (l0 : IRConfig) (l1 : IRConfig) (gb : IRFrame) (tb : IRList IRFrame) (dn : IRList Nat) (e1 : Eq IRConfig l1 (ir_config_stack x (ir_frames_set_bot (IRList.cons IRFrame gb tb) dn))) (e0 : Eq IRConfig l0 (ir_config_stack x (IRList.cons IRFrame gb tb))) : Eq IRConfig l1 (ir_config_set_bot l0 dn) := Eq.trans IRConfig l1 (ir_config_stack x (ir_frames_set_bot (IRList.cons IRFrame gb tb) dn)) (ir_config_set_bot l0 dn) e1 (Eq.trans IRConfig (ir_config_stack x (ir_frames_set_bot (IRList.cons IRFrame gb tb) dn)) (ir_config_set_bot (ir_config_stack x (IRList.cons IRFrame gb tb)) dn) (ir_config_set_bot l0 dn) (ir_bdst_stack_cons x gb tb dn) (ir_eq_cong IRConfig IRConfig (fun (c1 : IRConfig) => ir_config_set_bot c1 dn) (ir_config_stack x (IRList.cons IRFrame gb tb)) l0 (Eq.symm IRConfig l0 (ir_config_stack x (IRList.cons IRFrame gb tb)) e0)))",
     "ir_bdst_of_stk: the joint every non-ret minor of ir_bdst_step_cons goes through -- if the rewritten-tail step and the original step are the SAME one-frame step x stacked over the two tails, the first is the second with its bottom dests rewritten. Two Eq.trans and ir_bdst_stack_cons. " + D),
    ("SRC_BDST_RET_TO", "ir_bdst_ret_to",
     "def ir_bdst_ret_to (ds : IRList Nat) (dn : IRList Nat) (mem : IRList IRMemSlot) (na : Nat) (vs : IRList IRScalar) (tb : IRList IRFrame) : forall (gb : IRFrame), Eq IRConfig (ir_ret_to ds (ir_frames_set_bot (IRList.cons IRFrame gb tb) dn) mem na vs) (ir_config_set_bot (ir_ret_to ds (IRList.cons IRFrame gb tb) mem na vs) dn) := IRList.rec IRFrame (fun (t0 : IRList IRFrame) => forall (gb : IRFrame), Eq IRConfig (ir_ret_to ds (ir_frames_set_bot (IRList.cons IRFrame gb t0) dn) mem na vs) (ir_config_set_bot (ir_ret_to ds (IRList.cons IRFrame gb t0) mem na vs) dn)) (fun (gb : IRFrame) => IRFrame.rec (fun (g0 : IRFrame) => Eq IRConfig (ir_ret_to ds (ir_frames_set_bot (IRList.cons IRFrame g0 (IRList.nil IRFrame)) dn) mem na vs) (ir_config_set_bot (ir_ret_to ds (IRList.cons IRFrame g0 (IRList.nil IRFrame)) mem na vs) dn)) (fun (fi : Nat) (bl : Nat) (pc : Nat) (loc : IRList IRBinding) (e : IRList Nat) => Eq.refl IRConfig (IRConfig.running (IRMachine.mk (IRList.cons IRFrame (IRFrame.mk fi bl pc (ir_bind_params ds vs loc) dn) (IRList.nil IRFrame)) mem na))) gb) (fun (g2 : IRFrame) (t3 : IRList IRFrame) (_ : forall (gb : IRFrame), Eq IRConfig (ir_ret_to ds (ir_frames_set_bot (IRList.cons IRFrame gb t3) dn) mem na vs) (ir_config_set_bot (ir_ret_to ds (IRList.cons IRFrame gb t3) mem na vs) dn)) (gb : IRFrame) => Eq.refl IRConfig (IRConfig.running (IRMachine.mk (IRList.cons IRFrame (ir_frame_set_many gb ds vs) (ir_frames_set_bot (IRList.cons IRFrame g2 t3) dn)) mem na))) tb",
     "ir_bdst_ret_to: a return into a caller commutes with rewriting the bottom dests beneath it. IRList.rec on the caller's tail: if the caller IS the bottom frame, the return writes the values into its locals and keeps its dests, so rewriting before or after is the same frame -- IRFrame.rec on the caller, Eq.refl at the constructor (ir_frame_set_many and ir_frame_set_dests touch different fields); if the caller has a caller of its own, the bottom frame is further down and both sides re-cons it verbatim (Eq.refl). " + D),
    ("SRC_BDST_RET_CONS", "ir_bdst_ret_cons",
     f"def ir_bdst_ret_cons (fh : IRFrame) (gb : IRFrame) (tb : IRList IRFrame) (dn : IRList Nat) (mem : IRList IRMemSlot) (na : Nat) (ids : IRList Nat) : Eq IRConfig (ir_ret_to (ir_frame_dests fh) {T1} mem na (ir_resolve {C1} ids)) (ir_config_set_bot (ir_ret_to (ir_frame_dests fh) {T0} mem na (ir_resolve {C0} ids)) dn) := Eq.subst {VS} (fun (vs : IRList IRScalar) => Eq IRConfig (ir_ret_to (ir_frame_dests fh) {T1} mem na vs) (ir_config_set_bot (ir_ret_to (ir_frame_dests fh) {T0} mem na (ir_resolve {C0} ids)) dn)) (ir_resolve {C1F} ids) (ir_resolve {C1} ids) (Eq.symm {VS} (ir_resolve {C1} ids) (ir_resolve {C1F} ids) (ir_resolve_stack fh {NILF} {T1} mem na ids)) (Eq.subst {VS} (fun (vs : IRList IRScalar) => Eq IRConfig (ir_ret_to (ir_frame_dests fh) {T1} mem na (ir_resolve {C1F} ids)) (ir_config_set_bot (ir_ret_to (ir_frame_dests fh) {T0} mem na vs) dn)) (ir_resolve {C1F} ids) (ir_resolve {C0} ids) (Eq.symm {VS} (ir_resolve {C0} ids) (ir_resolve {C1F} ids) (ir_resolve_stack fh {NILF} {T0} mem na ids)) (ir_bdst_ret_to (ir_frame_dests fh) dn mem na (ir_resolve {C1F} ids) tb gb))",
     "ir_bdst_ret_cons: the ret arm of a NON-bottom head -- the return into `gb :: tb` with its bottom dests rewritten is the rewritten return. The returned values are resolved from the head frame alone, so both resolutions are transported to the one-frame machine's through ir_resolve_stack at an empty tail (one Eq.subst each), then ir_bdst_ret_to. " + D),
]


def g_step_cons() -> str:
    step_f = lambda S, o: f"(ir_step_f m {S} (ir_frame_block fh) (ir_frame_pc fh) {o})"
    step_b = lambda S, o: f"(ir_step_b m {S} (ir_frame_pc fh) {o})"
    step_n = lambda S, o: f"(ir_step_n m {S} {o})"
    exec_node = lambda S, n0: f"(ir_exec_node m {n0} {S})"
    exec_i = lambda S, i0: f"(ir_exec m {i0} rs {S})"
    layer = lambda step: (lambda o: f"Eq IRConfig {step(C1, o)} (ir_config_set_bot {step(C0, o)} dn)")
    mot_f, mot_b, mot_n, mot_nd, mot_i = (layer(step_f), layer(step_b), layer(step_n),
                                          layer(exec_node), layer(exec_i))
    inst_minors = []
    for ctor, names, types, rhs in G.ARMS:
        assert not ({"fh", "gb", "tb", "dn", "mem", "na", "m", "rs"} & set(names)), (ctor, names)
        fields = " ".join(f"({n} : {ty})" for n, ty in zip(names, types))
        inst = G.inst_app(ctor, names)
        if G.is_ret_rhs(rhs):
            (ids,) = names
            inst_minors.append(f"(fun {fields} => ir_bdst_ret_cons fh gb tb dn mem na {ids})")
            continue
        x = f"(ir_exec m {inst} rs {C1F})"
        l0, l1 = f"(ir_exec m {inst} rs {C0})", f"(ir_exec m {inst} rs {C1})"
        arm = lambda tail: f"(ir_stkn_arm_{ctor} m fh {NILF} {tail} mem na rs {' '.join(names)})".replace(" )", ")")
        call = f"ir_bdst_of_stk {x} {l0} {l1} gb tb dn {arm(T1)} {arm(T0)}"
        inst_minors.append(f"(fun {fields} => {call})" if names else f"({call})")
    inst_rec = f"IRInst.rec (fun (i0 : IRInst) => {mot_i('i0')}) {' '.join(inst_minors)} i"
    node_rec = f"IRNode.rec (fun (n0 : IRNode) => {mot_nd('n0')}) (fun (i : IRInst) (rs : IRList Nat) => {inst_rec}) nd"
    n_scrut = "(ir_nodes_get (ir_block_nodes bk) (ir_frame_pc fh))"
    n_rec = G.neutral_opt_rec("IRNode", "on", mot_n, G.refl("IRConfig", G.stuck("fetch_past_end")),
                              ("nd", "IRNode"), node_rec, n_scrut, mot_n(n_scrut))
    b_scrut = "(ir_block_find (ir_func_blocks fn) (ir_frame_block fh))"
    b_rec = G.neutral_opt_rec("IRBlock", "ob", mot_b, G.refl("IRConfig", G.stuck("no_block")),
                              ("bk", "IRBlock"), n_rec, b_scrut, mot_b(b_scrut))
    f_scrut = "(ir_func_find (ir_mod_funcs m) (ir_frame_func fh))"
    f_rec = G.neutral_opt_rec("IRFunc", "o", mot_f, G.refl("IRConfig", G.stuck("no_func")),
                              ("fn", "IRFunc"), b_rec, f_scrut, mot_f(f_scrut))
    binders = ("(m : IRModule) (fh : IRFrame) (gb : IRFrame) (tb : IRList IRFrame) (dn : IRList Nat) "
               "(mem : IRList IRMemSlot) (na : Nat)")
    return G.defn("ir_bdst_step_cons", binders,
                  f"Eq IRConfig (ir_step m {C1}) (ir_config_set_bot (ir_step m {C0}) dn)", f_rec)


# ==========================================================================
# AXIS 2 -- the module axis keyed on the OUTCOME class (the ir_mexto family)
# ==========================================================================

FAULTS = [c for c, _ in G.ctors("IRFault")]
OUTCOMES = [c for c, _ in G.ctors("IROutcome")]
assert OUTCOMES == ["ret", "ub", "type_error", "unmodelled", "stuck", "fuel_out"], OUTCOMES
assert "no_func" in FAULTS and "no_global" in FAULTS


def fault_is(name: str, target: str) -> str:
    minors = " ".join("Bool.true" if c == target else "Bool.false" for c in FAULTS)
    return G.defn(name, "(f : IRFault)", "Bool", f"IRFault.rec (fun (_ : IRFault) => Bool) {minors} f")


NOT_ = "Bool.rec (fun (_ : Bool) => Bool) Bool.true Bool.false"

DEFS_MEXTO = [
    ("SRC_FAULT_IS_NO_FUNC", "ir_fault_is_no_func", lambda: fault_is("ir_fault_is_no_func", "no_func"),
     f"ir_fault_is_no_func: Bool test for the `no_func` fault -- one IRFault.rec, one minor per constructor READ OFF the inductive declaration ({len(FAULTS)} today), true only at no_func. A new IRFault constructor re-mints it. " + D),
    ("SRC_FAULT_IS_NO_GLOBAL", "ir_fault_is_no_global", lambda: fault_is("ir_fault_is_no_global", "no_global"),
     "ir_fault_is_no_global: the same for the `no_global` fault -- one IRFault.rec with its minors read off the inductive declaration, true only at no_global, the fault a global-address lookup that misses produces. " + D),
    ("SRC_MEXT_OK", "ir_mext_ok", lambda: G.defn(
        "ir_mext_ok", "(c : IRConfig)", "Bool",
        "IRConfig.rec (fun (_ : IRConfig) => Bool) (fun (_ : IRMachine) => Bool.true) "
        "(fun (o : IROutcome) => IROutcome.rec (fun (_ : IROutcome) => Bool) "
        "(fun (_ : IRList IRScalar) => Bool.true) (fun (_ : IRFault) => Bool.true) "
        f"(fun (f : IRFault) => {NOT_} (ir_fault_is_no_global f)) (fun (_ : IRFault) => Bool.true) "
        f"(fun (f : IRFault) => {NOT_} (ir_fault_is_no_func f)) Bool.true o) c"),
     "ir_mext_ok: *** THE MODULE AXIS'S PREMISE, KEYED ON THE OUTCOME CLASS. *** True of every running configuration and of every halted one EXCEPT `stuck no_func` and `type_error no_global` -- the only two outcomes a module lookup that misses can produce (the function fetch, a jump's current function, a call's callee: stuck no_func; a global's address: type_error no_global). Everything else a step can do -- return, any other fault, a sanctioned panic, an unmodelled arm -- is the same term in every extension of the module, so a callee that HALTS transports across modules exactly when its halt is not a lookup miss. The running premise of ir_mext_step is the special case (ir_mext_ok_of_running). " + D),
]

PINS_MEXTO = [
    ("SRC_MEXT_OK_RUNNING", "ir_mext_ok_running", "(s : IRMachine)",
     "(ir_mext_ok (IRConfig.running s))", "Bool.true", "a running configuration passes"),
    ("SRC_MEXT_OK_NO_FUNC", "ir_mext_ok_no_func", "",
     "(ir_mext_ok (IRConfig.halted (IROutcome.stuck IRFault.no_func)))", "Bool.false",
     "a function lookup miss is REFUSED -- an extension may define the function"),
    ("SRC_MEXT_OK_NO_GLOBAL", "ir_mext_ok_no_global", "",
     "(ir_mext_ok (IRConfig.halted (IROutcome.type_error IRFault.no_global)))", "Bool.false",
     "a global lookup miss is REFUSED -- an extension may define the global"),
    ("SRC_MEXT_OK_ASSERT", "ir_mext_ok_assert", "",
     "(ir_mext_ok (IRConfig.halted (IROutcome.ub IRFault.assert_failed)))", "Bool.true",
     "a sanctioned panic passes -- it is the same halt in every extension"),
    ("SRC_MEXT_OK_STUCK_NO_BLOCK", "ir_mext_ok_stuck_no_block", "",
     "(ir_mext_ok (IRConfig.halted (IROutcome.stuck IRFault.no_block)))", "Bool.true",
     "a stuck that is NOT a function miss passes -- the block lookup is inside a function the fetch already found, so it is the same lookup in every extension"),
    ("SRC_MEXT_OK_TYPE_ERROR_NOT_INT", "ir_mext_ok_type_error_not_int", "",
     "(ir_mext_ok (IRConfig.halted (IROutcome.type_error IRFault.not_int)))", "Bool.true",
     "a type_error that is NOT a global miss passes"),
    ("SRC_MEXT_OK_RET", "ir_mext_ok_ret", "(vs : IRList IRScalar)",
     "(ir_mext_ok (IRConfig.halted (IROutcome.ret vs)))", "Bool.true", "a return passes"),
]

SUPPORT_MEXTO = [
    ("SRC_MEXT_OK_BACK", "ir_mext_ok_back",
     "def ir_mext_ok_back (m : IRModule) (k : Nat) (c : IRConfig) (h : Eq Bool (ir_mext_ok (ir_steps k m c)) Bool.true) : Eq Bool (ir_mext_ok c) Bool.true := IRConfig.rec (fun (c0 : IRConfig) => Eq Bool (ir_mext_ok (ir_steps k m c0)) Bool.true -> Eq Bool (ir_mext_ok c0) Bool.true) (fun (s : IRMachine) (_ : Eq Bool (ir_mext_ok (ir_steps k m (IRConfig.running s))) Bool.true) => Eq.refl Bool Bool.true) (fun (o : IROutcome) (h0 : Eq Bool (ir_mext_ok (ir_steps k m (IRConfig.halted o))) Bool.true) => Eq.subst IRConfig (fun (c1 : IRConfig) => Eq Bool (ir_mext_ok c1) Bool.true) (ir_steps k m (IRConfig.halted o)) (IRConfig.halted o) (ir_steps_halted m o k) h0) c h",
     "ir_mext_ok_back: the premise is BACKWARD-closed along a run -- if the configuration k steps later passes, so does this one (a running configuration passes outright; a halted one IS its own k-step successor, ir_steps_halted). The twin of ir_stk_running_back, and what ir_mexto_steps hands the one-step lemma. " + D),
    ("SRC_MEXT_OK_OF_RUNNING", "ir_mext_ok_of_running",
     "def ir_mext_ok_of_running (c : IRConfig) (h : Eq Bool (ir_stk_running c) Bool.true) : Eq Bool (ir_mext_ok c) Bool.true := IRConfig.rec (fun (c0 : IRConfig) => Eq Bool (ir_stk_running c0) Bool.true -> Eq Bool (ir_mext_ok c0) Bool.true) (fun (s : IRMachine) (_ : Eq Bool (ir_stk_running (IRConfig.running s)) Bool.true) => Eq.refl Bool Bool.true) (fun (o : IROutcome) (h0 : Eq Bool (ir_stk_running (IRConfig.halted o)) Bool.true) => ir_bool_false_ne_true (Eq Bool (ir_mext_ok (IRConfig.halted o)) Bool.true) h0) c h",
     "ir_mext_ok_of_running: the running premise implies the new one -- so the running-keyed module axis (ir_mext_step, ir_mext_steps, ir_mext_run) is the special case of the outcome-keyed twin. " + D),
    ("SRC_MEXT_OK_RET_TO", "ir_mext_ok_ret_to",
     "def ir_mext_ok_ret_to (ds : IRList Nat) (mem : IRList IRMemSlot) (na : Nat) (vs : IRList IRScalar) (r : IRList IRFrame) : Eq Bool (ir_mext_ok (ir_ret_to ds r mem na vs)) Bool.true := IRList.rec IRFrame (fun (r0 : IRList IRFrame) => Eq Bool (ir_mext_ok (ir_ret_to ds r0 mem na vs)) Bool.true) (Eq.refl Bool Bool.true) (fun (g : IRFrame) (r2 : IRList IRFrame) (_ : Eq Bool (ir_mext_ok (ir_ret_to ds r2 mem na vs)) Bool.true) => Eq.refl Bool Bool.true) r",
     "ir_mext_ok_ret_to: a return passes at EVERY caller stack -- into a caller it is running, at the empty stack it halts with IROutcome.ret. What lets E1's T case cross modules through the outcome-keyed twin even when the return is the last step. " + D),
]


def mexto_names() -> list[str]:
    """The running-keyed module family, in gen_stack_lemmas.py's registration order."""
    return [n for n in G.NAMES if n.startswith("ir_mext_")]


def to_mexto(term: str) -> str:
    t = re.sub(r"\bir_mext_", "ir_mexto_", term)
    t = re.sub(r"\bir_stk_running_back\b", "ir_mext_ok_back", t)
    return re.sub(r"\bir_stk_running\b", "ir_mext_ok", t)


def from_mexto(term: str) -> str:
    t = re.sub(r"\bir_mext_ok_back\b", "ir_stk_running_back", term)
    t = re.sub(r"\bir_mext_ok\b", "ir_stk_running", t)
    return re.sub(r"\bir_mexto_", "ir_mext_", t)


def mextvo_names() -> list[str]:
    """The running-keyed mkv module family (crystal link 4 M0 W3), in gen_stack_lemmas.py's order;
    its run form is not twinned term-for-term (ir_mextvo_run is minted below)."""
    return [n for n in G.NAMES if n.startswith("ir_mextv_") and n != "ir_mextv_run"]


def to_mextvo(term: str) -> str:
    t = re.sub(r"\bir_mextv_", "ir_mextvo_", term)
    t = re.sub(r"\bir_stk_running_back\b", "ir_mext_ok_back", t)
    return re.sub(r"\bir_stk_running\b", "ir_mext_ok", t)


def from_mextvo(term: str) -> str:
    t = re.sub(r"\bir_mext_ok_back\b", "ir_stk_running_back", term)
    t = re.sub(r"\bir_mext_ok\b", "ir_stk_running", t)
    return re.sub(r"\bir_mextvo_", "ir_mextv_", t)


def g_mextvo_run() -> str:
    """ir_mexto_run's mkv form: a run HALTED in IRModule.mkv fs0 gs0 es0 with an outcome that is
    not a lookup miss halts with the same outcome in every mkv extension (hf / hg / henc / hlen)."""
    s0, s1, ho = f"(ir_steps k {G.MV0} c)", f"(ir_steps k {G.MV1} c)", "(IRConfig.halted o)"
    back = (f"Eq.subst IRConfig (fun (c1 : IRConfig) => Eq Bool (ir_mext_ok c1) Bool.true) {ho} {s0} "
            f"(Eq.symm IRConfig {s0} {ho} hh) hok")
    body = (f"Eq.trans IRConfig {s1} {s0} {ho} "
            f"(Eq.symm IRConfig {s0} {s1} (ir_mextvo_steps {G.MVARGS} hf hg henc hlen k c ({back}))) hh")
    binders = (f"{G.MVBLOCK} {G.PREMISE['hf']} {G.PREMISE['hg']} {G.PREMISE['he']} {G.PREMISE['hl']} "
               f"(k : Nat) (c : IRConfig) (o : IROutcome) (hh : Eq IRConfig {s0} {ho}) "
               f"(hok : Eq Bool (ir_mext_ok {ho}) Bool.true)")
    return G.defn("ir_mextvo_run", binders, f"Eq IRConfig {s1} {ho}", body)


def _mexto_desc(name: str) -> str:
    base = name[len("ir_mext_"):]
    if name == "ir_mext_step":
        what = ("*** ONE STEP IS MODULE-EXTENSION-INVARIANT WHENEVER IT IS NOT A LOOKUP MISS -- running OR halted. *** "
                "The running-keyed ir_mext_step with its premise predicate ir_stk_running replaced by ir_mext_ok and "
                "NOTHING ELSE changed: the premise was consumed only in the none-minors of the four module lookups, "
                "and each of those reduces to stuck no_func or type_error no_global, which ir_mext_ok refuses exactly "
                "as ir_stk_running did. So a step that halts with any other outcome -- a sanctioned panic, a type error "
                "of an operand, a return -- is the same halt in every extension. ")
    elif name == "ir_mext_steps":
        what = ("n steps, same n in both modules, for every run whose n-step configuration is not a lookup miss -- "
                "the twin of ir_mext_steps through ir_mext_ok_back; a halted run transports its outcome. ")
    elif base.startswith("arm_"):
        what = f"the `{base[4:]}` arm of the outcome-keyed twin -- ir_mext_{base} with its premise read through ir_mext_ok. "
    else:
        what = f"the outcome-keyed twin of ir_mext_{base} -- its premise read through ir_mext_ok. "
    return (f"ir_mexto_{base}: {what}Minted by substitution from gen_stack_lemmas.py's own term; --self-test holds "
            f"the inverse substitution to that term byte for byte. {D}")


# ==========================================================================
# THE CLASSIFIER'S CONVERSE -- for the three-way reading at an arbitrary caller
# stack (E2's open item; eval_ir_ctr_stack.rs)
# ==========================================================================
#
# E1's classifier ir_stk_botret is keyed on the fetched node and E1 proved one
# direction about it (a running step is never a bottom ret). The reading at an
# arbitrary caller stack needs the other: a bottom ret's step HALTS WITH
# IROutcome.ret. Then a run that halts with anything else -- a sanctioned panic,
# say -- was clear at every running prefix, so E1's split carries it to every
# caller stack.

DEFS_TRI = [
    ("SRC_FAULT_IS_NO_FRAME", "ir_fault_is_no_frame", lambda: fault_is("ir_fault_is_no_frame", "no_frame"),
     "ir_fault_is_no_frame: Bool test for the `no_frame` fault -- one IRFault.rec with its minors read off the inductive declaration, true only at no_frame, the halt an EMPTY frame list produces (the one outside the commuting class that is not a bottom ret). " + D),
    ("SRC_IS_RET_HALT", "ir_is_ret_halt", lambda: G.defn(
        "ir_is_ret_halt", "(c : IRConfig)", "Bool",
        "IRConfig.rec (fun (_ : IRConfig) => Bool) (fun (_ : IRMachine) => Bool.false) "
        "(fun (o : IROutcome) => IROutcome.rec (fun (_ : IROutcome) => Bool) (fun (_ : IRList IRScalar) => Bool.true) "
        "(fun (_ : IRFault) => Bool.false) (fun (_ : IRFault) => Bool.false) (fun (_ : IRFault) => Bool.false) "
        "(fun (_ : IRFault) => Bool.false) Bool.false o) c"),
     "ir_is_ret_halt: Bool test for a configuration that has HALTED WITH A RETURN -- false on a running configuration and on every other outcome. What a bottom ret's step produces (ir_stk_botret_ret). " + D),
    ("SRC_HALT_MID", "ir_halt_mid", lambda: G.defn(
        "ir_halt_mid", "(c : IRConfig)", "Bool",
        "IRConfig.rec (fun (_ : IRConfig) => Bool) (fun (_ : IRMachine) => Bool.false) "
        "(fun (o : IROutcome) => IROutcome.rec (fun (_ : IROutcome) => Bool) (fun (_ : IRList IRScalar) => Bool.false) "
        "(fun (_ : IRFault) => Bool.true) (fun (_ : IRFault) => Bool.true) (fun (_ : IRFault) => Bool.true) "
        f"(fun (f : IRFault) => {NOT_} (ir_fault_is_no_frame f)) Bool.true o) c"),
     "ir_halt_mid: *** A HALT THAT HAPPENED IN THE MIDDLE OF THE COMMUTING CLASS. *** True of a halted configuration whose outcome is neither a return nor stuck no_frame -- exactly the halts that the two exclusions of the commuting class (a bottom ret, an empty frame list) cannot produce. So a run that ends in one of them was clear at every running prefix (ir_stk_clear_of_mid), and E1's F case carries it to every caller stack. False on a running configuration. " + D),
]

PINS_TRI = [
    ("SRC_HALT_MID_ASSERT", "ir_halt_mid_assert", "",
     "(ir_halt_mid (IRConfig.halted (IROutcome.ub IRFault.assert_failed)))", "Bool.true",
     "a sanctioned panic is a mid halt"),
    ("SRC_HALT_MID_NO_FRAME", "ir_halt_mid_no_frame", "",
     "(ir_halt_mid (IRConfig.halted (IROutcome.stuck IRFault.no_frame)))", "Bool.false",
     "the empty-frame halt is NOT -- it is the empty list's step, outside the commuting class"),
    ("SRC_HALT_MID_NO_FUNC", "ir_halt_mid_no_func", "",
     "(ir_halt_mid (IRConfig.halted (IROutcome.stuck IRFault.no_func)))", "Bool.true",
     "a stuck that is not the empty-frame one IS -- E1's F witness halts this way"),
    ("SRC_HALT_MID_RET", "ir_halt_mid_ret", "(vs : IRList IRScalar)",
     "(ir_halt_mid (IRConfig.halted (IROutcome.ret vs)))", "Bool.false",
     "a return is NOT -- it is a bottom ret's step, outside the commuting class"),
    ("SRC_HALT_MID_RUNNING", "ir_halt_mid_running", "(s : IRMachine)",
     "(ir_halt_mid (IRConfig.running s))", "Bool.false", "a running configuration is not a halt at all"),
    ("SRC_IS_RET_HALT_RET", "ir_is_ret_halt_ret", "(vs : IRList IRScalar)",
     "(ir_is_ret_halt (IRConfig.halted (IROutcome.ret vs)))", "Bool.true", "a return is a return halt"),
    ("SRC_IS_RET_HALT_ASSERT", "ir_is_ret_halt_assert", "",
     "(ir_is_ret_halt (IRConfig.halted (IROutcome.ub IRFault.assert_failed)))", "Bool.false",
     "a panic is not"),
]


def g_botret_ret() -> str:
    mk = lambda fs: f"(IRMachine.mk {fs} mem na)"
    yes = lambda b: f"Eq Bool {b} Bool.true"
    goal = lambda c: yes(f"(ir_is_ret_halt {c})")
    mot_s = lambda s0: f"{yes(f'(ir_stk_botret m {s0})')} -> {goal(f'(ir_step m {s0})')}"
    mot_fs = lambda fs0: mot_s(mk(fs0))
    S0n = mk(G.cons("f", G.NIL_F))
    bl, pc, F, B, N, ND, I = G._fetch_layers()

    def layer(step, cls):
        return lambda o: f"{yes(cls(o))} -> {goal(step(S0n, o))}"

    mot_f, mot_b, mot_n = layer(*F), layer(*B), layer(*N)
    mot_nd, mot_i = layer(*ND), layer(*I)

    def none_minor(step, cls, param: str) -> str:
        none = f"(IROption.none {param})"
        return f"fun (h : {yes(cls(none))}) => ir_bool_false_ne_true ({goal(step(S0n, none))}) h"

    inst_minors = []
    for ctor, names, types, rhs in G.ARMS:
        fields = " ".join(f"({n} : {ty})" for n, ty in zip(names, types))
        app = G.inst_app(ctor, names)
        prem, concl = yes(I[1](app)), goal(I[0](S0n, app))
        lead = f"fun {fields + ' ' if fields else ''}"
        if G.is_ret_rhs(rhs):
            inst_minors.append(f"({lead}(_ : {prem}) => {G.refl('Bool', 'Bool.true')})")
        else:
            inst_minors.append(f"({lead}(h : {prem}) => ir_bool_false_ne_true ({concl}) h)")
    inst_rec = f"IRInst.rec (fun (i0 : IRInst) => {mot_i('i0')}) {' '.join(inst_minors)} i"
    node_rec = f"IRNode.rec (fun (n0 : IRNode) => {mot_nd('n0')}) (fun (i : IRInst) (rs : IRList Nat) => {inst_rec}) nd"
    n_scrut = f"(ir_nodes_get (ir_block_nodes bk) {pc})"
    n_rec = G.neutral_opt_rec("IRNode", "on", mot_n, none_minor(N[0], N[1], "IRNode"),
                              ("nd", "IRNode"), node_rec, n_scrut, mot_n(n_scrut))
    b_scrut = f"(ir_block_find (ir_func_blocks fn) {bl})"
    b_rec = G.neutral_opt_rec("IRBlock", "ob", mot_b, none_minor(B[0], B[1], "IRBlock"),
                              ("bk", "IRBlock"), n_rec, b_scrut, mot_b(b_scrut))
    f_scrut = "(ir_func_find (ir_mod_funcs m) (ir_frame_func f))"
    f_rec = G.neutral_opt_rec("IRFunc", "o", mot_f, none_minor(F[0], F[1], "IRFunc"),
                              ("fn", "IRFunc"), b_rec, f_scrut, mot_f(f_scrut))

    def t_mot(t0: str) -> str:
        return f"{yes(G.frames_case(G.cls_f_at('f'), t0))} -> {goal('(ir_step m ' + mk(G.cons('f', t0)) + ')')}"

    step_two = "(ir_step m " + mk(G.cons("f", G.cons("g", "t2"))) + ")"
    t_cons = (f"(fun (g : IRFrame) (t2 : IRList IRFrame) (_ih : {t_mot('t2')}) "
              f"(h : {yes(G.frames_case(G.cls_f_at('f'), G.cons('g', 't2')))}) => "
              f"ir_bool_false_ne_true ({goal(step_two)}) h)")
    t_rec = f"IRList.rec IRFrame (fun (t0 : IRList IRFrame) => {t_mot('t0')}) ({f_rec}) {t_cons} t"
    step_nil = "(ir_step m " + mk(G.NIL_F) + ")"
    nil_minor = (f"(fun (h : {yes('(ir_stk_botret m ' + mk(G.NIL_F) + ')')}) => "
                 f"ir_bool_false_ne_true ({goal(step_nil)}) h)")
    cons_minor = f"(fun (f : IRFrame) (t : IRList IRFrame) (_ih : {mot_fs('t')}) => {t_rec})"
    list_rec = f"IRList.rec IRFrame (fun (fs0 : IRList IRFrame) => {mot_fs('fs0')}) {nil_minor} {cons_minor} fs"
    body = (f"IRMachine.rec (fun (s0 : IRMachine) => {mot_s('s0')}) "
            f"(fun (fs : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) => {list_rec}) s hc")
    binders = f"(m : IRModule) (s : IRMachine) (hc : {yes('(ir_stk_botret m s)')})"
    return G.defn("ir_stk_botret_ret", binders, goal("(ir_step m s)"), body)


# ==========================================================================
# The registry, in REGISTRATION order
# ==========================================================================

def _fixed(src: str):
    return lambda: src


TERMS: list[tuple[str, str, object, str]] = []
TERMS += [(c, n, _fixed(s), d) for c, n, s, d in DEFS_BDST]
TERMS += [(c, n, (lambda n=n, b=b, t=t, l=l, r=r: pin_term(n, b, t, l, r)),
           f"{n}: vacuity pin -- {why}. Eq.refl, so the definition is held to this spelling and not only to its name. {D}")
          for c, n, b, t, l, r, why in PINS_BDST]
TERMS += [
    ("SRC_RESOLVE_BDST", "ir_resolve_bdst", c_resolve,
     "ir_resolve_bdst: resolving an argument list reads the locals of the executing frame only, never its dests -- IRList.rec on the ids, the cons case ir_eq_cong over IRList.cons of the head read (the same term on both sides after one iota). The one head-only fact of the family that needs induction, as ir_resolve_stack is for the stacking family. " + D),
]
_D_ROWS = [
    ("ir_bind", d_bind, "binding a result rebuilds the executing frame at the same dests field, so rewriting that field before or after is the same frame -- Eq.refl at the constructor"),
    ("ir_bind_result", d_bind_result, "IRStepResult.rec: a value routes to ir_bind_bdst, a fault halts identically on both sides because ir_config_set_bot is the identity on a halted configuration"),
    ("ir_bind2", d_bind2, "the two-result bind overflow uses -- Eq.refl"),
    ("ir_advance", d_advance, "advancing the pc -- Eq.refl"),
    ("ir_advance_set_mem", d_advance_set_mem, "an advance after a heap replacement, at EVERY replacement heap -- the store's commit path, Eq.refl"),
    ("ir_alloca_k", d_alloca_k, "allocation -- Eq.refl; heap and counter are the SAME on both sides"),
    ("ir_goto", d_goto, "an intra-function jump rebinds the locals from the branch arguments and keeps the dests -- Eq.refl"),
    ("ir_push", d_push, "a call pushes the callee OVER the executing frame, so the executing frame stops being the one that runs but stays the BOTTOM one -- Eq.refl, the rewritten frame is the advanced caller beneath the callee"),
    ("ir_ret_vals", d_ret_vals, "*** THE ONE READ OF THE FIELD. *** A return from the bottom frame hands its values to ir_ret_to at an EMPTY caller list, which halts with IROutcome.ret and never looks at the dests it was given -- so both sides are the same halt"),
]
TERMS += [(f"SRC_{h[3:].upper()}_BDST", f"{h}_bdst", fn,
           f"{h}_bdst: at a SINGLE executing frame, the writer {h} commutes with rewriting that frame's dests -- {why}. {D}")
          for h, fn, why in _D_ROWS]
_E_ROWS = [
    ("ir_store_live", e_store_live, "Bool.rec on the liveness bit: a dead cell halts identically, a live one commits through ir_advance_set_mem_bdst"),
    ("ir_store_checked", e_store_checked, "IROption.rec on the looked-up cell"),
    ("ir_store_exec", e_store_exec, "IRScalar.rec on the pointer operand, one minor per constructor read off the family declaration"),
    ("ir_jump_block", e_jump_block, "IROption.rec on the resolved block"),
    ("ir_jump_func", e_jump_func, "IROption.rec on the resolved function"),
    ("ir_jump", e_jump, "br, and the shared target of condbr and switch: the current function is read off the executing frame's function id (the same term on both sides); the branch arguments are transported through ir_resolve_bdst"),
    ("ir_condbr_b", e_condbr_b, "Bool.rec on the decided condition, each edge ir_jump_bdst"),
    ("ir_condbr_exec", e_condbr_exec, "IRScalar.rec on the condition operand"),
    ("ir_switch_n", e_switch_n, "IROption.rec on the NEUTRAL scrutinee `ir_case_find cases n` with a goal-abstracting motive whose body is ir_switch_n's own"),
    ("ir_switch_exec", e_switch_exec, "IRScalar.rec on the selector"),
    ("ir_call_exec", e_call_exec, "IROption.rec on the NEUTRAL callee lookup; a callee is ir_push_bdst after one Eq.subst through ir_resolve_bdst"),
    ("ir_callind_exec", e_callind_exec, "IRScalar.rec on the callee value"),
    ("ir_assert_b", e_assert_b, "Bool.rec on the decided condition: a failed assertion halts identically, a passed one is ir_advance_bdst"),
    ("ir_assert_exec", e_assert_exec, "IRScalar.rec on the condition operand"),
    ("ir_alloca_exec", e_alloca_exec, "IROption.rec on the count field, then on the NEUTRAL head read `ir_as_int (ir_frame_get F i)`"),
    ("ir_overflow_ints", e_overflow_ints, "one ir_bind2_bdst at ir_overflow_ints's own arguments, read from the source"),
    ("ir_overflow_vals", e_overflow_vals, "IRScalar.rec on each operand"),
    ("ir_overflow_exec", e_overflow_exec, "IRTy.rec on the declared type, one minor per constructor read off the family declaration"),
]
TERMS += [(f"SRC_{h[3:].upper()}_BDST", f"{h}_bdst", fn,
           f"{h}_bdst: at a SINGLE executing frame, the branching helper {h} commutes with rewriting that frame's dests -- {why}. {D}")
          for h, fn, why in _E_ROWS]


def _arm_desc_h(ctor: str, rhs: str) -> str:
    if rhs.startswith("IRConfig.halted "):
        how = "both sides halt identically and ir_config_set_bot is the identity on a halted configuration, so Eq.refl closes it"
    elif G.is_ret_rhs(rhs):
        how = ("the bottom frame's return: ir_ret_vals_bdst after the returned ids are transported through ir_resolve_bdst -- "
               "the dests are handed to ir_ret_to at an empty caller list, which discards them")
    else:
        how = f"one application of {G.top_tokens(rhs)[0]}_bdst at the arm's operands read from the executing frame"
        if "(ir_resolve s " in rhs:
            how += ", after one Eq.subst through ir_resolve_bdst"
    refusal = ("This is an explicit legacy refusal, not successful execution coverage. "
               if rhs.startswith("IRConfig.halted (IROutcome.unmodelled ") else "")
    return (f"ir_bdst_arm_{ctor}: the `{ctor}` arm of ir_exec at a single executing frame commutes with rewriting that "
            f"frame's dests -- {how}. NO premise: the arm is checked as a statement about every module, operand and heap, "
            f"and a failure names the arm. {refusal}{D}")


TERMS += [(f"SRC_BDST_ARM_{ctor.upper()}", f"ir_bdst_arm_{ctor}",
           (lambda c=ctor, n=names, t=types, r=rhs: arm_lemma_h(c, n, t, r)), _arm_desc_h(ctor, rhs))
          for ctor, names, types, rhs in G.ARMS]
TERMS.append(("SRC_BDST_STEP1", "ir_bdst_step1", g_step1,
              "ir_bdst_step1: *** ONE STEP OF A SINGLE-FRAME MACHINE COMMUTES WITH REWRITING THAT FRAME'S DESTS -- at every module, every frame, every heap, with NO premise. *** The executing frame IS the bottom frame here, so this is the case where the rewritten field belongs to the frame that runs: the three fetch recursors on their NEUTRAL majors (every none minor is Eq.refl -- both sides halt identically), IRNode.rec, and IRInst.rec with one minor per constructor, each its ir_bdst_arm_ lemma. " + D))
TERMS += [(c, n, _fixed(s), d) for c, n, s, d in SUPPORT]
TERMS.append(("SRC_BDST_STEP_CONS", "ir_bdst_step_cons", g_step_cons,
              "ir_bdst_step_cons: *** ONE STEP OF A MACHINE WHOSE EXECUTING FRAME HAS A CALLER BENEATH IT COMMUTES WITH REWRITING THE BOTTOM DESTS. *** No new per-arm family: the head `fh` over `gb :: tb` is the one-frame machine [fh] stacked over that tail, and E1's node-keyed arms ir_stkn_arm_<ctor> state exactly that for every non-ret arm at an empty tail -- so each non-ret minor is ir_stkn_arm_<ctor> at the rewritten tail and at the original, joined by ir_bdst_of_stk; the ret minor is ir_bdst_ret_cons. The fetch reads `fh` only, so the three fetch recursors are shared. " + D))
TERMS += [(c, n, g, d) for c, n, g, d in DEFS_MEXTO]
TERMS += [(c, n, (lambda n=n, b=b, l=l, r=r: G.defn(n, b, f"Eq Bool {l} {r}", G.refl("Bool", r))),
           f"{n}: vacuity pin -- {why}. Eq.refl, so ir_mext_ok is held to this spelling. {D}")
          for c, n, b, l, r, why in PINS_MEXTO]
TERMS += [(c, n, _fixed(s), d) for c, n, s, d in SUPPORT_MEXTO]
TERMS += [(c, n, g, d) for c, n, g, d in DEFS_TRI]
TERMS += [(c, n, (lambda n=n, b=b, l=l, r=r: G.defn(n, b, f"Eq Bool {l} {r}", G.refl("Bool", r))),
           f"{n}: vacuity pin -- {why}. Eq.refl, so the Bool test is held to this spelling. {D}")
          for c, n, b, l, r, why in PINS_TRI]
TERMS.append(("SRC_STK_BOTRET_RET", "ir_stk_botret_ret", g_botret_ret,
              "ir_stk_botret_ret: *** THE CLASSIFIER'S CONVERSE: A BOTTOM RET'S STEP HALTS WITH A RETURN. *** E1 proved that a running step is never a bottom ret (ir_stk_botret_false_of_running); this is the other half -- where the classifier fires, the step halts with IROutcome.ret, at every module and machine. IRMachine.rec, IRList.rec on the frames (the empty list and two or more frames make the classifier false by computation, refuted), then the three fetch recursors with the classifier premise abstracted alongside the step (a miss makes it false), IRNode.rec, and IRInst.rec: every non-ret constructor refutes the premise, and the ret minor is Eq.refl -- at a single frame ir_ret_to meets the empty caller list and halts. " + D))
TERMS += [(f"SRC_MEXTO_{n[len('ir_mext_'):].upper()}", "ir_mexto_" + n[len("ir_mext_"):],
           (lambda n=n: to_mexto(G.by_name(n))), _mexto_desc(n)) for n in mexto_names()]
# The mkv module axis keyed on the outcome class (crystal link 4 M0 W3, 2026-09-30) -- appended
# LAST, so every earlier registration keeps its position and its pinned digest.
TERMS += [(f"SRC_MEXTVO_{n[len('ir_mextv_'):].upper()}", "ir_mextvo_" + n[len("ir_mextv_"):],
           (lambda n=n: to_mextvo(G.by_name(n))),
           "ir_mextvo_" + n[len("ir_mextv_"):] + ": the outcome-keyed twin of gen_stack_lemmas.py's mkv term "
           + n + " -- ir_stk_running read through ir_mext_ok, nothing else changed (--self-test holds the inverse "
           "substitution to that term byte for byte), so a step or run HALTED in IRModule.mkv fs0 gs0 es0 with an "
           "outcome that is not a lookup miss transports to every mkv extension under hf / hg / henc / hlen. " + D)
          for n in mextvo_names()]
TERMS.append(("SRC_MEXTVO_RUN", "ir_mextvo_run", g_mextvo_run,
              "ir_mextvo_run: *** THE MODULE AXIS FOR A HALTED RUN OF A DERIVED (mkv) MODULE. *** A run in IRModule.mkv fs0 gs0 es0 that halts with outcome o halts with the SAME o in every IRModule.mkv fs gs es extending its function / global lookups (hf / hg) whose encodings table finds every row alike and has its length (henc / hlen), unless o is a lookup miss (ir_mext_ok) -- ir_mextvo_steps at the halted endpoint, ir_mexto_run's term with the module re-spelled and the encodings premise threaded. " + D))

NAMES = [n for _, n, _, _ in TERMS]
CONSTS = [c for c, _, _, _ in TERMS]


def minted() -> dict[str, str]:
    return {const: fn() for const, _, fn, _ in TERMS}


def by_name(name: str) -> str:
    for const, n, fn, _ in TERMS:
        if name in (n, const):
            return fn()
    raise SystemExit(f"gen_stack_axes: no term named {name}")


# ==========================================================================
# The Rust file
# ==========================================================================

HEADER = """\
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The two axes E1's split left open -- MINTED**: dests parametricity over an
//! ABSTRACT body (`ir_bdst_*`) and the module axis keyed on the outcome class
//! (`ir_mexto_*`). Statements settled in `designs/2026-09-25-e1-axes.md`.
//!
//! GENERATED by `scripts/gen_stack_axes.py --emit`. DO NOT HAND-EDIT: every
//! constant, the registration order, [`STACK_AXES_MINTED_NAMES`], the tests and
//! this doc are re-derived by the script, and `python3 scripts/gen_stack_axes.py
//! --check` refuses the file byte-for-byte if any of them differ (its
//! `--self-test` demonstrates the refusal on three hand edits).
//!
//! What is here, in registration order:
//!
//! - **Axis 1, the bottom frame's dests.** `ir_frame_set_dests`,
//!   `ir_frames_set_bot`, `ir_mach_set_bot`, `ir_config_set_bot` (rewrite the
//!   dests of the LAST frame; the identity on a halted configuration) and their
//!   vacuity pins; `ir_resolve_bdst`; the writer and branching-helper lemmas
//!   `<helper>_bdst` and the per-constructor arms `ir_bdst_arm_<ctor>` at a
//!   SINGLE executing frame, each with NO premise; `ir_bdst_step1` over them;
//!   the tail lemmas and `ir_bdst_step_cons`, the case of an executing frame
//!   with a caller beneath it, which reuses E1's `ir_stkn_arm_<ctor>` at an
//!   empty tail instead of a second per-arm family.
//! - **Axis 2, the module.** `ir_fault_is_no_func`, `ir_fault_is_no_global`,
//!   `ir_mext_ok` (running, or halted with any outcome but the two a lookup
//!   miss produces) and its pins; `ir_mext_ok_back`, `ir_mext_ok_of_running`,
//!   `ir_mext_ok_ret_to`; then the outcome-keyed twin `ir_mexto_*` of the whole
//!   running-keyed module family -- gen_stack_lemmas.py's own terms with the
//!   premise predicate substituted and nothing else changed.
//!
//! The general theorems over these (`ir_bdst_step`, `ir_bdst_steps`,
//! `ir_stk_activation_dests_gen`, `ir_mexto_run` and the compositions with the
//! split) are hand-authored in `eval_ir_stack_axes.rs`, which MUST register
//! after this stage.
//!
//! Wiring, none of it in this file: `mod eval_ir_stack_axes_minted;` and the
//! `pub use` of [`STACK_AXES_MINTED_NAMES`] in `mod.rs`, and a
//! `Specification::add_eval_ir_stack_axes_minted` entry after
//! `add_eval_ir_stack_split` in BOTH stage lists of `bundles.rs`.

use crate::spec::error::SpecError;
use crate::spec::Specification;

"""


def rust_escape(s: str) -> str:
    return s.replace("\\", "\\\\").replace('"', '\\"')


def rust_order_assert(after: str, before: str) -> str:
    """Keep the generated test assertion in rustfmt's width100 form."""
    one = f'        assert!(position_of("{after}") > position_of("{before}"));\n'
    if len(one.rstrip()) <= 100:
        return one
    return (
        '        assert!(\n'
        f'            position_of("{after}")\n'
        f'                > position_of("{before}")\n'
        '        );\n'
    )


def render_rust(terms: dict[str, str]) -> str:
    out = [HEADER]
    for const in CONSTS:
        out.append(f'const {const}: &str = "{rust_escape(terms[const])}";\n')
    out.append("\n")
    out.append(
        "/// Every declaration this stage registers, in registration order. `pub` so\n"
        "/// the census holds its copy against THIS list, and so\n"
        "/// `scripts/gen_stack_axes.py --check` has one authority for the order.\n"
        "pub const STACK_AXES_MINTED_NAMES: &[&str] = &[\n"
    )
    for name in NAMES:
        out.append(f'    "{name}",\n')
    out.append("];\n\n")
    out.append("/// `(source, description)`, positionally paired with [`STACK_AXES_MINTED_NAMES`].\n")
    out.append("const DECLS: &[(&str, &str)] = &[\n")
    for const, _, _, desc in TERMS:
        assert '"' not in desc and "\\" not in desc, desc
        assert len(desc) > 100, f"description too short to be rustfmt-stable on one row: {desc}"
        out.append(f'    ({const}, "{desc}"),\n')
    out.append("];\n\n")
    out.append(
        "impl Specification {\n"
        "    /// Register the two minted axes. MUST follow `add_eval_ir_stack_split`\n"
        "    /// (which follows the minted stacking family: `ir_stkn_arm_*`,\n"
        "    /// `ir_resolve_stack`, the `ir_mext_*` family the twin mirrors) and\n"
        "    /// `add_eval_ir_steps` (`ir_steps_halted`).\n"
        "    ///\n"
        "    /// # Errors\n"
        "    /// Returns `SpecError` if any declaration fails to elaborate or\n"
        "    /// kernel-check -- by name, one declaration per arm.\n"
        "    pub(super) fn add_eval_ir_stack_axes_minted(&mut self) -> Result<(), SpecError> {\n"
        "        for (source, description) in DECLS {\n"
        "            self.add_recursive_def(source, description)?;\n"
        "        }\n"
        "        Ok(())\n"
        "    }\n"
        "}\n"
        "\n"
        "#[cfg(test)]\n"
        "mod tests {\n"
        "    use super::*;\n"
        "\n"
        "    /// The sources stay ASCII, balanced, and declare the names listed.\n"
        "    #[test]\n"
        "    fn test_sources_balanced_ascii_and_named() {\n"
        "        assert_eq!(DECLS.len(), STACK_AXES_MINTED_NAMES.len());\n"
        "        for ((src, _), name) in DECLS.iter().zip(STACK_AXES_MINTED_NAMES) {\n"
        '            assert!(src.is_ascii(), "spec sources stay ASCII");\n'
        '            assert_eq!(src.matches(\'(\').count(), src.matches(\')\').count(), "{name}");\n'
        '            assert!(src.starts_with(&format!("def {name} ")), "{name}");\n'
        "        }\n"
        "    }\n"
        "\n"
        "    /// One single-frame arm per `IRInst` constructor and one outcome-keyed\n"
        "    /// twin arm per constructor; each main term after its arms. The count is\n"
        "    /// the one the generator read off the inductive declaration.\n"
        "    #[test]\n"
        "    fn test_one_arm_per_irinst_constructor_per_axis() {\n"
        f'        assert_eq!(count_prefixed("ir_bdst_arm_"), {G.N_ARMS});\n'
        f'        assert_eq!(count_prefixed("ir_mexto_arm_"), {G.N_ARMS});\n'
        f'{rust_order_assert("ir_bdst_step1", "ir_bdst_arm_" + G.LAST_ARM)}'
        '        assert!(position_of("ir_bdst_step_cons") > position_of("ir_bdst_ret_cons"));\n'
        f'{rust_order_assert("ir_mexto_step", "ir_mexto_arm_" + G.LAST_ARM)}'
        '        assert!(position_of("ir_mexto_steps") > position_of("ir_mext_ok_back"));\n'
        f'        assert_eq!(count_prefixed("ir_mextvo_arm_"), {G.N_ARMS});\n'
        f'{rust_order_assert("ir_mextvo_step", "ir_mextvo_arm_" + G.LAST_ARM)}'
        '        assert!(position_of("ir_mextvo_run") > position_of("ir_mextvo_steps"));\n'
        '        assert_eq!(STACK_AXES_MINTED_NAMES.last(), Some(&"ir_mextvo_run"));\n'
        "    }\n"
        "\n"
        "    fn count_prefixed(prefix: &str) -> usize {\n"
        "        STACK_AXES_MINTED_NAMES\n"
        "            .iter()\n"
        "            .filter(|n| n.starts_with(prefix))\n"
        "            .count()\n"
        "    }\n"
        "\n"
        "    fn position_of(name: &str) -> usize {\n"
        "        STACK_AXES_MINTED_NAMES\n"
        "            .iter()\n"
        "            .position(|n| *n == name)\n"
        '            .expect("every name this test asks for is listed")\n'
        "    }\n"
        "}\n"
    )
    return "".join(out)


# ==========================================================================
# Checks
# ==========================================================================

# sha256 of every term as emitted. Pinned ONLY after the EvalIr bundle accepted
# every one of them; a --self-test red means a shape moved away from what the
# kernel accepted, and the remedy is a bundle build, never a re-pin. Re-pinned
# 2026-09-25 at the merge of origin/main into the crystal lane, after the merged
# spec accepted all 145 (it added the two atomic_fetch_add_relaxed_usize_seq arms
# and moved the five terms that enumerate IRInst or read the fat-kind IRTy cases):
# eval_ir_stack_census's axes test and Full-spec witness test passed in ONE
# spec_suite process, 34 passed / 0 failed
# (target-quality/crystal-m0-merge/spec-suite.log).
PINNED_DIGESTS: dict = {
    "SRC_ADVANCE_BDST": "734cd072e2adc097ab5b06817394b569e005073e6f5261f9456fea48308611d0",
    "SRC_ADVANCE_SET_MEM_BDST": "c286ce8402c7016297bda50fe93fa98808dd7940f824f281270d9e91c3b99d27",
    "SRC_ALLOCA_EXEC_BDST": "c1b4b7675307acc12c873a22689e048070b204414e37ef6ce244230eea6652c2",
    "SRC_ALLOCA_K_BDST": "06953b22a39eb929b8de1c3d2e5d7c74c63ae61669a2fc99c8e4af1b50ea013a",
    "SRC_ASSERT_B_BDST": "2779b0784a346201680742cadf4bf78230f6be4801b0fac9190fdfb7f9e6485c",
    "SRC_ASSERT_EXEC_BDST": "258139c2e17db6794e4eb4d95ef86733d022ab102709d1fd68821d423112aef8",
    "SRC_BDST_ARM_ALLOCA": "1b85ba0310186652c5ca0b0901b44180d7522cd7bb7e67c5cc6810c8285c293f",
    "SRC_BDST_ARM_ASSERT": "7b029a7ebfbd752a4b0dab0741b5f96bf42dae8c7534490b71d340f4dfceebcd",
    "SRC_BDST_ARM_ATOMIC_FETCH_ADD_RELAXED_U64_SEQ": "95551b1d8c6b04b6854edc1f6c930b46ced7f06b8922ab5f48c4baf91ddba90e",
    "SRC_BDST_ARM_ATOMIC_FETCH_ADD_RELAXED_USIZE_SEQ": "a33e86d439048e37acef885cf305dea14d0f4b7190870e3327265213fa4e1203",
    "SRC_BDST_ARM_BINOP": "0ac6d8fc73335b5a6838f6ae489c125a2cd8fefa9c19e209abe23e7f9b540f00",
    "SRC_BDST_ARM_BORROW": "5e8c4180dfd6edad11664531f07bc2ab30f9f25a2ca3db7a4954af05bceb66cd",
    "SRC_BDST_ARM_BR": "a58486e462d60434ed27179f15def05b949f118f15230b6c9483cc3314241173",
    "SRC_BDST_ARM_CALL": "a666711617fdb129239f460ed2b4409865bad77668d33fb4a77bc0901959b6eb",
    "SRC_BDST_ARM_CALLINDIRECT": "9ee2153a969e1fcb1abd75b5f72ac4ed43d21071f5888151082a914d8ab18ec2",
    "SRC_BDST_ARM_CAST": "c9bfa3c1662053bba3549a42f917c5c01f0dde71f11e6b9058756a9749342c4e",
    "SRC_BDST_ARM_CONDBR": "691cacba1a66a70fda1727ee289ab889df327bde20a3fb42318f14658a3a3fe2",
    "SRC_BDST_ARM_CONST_": "35f258920d8fc20c8669d9cbe2d871eeff3d5161b494aa013ca4e8b8c7013267",
    "SRC_BDST_ARM_COPY": "f010ab8b575a485e65cfc2c5623f8ec8f6cee4e06ebf91116247a0168673d18c",
    "SRC_BDST_ARM_EXTRACTELEMENT": "8acd6e3a3c0c59dfb0bbae6a0be28bead9726a847c55727749588b81a59b7415",
    "SRC_BDST_ARM_EXTRACTFIELD": "63351866bb87aae2270b1468b30cb1d35a5678c1d1b3bdf28ec8db24dfd97566",
    "SRC_BDST_ARM_FCMP": "64f5d644fdb7e1caacc0e79237aeddae89bf47f2ed487cdafa57c7809977b66b",
    "SRC_BDST_ARM_GEP": "92977a0e671948babda315379d7b981d77f34d3df324656e93f9d4d5e2a794a2",
    "SRC_BDST_ARM_GLOBALADDR": "9f25d44387509af7c58dd82c913466d8c5724ecad30b602a279d8e2d33b4626e",
    "SRC_BDST_ARM_ICMP": "cd004afd6bcede3773a634c0b0cf0fb197f8b7edbb8b3d40e36591c9b17c6db5",
    "SRC_BDST_ARM_INSERTFIELD": "80ed69e5b7a45a8b64bae9b60da01b43f69b2e061dd1fb08e6ca0dfab074b465",
    "SRC_BDST_ARM_LOAD": "516310af640a8bb2c9d7f572917ac95dd16b29d94c60a57bb0ca89202a3232f5",
    "SRC_BDST_ARM_OVERFLOW": "04bc0e3bc0536f182a3574029df4bc540266351adde365cda82948c6995a62d3",
    "SRC_BDST_ARM_PTRDATA": "938c892311c8e3cee0fbd37dd269bd65c2212c2be98ec79d43224c68160a8957",
    "SRC_BDST_ARM_PTRFROMPARTS": "77aa19096b7946ef2887c761cab024ef5a7a33aff1b5fa76a180ff45f2d51581",
    "SRC_BDST_ARM_PTRMETADATA": "44ebe96eaf4d73c7740a48e472dd3cfc2356708b7fd29c46b45c0c5a783b7f9d",
    "SRC_BDST_ARM_RELEASE": "d81d4aa3ab5443ffce8a5cd6a6d7a536f24acde951f0300462605dca495c2df6",
    "SRC_BDST_ARM_RET": "4e843ca998f7ca7864d624f95e937620766aa06d8855b69f22e06436f467d21b",
    "SRC_BDST_ARM_SELECT": "618d4e3b52bf245418cbfb8b72f0209e5cec6260cbbe5d1913d0706310153a6f",
    "SRC_BDST_ARM_STORE": "b22c068a56ff93fd4028e9511a6f6a317184c3a8b49fb7296af027184448e57c",
    "SRC_BDST_ARM_SWITCH": "7f2d4e7b9e056da8288fe0fa2d70d7a839837c2f5805a1397b1f9fd46cbdbcf0",
    "SRC_BDST_ARM_UNDEF": "30ddbf55cbd393c423a87581452c88328ca6bba4f683d10baa2d4024e80b344e",
    "SRC_BDST_ARM_UNOP": "92d37e1328b0479f34229464f22973891133ebba92dbb0ad0f26198db30af667",
    "SRC_BDST_ARM_UNREACHABLE": "9512515c40144f6f36d365de914d2503f20cf6682adc34e0678c90b125532de3",
    "SRC_BDST_OF_STK": "b39b7b7902f9cc4282f62095b4fabefb5cab6438480b6513b4a7c9012f9b1ebf",
    "SRC_BDST_RET_CONS": "20cd4b864cf0127bc656f68101a385d6da4830d55a367348d273a8c885e1426d",
    "SRC_BDST_RET_TO": "28bb733ac6eee7e3f375cacad76d1a803f49942a6e528a06ef29743470679d77",
    "SRC_BDST_STACK_CONS": "585e517b76a8ef9c493acdbe2b8bac523b8cd08f1a002d5a7808c61e049a063f",
    "SRC_BDST_STEP1": "9298de434cbf3b83fa18b0501c0f1d10174d7cfceb57c083f70158d01bea6035",
    "SRC_BDST_STEP_CONS": "87cb454b64cc53b13957cf6edab4e55530cedb6ce964c5d107f9e10942d21988",
    "SRC_BIND2_BDST": "32a56ff0c522738cca85e9297a46c9d4d783539fb87e861ff23fb1f274ab6e74",
    "SRC_BIND_BDST": "1edabcc779c11d9fca82aafd92d22c55bb6eb770c82d1a0991e6d6163401776e",
    "SRC_BIND_RESULT_BDST": "73a6f34ac23f8399f9bcdcbde25c708b1205b0a737b8a1933f143acd8cc8460a",
    "SRC_CALLIND_EXEC_BDST": "b6913003fc45aad06d9c41d06d41ec50859cf9d170c8d798e857fa3bcb71ae73",
    "SRC_CALL_EXEC_BDST": "fb85a1bc64e32621bfb979dc5f2ce85d604e894e3361d03d6250b1b86f9e9fb6",
    "SRC_CONDBR_B_BDST": "5922f836d699ef21db53fbfe51de143aedeb01e03e74c1b86161d273a5521659",
    "SRC_CONDBR_EXEC_BDST": "d391330562512cb0222c0c2652868ebf083510bd22c75ee987670571fb136c9c",
    "SRC_CONFIG_SET_BOT": "8ee4c90f74d434c6823c945554af3e14eb8e078ea9b00e96c474dfeddd0f6b1f",
    "SRC_CONFIG_SET_BOT_HALTED": "eff78d6ded18aa421510e0d2b6cab191877ddec2e18f158589c03b480f7b324c",
    "SRC_FAULT_IS_NO_FRAME": "c138048d41b003d9a2eb6ae8a40faa1d3ac7030d42ca30fc2cbcd228b609e33e",
    "SRC_FAULT_IS_NO_FUNC": "c24c44d7e5bf5b3fd00fd6b46d77af45d8f2e1570774361b5fffcd2571487844",
    "SRC_FAULT_IS_NO_GLOBAL": "dc8fd8b8da7eecf73fe00829176f1eb7ad8f04937c4d3ac127e43668475898f2",
    "SRC_FRAMES_APP_SET_BOT": "dbfc986ce8b11b29f59e7554e86cc37beecb09573d50a992103b1a2da9daab6e",
    "SRC_FRAMES_APP_SET_BOT_PRE": "dbdf46dd55cd84ea3560ff0e1bd305fcba0c2da6bce0e079cd9edff41465faa3",
    "SRC_FRAMES_SET_BOT": "c14697fca1c5d9457ada8a5c67453c8c807e193be4732b6a063e0082e38acca2",
    "SRC_FRAMES_SET_BOT_NIL": "f6ea4453abb201879b7e78c4a0b84255a86c67910625aeaff53635fa36830fe9",
    "SRC_FRAMES_SET_BOT_ONE": "2555a1b221b999c424eed42e588b25d9c352dce0390d9f7b4b656ced99613afa",
    "SRC_FRAMES_SET_BOT_TWO": "0967ae6acf1e048c10304e247b88c6b941fc2f26373879fa91c596e71291d1b1",
    "SRC_FRAME_DESTS_SET_DESTS": "a9e239a38ac66c7593d40c703b83d9c71235467abb57684fb6b7d228af599d3b",
    "SRC_FRAME_FUNC_SET_DESTS": "c85bad0561c9b72e62c4cc06587eb636ffe15b297c5ba7251bd45a716d353d72",
    "SRC_FRAME_SET_DESTS": "97a9bb48a237ce563c7b6d91d3005617f41f995e61a27d55db45b9a3df7e407a",
    "SRC_FRAME_SET_DESTS_MK": "1fef8929296881c195311b68daffcf05156d7f257b33768b710255fe4dd732a4",
    "SRC_GOTO_BDST": "3ada1bb5b76b1ab74b051a25794a902dfa8472ae6680088eacceb06f35b53b0d",
    "SRC_HALT_MID": "509a139946700ca695a4cd911f1389f4d829b1f1c98fa22644ecc78c3dc2ccb4",
    "SRC_HALT_MID_ASSERT": "de41d3a695d839a578b6c19278ad99e75ce2b55611a46d3b9885198220e3f8fd",
    "SRC_HALT_MID_NO_FRAME": "8429d75a5bf8e8637231fd291b63656efe8c23af69e78a49dd592753db01ad49",
    "SRC_HALT_MID_NO_FUNC": "2721fb5d6f3caa1bddb88855595a2ed7adbb41fb1f7af165b7f1cd195294bd28",
    "SRC_HALT_MID_RET": "2addc5e32e76dcef37bc27c69e9ff5ceef6863edcf66a4db83777f06737fd75f",
    "SRC_HALT_MID_RUNNING": "54964fda3b35f6179f42e745b9e9dda60e7337995785a09a902320b60ed56cf9",
    "SRC_IS_RET_HALT": "483a0db8f3e0809ae823d7112ed8410730882a56480578c73e7da00a07a7212a",
    "SRC_IS_RET_HALT_ASSERT": "c84ff3331999889609b95112e3fda1c6cf055f46f9f745ffe2c156352f5cd487",
    "SRC_IS_RET_HALT_RET": "96d0d322eda1e09f72fe0e3444eaaaa8133c5e066bb95a2e8289384178a1ee3d",
    "SRC_JUMP_BDST": "986b9fec5906a590e3723b5d448b4681a0750f538765dc819f6015040631b0c3",
    "SRC_JUMP_BLOCK_BDST": "5c853904dd043f581fcfe4e3f5ebdd9858d256ab50ef04e1cb158336c58228d4",
    "SRC_JUMP_FUNC_BDST": "de4e757808c403a60b3e268c393b055adb093a9d80144c65fda1fc8db03c1509",
    "SRC_MACH_SET_BOT": "c2ade98d7ac8ef6e193780df303a708bec67cd4aec36447b4f00bfd2019ebe08",
    "SRC_MEXTO_ARM_ALLOCA": "95872fef66bb217de164b8b0d128b3cadb6cbc4f1010f38b8da569ca52c02250",
    "SRC_MEXTO_ARM_ASSERT": "4cce146f78ecb50214603e0f267af28978350fe5edc41d3246a9196651f199d0",
    "SRC_MEXTO_ARM_ATOMIC_FETCH_ADD_RELAXED_U64_SEQ": "3d830139d39d7bce27ed3adc638b1f98db5671cb535860ef39e714c09c1809e1",
    "SRC_MEXTO_ARM_ATOMIC_FETCH_ADD_RELAXED_USIZE_SEQ": "4bd5c1299a37a96e6d7475b169cb50472f28d11f4307c487e4ccef099505c0f5",
    "SRC_MEXTO_ARM_BINOP": "8a1e8fdc5b067dcdf96b1dfdf9faa1e30ef448f114d79ec38b1a30a52b29269f",
    "SRC_MEXTO_ARM_BORROW": "41c65b147d0b9c12df4a26b96dab3a940290679670856540f3c0d2c7337eddd3",
    "SRC_MEXTO_ARM_BR": "5ed6d30337121367d26c9cd6e278dd67da6480caebd441f8fac4b3c600ec942b",
    "SRC_MEXTO_ARM_CALL": "46e0138cac86169489a7b3a012b4006216d51dafdc3630bf6e896f2f5d8c9cf3",
    "SRC_MEXTO_ARM_CALLINDIRECT": "95f6e2333e3c3c92e91712796e70a7d5ce62735f1170382adcdc665e343ca1b6",
    "SRC_MEXTO_ARM_CAST": "a2bda65c67b53910c2d271139c0140e52626fc24ebdc729a1e15e363b0cbe729",
    "SRC_MEXTO_ARM_CONDBR": "cf990d2271f75606d595745db8f0cbb06a17d0757bd5bf2f3d1d6c3090b7f4c9",
    "SRC_MEXTO_ARM_CONST_": "046dfa6dc8ddace377868cca8ea45d7d703e6445e8ca09c0943ebda0b622fd21",
    "SRC_MEXTO_ARM_COPY": "106dd4bbe35215930c4b478ca798591d2fa429a053ab48f127a74c8ea0991f09",
    "SRC_MEXTO_ARM_EXTRACTELEMENT": "2ff7544671c62137b45af038fd4465a911f3091ab76e1c860349db94009fdaa6",
    "SRC_MEXTO_ARM_EXTRACTFIELD": "22196239197cc6df593d1ed0e851b3833dde516363d0da9035f546e1debec2c4",
    "SRC_MEXTO_ARM_FCMP": "02229bd8e95a0ae42e3b47451457ce7679b47344d1eb34f6dd5ecbe5553dfc50",
    "SRC_MEXTO_ARM_GEP": "8196e14d166654d800373e9cb7c80789742989fdc67e0fbf6e7864c14c61f55b",
    "SRC_MEXTO_ARM_GLOBALADDR": "4b825e510cde85dcaab01bb4f06c78e384fc5eb742e059cecf2033ae220bb2c1",
    "SRC_MEXTO_ARM_ICMP": "8b233ca73eb10b280ca95499194ca90127ee1f5ae6c9114d57e7aff6d960c8b3",
    "SRC_MEXTO_ARM_INSERTFIELD": "88d178eb389621f7d36571b604342f80b52b5e025d28b01cc9f62f76e4fe52a3",
    "SRC_MEXTO_ARM_LOAD": "2df2d004adaf387ed1e22aeadd83c621277ccf7010fbb155e665770753af5738",
    "SRC_MEXTO_ARM_OVERFLOW": "013ecdc2789e4e95a91fbba54fc57f025ed67273bd9827a81acf27c2d6aeae33",
    "SRC_MEXTO_ARM_PTRDATA": "bda9602b3b295bc804e5226c792d7fdedd614a55de28273d3873256f8a458fa1",
    "SRC_MEXTO_ARM_PTRFROMPARTS": "5dc90817b9df75d952bfb72642af545f21f887e72cf8a3ade5ab3338bec35452",
    "SRC_MEXTO_ARM_PTRMETADATA": "ff4c7b467407482e3b0657bb85b4391939e4d8facaed5a663cbb476a8c8d70c0",
    "SRC_MEXTO_ARM_RELEASE": "59f15932561daea924dc6d76095828bc57e823e44921a3e3f6b873dadd4b0b95",
    "SRC_MEXTO_ARM_RET": "49c3286fda38eff4acaabe0289f35336a2460d573666682c328fd615e7fd5b01",
    "SRC_MEXTO_ARM_SELECT": "4104509c7f5a8b14ea6820a6e29d92c59310c340d44ae96f2875bcb35ca67011",
    "SRC_MEXTO_ARM_STORE": "6f36f3312275c713cb469a0d7b101dfa170dc01a4c00487419b518a42e3bdbd1",
    "SRC_MEXTO_ARM_SWITCH": "ce97b0eb88aa6fe062482feecccc6c96221ec5682c2435f5b32e6806d20308b0",
    "SRC_MEXTO_ARM_UNDEF": "216b6dc23bb224f8431005ebfcd56f0e6b514201e047c2239fa33ac72caef109",
    "SRC_MEXTO_ARM_UNOP": "00e4cc52bb919da1fa50339315d43dc2d92e76d67117183bfacd1d9aa8280075",
    "SRC_MEXTO_ARM_UNREACHABLE": "3bb47db596ec24508857c7bc0f855ee812aa34a8b7f6b358b78c92701266f793",
    "SRC_MEXTO_CALLIND_EXEC": "8346a93351eb35470719137d0c588476b140eb7bab5ef66c14d6fa1d440eaef3",
    "SRC_MEXTO_CALL_EXEC": "bce37061c6f7cdc578d85d735922b104fac176c5429bb1d042aec80393f2d12e",
    "SRC_MEXTO_CONDBR_B": "71b9f332a2069aa04c8c4d4b8d5f96c33e6792b86aef079090f0accb56884310",
    "SRC_MEXTO_CONDBR_EXEC": "f39d81f3f63e56162c768ecc22ff40a7a67d3e470b99052bc5a9ab29a89c9f71",
    "SRC_MEXTO_GLOBALADDR": "d75924bf1a651e3c5d4f25a5ffb793086917be78f8aca40c6335765853d33ea9",
    "SRC_MEXTO_JUMP": "87dbf2ed09d5f36fcbd4f05115df071185ab55e83434f27fcad9e03938d7b06f",
    "SRC_MEXTO_STEP": "2ad6c8728fc0970e8304cec9745655c05fd98c68c46f356fc05784298ea43f14",
    "SRC_MEXTO_STEPS": "dd006fb7c6cf82c0e2fd3dfd361158ebf0e8c2613f1066b04ada1974866e3ae3",
    "SRC_MEXTO_SWITCH_EXEC": "b605f913231340eedb190c0c87bea467df214a53662725f7e9c76b88a4264ef6",
    "SRC_MEXTO_SWITCH_N": "f017f89ca29391438e78c0bd5569c9fce43fb944fe73b183a7504feda50488f0",
    "SRC_MEXTVO_ARM_ALLOCA": "81f388bf3d8979a3f1e5f98348fd717690ae72ef5a28781efa0b64b9f98da663",
    "SRC_MEXTVO_ARM_ASSERT": "4f4d87f74c9a92d3159fd21b627f0e499dfb49c2d882b7148d92dec1bcb88a81",
    "SRC_MEXTVO_ARM_ATOMIC_FETCH_ADD_RELAXED_U64_SEQ": "9bb433731f1b21cbf3e9b0c05ba798404f398bc44804cfef1ff835f4fa6a3bdd",
    "SRC_MEXTVO_ARM_ATOMIC_FETCH_ADD_RELAXED_USIZE_SEQ": "47e6f00c007c3083b04c4e4dd062e563ea1de8d0c86b2569c986b227ec4387db",
    "SRC_MEXTVO_ARM_BINOP": "d2a4a3d302e0353988ff808c5e4362c42a422b62191ad5b26b99f9d0436fba1a",
    "SRC_MEXTVO_ARM_BORROW": "5395c241d3ba9ea028a34e44b901b91992dfa49432c35b362c50fcdcf17ab2b3",
    "SRC_MEXTVO_ARM_BR": "2e81dcee019656b89de6603c371191ececfd332a5d9f2abc5c2caf01d89390d1",
    "SRC_MEXTVO_ARM_CALL": "b5412ceb2114c3ae51d99ced1d9836b551b7b18547990901b6bb15b56040ea05",
    "SRC_MEXTVO_ARM_CALLINDIRECT": "170cbee5ad9a1b114b32a251914204ffaf50df32630c96de5b0cd3f200c0979a",
    "SRC_MEXTVO_ARM_CAST": "9cd07b5676ec66d8a60f9c669450ad9dc7b43c76f8762379eac9189d67958147",
    "SRC_MEXTVO_ARM_CONDBR": "2fc0389dca2ea1557f8582458cd83f1f91d4502a545f8973127742a137bbcf3e",
    "SRC_MEXTVO_ARM_CONST_": "89e15eacb50499bf4d2cf3b4394cb8ef8fc1a570f5fec8f95365852e319c01d1",
    "SRC_MEXTVO_ARM_COPY": "759fb6c35998f10b17bde2365aae5866a4fdf379498099e77de6e71ebdc89619",
    "SRC_MEXTVO_ARM_EXTRACTELEMENT": "840e4e1bfe82b790128f600ef6cfa9c68ddacb549733357a3f7382a1babf3699",
    "SRC_MEXTVO_ARM_EXTRACTFIELD": "d5f34236aa065f867d35d806ceff58e801d87c468af5fc1a9f3f2f4fc8c0e810",
    "SRC_MEXTVO_ARM_FCMP": "3eb94b4e09cdb63cf9a0aaa3cc02f51ec2909f5f5f2aa8ad8a79b88d6bcb04a9",
    "SRC_MEXTVO_ARM_GEP": "f6c90125182e985d43ad5e7c25e0a9f44a053a0cfca7f6ad26a22108a063d230",
    "SRC_MEXTVO_ARM_GLOBALADDR": "13f7e1da3c1b5c97db6e05f05c32ca729f0be63ffb247b54a1f793bdd33fea86",
    "SRC_MEXTVO_ARM_ICMP": "9422251f8a5f666ed0a69d083b93057a065c5275e90a75c7b9f7d9ce35dd216d",
    "SRC_MEXTVO_ARM_INSERTFIELD": "0a6f65b9ad45a2f81ea70ca0652345d9b10efaa672b3daad30d0bd5e50a43ef4",
    "SRC_MEXTVO_ARM_LOAD": "40b29bc0fbbacddc172c3848e69538bf756af2870345f58e973b8485639cc592",
    "SRC_MEXTVO_ARM_OVERFLOW": "c3e3756a8e621c7c4a3495737f7510df5be180256c3d4eb018e452155a92b426",
    "SRC_MEXTVO_ARM_PTRDATA": "9ba5186a870f60fd61199f01071e046430ffeeae9da70067a50b83744244e3d5",
    "SRC_MEXTVO_ARM_PTRFROMPARTS": "5f87c2cc66b669dc676795bd3e255a098a4cb40ef7c804714836aeaf5a17dbed",
    "SRC_MEXTVO_ARM_PTRMETADATA": "d69bd7581f011cf5dbd26f2d4f3612fc0b9c86b7235b3c338b847a138ce604ea",
    "SRC_MEXTVO_ARM_RELEASE": "598c797510901b6dee0b0fa53123aeeb6eb03f4d4219d81fd3d2056312b8f92d",
    "SRC_MEXTVO_ARM_RET": "7897067a9f32a799979454ac799edd3f0cd6f9eca9e2d01fccd3379456fe70ad",
    "SRC_MEXTVO_ARM_SELECT": "565e45278d4ac04adb4f8dcd19f35470e09cdd994a7c867f46a26358abc7a8cc",
    "SRC_MEXTVO_ARM_STORE": "3f7548270d0cab9e4b26eacd469d165726950c3d6627395ab37541c244b30ae3",
    "SRC_MEXTVO_ARM_SWITCH": "843f0e9b2f7aecc95f8b91b2104ce6e07e42c919f206e5f708a040c16d02b0b5",
    "SRC_MEXTVO_ARM_UNDEF": "c699511047624cb26a7cc672786c519eca46872572de69157e663ae314798f5e",
    "SRC_MEXTVO_ARM_UNOP": "c8e93cd639566dd480f9143e7929955312bcecab2a9f187596670fae1237f9b1",
    "SRC_MEXTVO_ARM_UNREACHABLE": "fde6dbe088e71455491420bc93f992abd3f3a0af41529d4ef8cc54ab13b2adb5",
    "SRC_MEXTVO_CALLIND_EXEC": "1768d24ebbd4495520ee70e773ea8e314af5d4fa9714cfd53074b79fbe7c6b3d",
    "SRC_MEXTVO_CALL_EXEC": "1f331f9b8d18673f5cd6cc6077d0b2177d3a70a6352dd76824ad54bc429649d7",
    "SRC_MEXTVO_CONDBR_B": "daa1858cf6a191bd79af581f8186ad84c8171999214335b3373ac8930ca24676",
    "SRC_MEXTVO_CONDBR_EXEC": "81238ca964a7a57e5552525f516adbd33588e82a370c75de8ac1014fd4953628",
    "SRC_MEXTVO_GLOBALADDR": "b4f74feef47bddc25a49756d9c0ad266796dfc19259578b0716581f4ed7843b9",
    "SRC_MEXTVO_JUMP": "94f8365432e6dff7b496f347d45f24ce1bf01d40f02f33a0e930c2e20499dff2",
    "SRC_MEXTVO_RUN": "4480f5ea0f0f81bd79638084ef1460360a3875ebae4d0242107b7a66924b189f",
    "SRC_MEXTVO_STEP": "bb9df578e92ecdffe905c4ad8606b6c103e79d0847ff2460e234ce1889daaa4b",
    "SRC_MEXTVO_STEPS": "a5a7135ba7ef7a076329752a558296f9fa1db2f34e240390cdf070b9164b8b2f",
    "SRC_MEXTVO_SWITCH_EXEC": "3133841fbcb1f033904dc1655f51dba63b3994f5eda0fd3c9b466f9747084274",
    "SRC_MEXTVO_SWITCH_N": "60a465fa79c0f1e88cbf98760c38a98e194b356093bf3b573c82c75e60fcbc52",
    "SRC_MEXT_OK": "95f365ad96484523c65705b5d93e5fb2fc5ee6830a78f8bb14e547420b614c79",
    "SRC_MEXT_OK_ASSERT": "499039f93de1f135aaf6b9726eae87caeee89d7d0d249e1d746c5d4d02efc929",
    "SRC_MEXT_OK_BACK": "973a3143873c3159c5e4d7f2aec333caef7a3dffc99c81080caaa2e96c081903",
    "SRC_MEXT_OK_NO_FUNC": "09b8b395ea553cc282fb2f992262861fd8e57fcb5116a07ed187c37a72a6772d",
    "SRC_MEXT_OK_NO_GLOBAL": "7994df2beb0e7eaec499bfad62f615727df901918612a6823bc7a4fd22f85f43",
    "SRC_MEXT_OK_OF_RUNNING": "36a1609fe787638eb4310817ec55c2462c8693151bfd467ee7fb3c54ad1d012e",
    "SRC_MEXT_OK_RET": "17ba19e87defbe1730c99bbc21334d9d8c28739233b96e3711e13e34db39e875",
    "SRC_MEXT_OK_RET_TO": "5878e6dc0a14cb17dfe5a750be9cbedb7ac64e622624966862963a4db048cdf6",
    "SRC_MEXT_OK_RUNNING": "e808ee1f546e4fdd3a3991ef1e7eb217a0f04feb76d2bc5c535cd9381a24ecf3",
    "SRC_MEXT_OK_STUCK_NO_BLOCK": "8a981e1cb898847f8e4fa023e29b73c6ea726c7cecd1e7a84e74c3af222a3a88",
    "SRC_MEXT_OK_TYPE_ERROR_NOT_INT": "4f403156d86db130dc2f84a74ae2c361a1ec537da06f391899cbaba81bd9742f",
    "SRC_OVERFLOW_EXEC_BDST": "159b475eef10743efd093b075131931d289d830d6b858066b24c26e8abb8057f",
    "SRC_OVERFLOW_INTS_BDST": "edfb7032a00f2917ebd7f533e47b1dde2374940434891cc950a7e08de88b5f41",
    "SRC_OVERFLOW_VALS_BDST": "6ffcb4f5eac071d48fb99abca3f894bd1ed050454649d65cd182292689a325a2",
    "SRC_PUSH_BDST": "ebe20c89cd433cf00746f03733537c3c8e95212a1acc614c939c00d9bb417553",
    "SRC_RESOLVE_BDST": "9ce4ec87cd2e77b7419ab0bf7f9ebd8413e2e24bfc36f380ad805c89991991c4",
    "SRC_RET_VALS_BDST": "2a43d072a81414981c427e9bb25a7d71ce21d5edc375a87a17f4e1bb0f63c193",
    "SRC_STK_BOTRET_RET": "14d79b67ed852271055c5e5d5573254c4d00e0116b7e0fd1af3dcbe5c8bca692",
    "SRC_STORE_CHECKED_BDST": "00b6d22c8644c715b29e1db276b2c1dbb0023e31c99ded0ac8ec7d45dc98972b",
    "SRC_STORE_EXEC_BDST": "fd63137d6566c238def08517504a0f7cee7364b207b49b90e07f515bdf722669",
    "SRC_STORE_LIVE_BDST": "ee18438d4ad6ea5ed78adbc9ba44223edba5adadba68e01b1ad362fdf374485c",
    "SRC_SWITCH_EXEC_BDST": "db65ccc1fe31f65970e6f269519fad006c1b20078d85cb598b8a8e45045574d1",
    "SRC_SWITCH_N_BDST": "6bb462fd7ea038ec6878dc97f75f714da46c953987d295a55ed0e6c2bf893da0",
}


def digests(terms: dict[str, str]) -> dict[str, str]:
    return {k: hashlib.sha256(v.encode()).hexdigest() for k, v in terms.items()}


# Names registered BEFORE this stage that the minted terms may reference. Read
# from the sources that register them, so a rename there is noticed here.
def registered_before() -> set[str]:
    seen: set[str] = set(re.findall(r'"def (ir_\w+) ', (CORE / "eval_ir_stack.rs").read_text()))
    seen |= set(G.NAMES)
    seen |= set(G.MACHINE)
    seen |= set(re.findall(r'"def (ir_\w+) ', (CORE / "eval_ir_stack_split.rs").read_text()))
    return seen


def structural(terms: dict[str, str]) -> list[str]:
    bad: list[str] = []
    before = registered_before()
    seen = set(before)
    own = set(NAMES)
    for const, name, _, _ in TERMS:
        src = terms[const]
        if not src.isascii():
            bad.append(f"{name}: non-ASCII")
        if src.count("(") != src.count(")"):
            bad.append(f"{name}: unbalanced parens")
        if "{S}" in src or '"' in src or "\\" in src:
            bad.append(f"{name}: leftover placeholder or quote")
        if not src.startswith(f"def {name} "):
            bad.append(f"{name}: source declares something else: {src[:50]}")
        body = src.split(" := ", 1)[1] if " := " in src else ""
        for ref in set(re.findall(r"\b(ir_\w+_bdst|ir_bdst_\w+|ir_mexto_\w+|ir_mextvo_\w+|ir_mext_ok\w*|ir_frames?_set_\w+|"
                                  r"ir_mach_set_bot|ir_config_set_bot|ir_stkn_\w+|ir_resolve_stack|"
                                  r"ir_fault_is_no_\w+|ir_frames_app_set_bot\w*|ir_is_ret_halt|ir_halt_mid)\b", body)):
            if ref in own and ref not in seen:
                bad.append(f"{name}: references {ref}, which is registered LATER in this stage")
            elif ref not in own and ref not in before:
                bad.append(f"{name}: references {ref}, which nothing registers before this stage")
        seen.add(name)
    # Axis 1: one arm per IRInst constructor, and exactly the stacking family's
    # helper set -- the two per-arm families must cover the same machine helpers.
    n_inst = len(G.ctors("IRInst"))
    if sum(1 for n in NAMES if n.startswith("ir_bdst_arm_")) != n_inst:
        bad.append(f"ir_bdst arms are not one per IRInst constructor ({n_inst})")
    stk_helpers = {n[: -len("_stack")] for n in G.NAMES if n.endswith("_stack") and n != "ir_ret_to_stack"
                   and n[: -len("_stack")] in G.MACHINE}
    stk_helpers |= {"ir_advance_set_mem"}
    bdst_helpers = {n[: -len("_bdst")] for n in NAMES if n.endswith("_bdst") and n != "ir_resolve_bdst"}
    want = (stk_helpers - {"ir_getd", "ir_mach_mem", "ir_resolve", "ir_ret_to"}) | {"ir_ret_vals"}
    if bdst_helpers != want:
        bad.append(f"the _bdst helper set is not the stacking family's: extra {sorted(bdst_helpers - want)}, "
                   f"missing {sorted(want - bdst_helpers)}")
    # Axis 2: the twin is the running-keyed family with ONE predicate substituted.
    for n in mexto_names():
        twin = "ir_mexto_" + n[len("ir_mext_"):]
        t = terms[CONSTS[NAMES.index(twin)]]
        if from_mexto(t) != G.by_name(n):
            bad.append(f"{twin}: undoing the substitution does not give back gen_stack_lemmas.py's {n}")
        if "ir_stk_running" in t:
            bad.append(f"{twin}: the running predicate survives")
    # The mkv twin of the outcome-keyed axis: the same ONE substitution over the mkv family.
    for n in mextvo_names():
        twin = "ir_mextvo_" + n[len("ir_mextv_"):]
        t = terms[CONSTS[NAMES.index(twin)]]
        if from_mextvo(t) != G.by_name(n):
            bad.append(f"{twin}: undoing the substitution does not give back gen_stack_lemmas.py's {n}")
        if "ir_stk_running" in t:
            bad.append(f"{twin}: the running predicate survives")
    if sum(1 for n in NAMES if n.startswith("ir_mextvo_")) != len(mextvo_names()) + 1:
        bad.append("the mkv outcome-keyed axis is not one twin per mkv module term plus ir_mextvo_run")
    return bad


CONST_RE = re.compile(r'^const (SRC_[A-Z0-9_]+): &str = "(.*?)";$', re.M)
NAMES_RE = re.compile(r"pub const STACK_AXES_MINTED_NAMES: &\[&str\] = &\[(.*?)\];", re.S)
DECLS_RE = re.compile(r"const DECLS: &\[\(&str, &str\)\] = &\[(.*?)\n\];", re.S)
ROW_RE = re.compile(r"^\s*\((SRC_[A-Z0-9_]+),", re.M)


def check_text(have: str, want: str) -> list[str]:
    if have == want:
        return []
    bad: list[str] = []
    have_consts = dict(CONST_RE.findall(have))
    for const, body in CONST_RE.findall(want):
        if const not in have_consts:
            bad.append(f"MISSING {const}")
        elif have_consts[const] != body:
            bad.append(f"DIFFERS {const}: committed {len(have_consts[const])} chars, minted {len(body)} chars")
    extra = sorted(set(have_consts) - set(CONSTS))
    if extra:
        bad.append(f"UNDECLARED consts: {extra} -- the census refuses hand-added terms")
    names = NAMES_RE.search(have)
    if not names or re.findall(r'"([^"]+)"', names.group(1)) != NAMES:
        bad.append("STACK_AXES_MINTED_NAMES is not the minted list")
    table = DECLS_RE.search(have)
    if not table or ROW_RE.findall(table.group(1)) != CONSTS:
        bad.append("DECLS rows are not the minted registration order")
    if not bad:
        bad.append("the file differs outside the consts and tables (doc, tests, or whitespace)")
    return bad


def mutation_test(want: str) -> list[str]:
    bad: list[str] = []
    if check_text(want, want):
        bad.append("MUTATION: the freshly rendered file does not pass its own check")
    found_consts = CONST_RE.findall(want)
    # The first term from the middle on that has an `Eq` to corrupt (a definition or a pin
    # in the middle may have none).
    const, body = next((c, b) for c, b in found_consts[len(CONSTS) // 2:] if "Eq" in b)
    i = body.index("Eq")
    edited = want.replace(f'const {const}: &str = "{body}";', f'const {const}: &str = "{body[:i]}Qe{body[i + 2:]}";', 1)
    if edited == want or not any(f"DIFFERS {const}" in b for b in check_text(edited, want)):
        bad.append(f"MUTATION: a hand-edited term inside {const} was not refused")
    hand = 'const SRC_HAND_ADDED: &str = "def ir_bdst_hand_added (x : Nat) : Nat := x";\n'
    added = want.replace(f"const {CONSTS[-1]}: &str = ", hand + f"const {CONSTS[-1]}: &str = ", 1)
    found = check_text(added, want)
    if added == want or not any("UNDECLARED" in b for b in found):
        bad.append(f"MUTATION: a hand-added const was not refused: {found}")
    rows = ROW_RE.findall(DECLS_RE.search(want).group(1))
    lines = want.split("\n")
    ia = next(i for i, ln in enumerate(lines) if ln.startswith(f"    ({rows[0]}, "))
    ib = next(i for i, ln in enumerate(lines) if ln.startswith(f"    ({rows[1]}, "))
    lines[ia], lines[ib] = lines[ib], lines[ia]
    if not any("DECLS rows" in b for b in check_text("\n".join(lines), want)):
        bad.append("MUTATION: a reordered DECLS row was not refused")
    return bad


def check() -> int:
    if not MINTED_RS.exists():
        print(f"MISSING: {MINTED_RS} does not exist; run --emit")
        return 1
    bad = check_text(MINTED_RS.read_text(), render_rust(minted()))
    for line in bad:
        print(line)
    if bad:
        print(f"gen_stack_axes: {MINTED_RS.name} is not what --emit produces ({len(bad)} finding(s))")
        return 1
    print(f"gen_stack_axes: {len(TERMS)} terms, STACK_AXES_MINTED_NAMES and DECLS match {MINTED_RS.name}")
    return 0


def self_test() -> int:
    terms = minted()
    bad = structural(terms)
    bad += mutation_test(render_rust(terms))
    have = digests(terms)
    for k in sorted(set(CONSTS) - set(PINNED_DIGESTS)):
        bad.append(f"UNPINNED: {k} is minted but has no pinned digest (run --pin after a kernel build accepts it)")
    for k in sorted(set(PINNED_DIGESTS) - set(CONSTS)):
        bad.append(f"ORPHAN DIGEST: {k} is pinned but no emitter produces it")
    for k, v in PINNED_DIGESTS.items():
        if k in have and have[k] != v:
            bad.append(f"DIGEST MOVED: {k}")
    for line in bad:
        print(line)
    n_b = sum(1 for n in NAMES if n.startswith("ir_bdst_arm_"))
    n_o = sum(1 for n in NAMES if n.startswith("ir_mexto_"))
    print(f"tables read from source: IRInst {len(G.ctors('IRInst'))}, IRFault {len(FAULTS)}; {len(TERMS)} terms "
          f"({n_b} single-frame arms, {n_o} outcome-keyed twins of the {len(mexto_names())} running-keyed module terms, "
          f"{sum(1 for n in NAMES if n.startswith('ir_mextvo_'))} mkv twins), {sum(len(v) for v in terms.values())} chars; mutation test: 3 hand edits refused")
    print("gen_stack_axes --self-test: " + ("OK" if not bad else f"FAILED ({len(bad)})"))
    return 0 if not bad else 1


def scratch(only: str | None, extra: list[Path]) -> int:
    terms = minted()
    items = [{"name": n, "kind": "def", "source": terms[c]} for c, n, _, _ in TERMS
             if only is None or re.search(only, n)]
    for p in extra:
        items += json.loads(p.read_text())
    SCRATCH.write_text(json.dumps(items, indent=1))
    print(f"gen_stack_axes: wrote {len(items)} candidates to {SCRATCH} (gitignored; a dev tool, not a gate)")
    return 0


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--emit", action="store_true")
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--print", dest="show")
    ap.add_argument("--list", action="store_true")
    ap.add_argument("--digests", action="store_true")
    ap.add_argument("--pin", action="store_true")
    ap.add_argument("--scratch", action="store_true")
    ap.add_argument("--only")
    ap.add_argument("--extra", action="append", default=[])
    args = ap.parse_args(argv)
    if args.list:
        for n in NAMES:
            print(n)
        return 0
    if args.show:
        print(by_name(args.show))
        return 0
    if args.scratch:
        return scratch(args.only, [Path(p) for p in args.extra])
    if args.digests:
        for k, v in sorted(digests(minted()).items()):
            print(f'    "{k}": "{v}",')
        return 0
    if args.pin:
        body = "PINNED_DIGESTS: dict = {\n" + "".join(
            f'    "{k}": "{v}",\n' for k, v in sorted(digests(minted()).items())) + "}"
        src = Path(__file__).read_text()
        src = re.sub(r"PINNED_DIGESTS: dict = \{.*?\n?\}", body, src, count=1, flags=re.S)
        Path(__file__).write_text(src)
        print(f"pinned {len(TERMS)} digests")
        return 0
    if args.self_test:
        return self_test()
    if args.emit:
        bad = structural(minted())
        if bad:
            for line in bad:
                print(line)
            return 1
        MINTED_RS.write_text(render_rust(minted()))
        print(f"gen_stack_axes: emitted {len(TERMS)} terms into {MINTED_RS}")
        return 0
    return check()


if __name__ == "__main__":
    sys.exit(main())
