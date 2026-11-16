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
NILF = "(@IRList.nil IRFrame)"

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
H0 = f"(IRMachine.mk (@IRList.cons IRFrame {F0} {NILF}) mem na)"
H1 = f"(IRMachine.mk (@IRList.cons IRFrame {F1} {NILF}) mem na)"


def hgoal(tpl: str) -> str:
    """`Eq IRConfig (H H1 ..) (ir_config_set_bot (H H0 ..) bdn)` for a template over {S}."""
    return f"@Eq IRConfig {G.at(tpl, H1)} (ir_config_set_bot {G.at(tpl, H0)} bdn)"


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
    return (f"@Eq.subst {VS} (fun (vs : IRList IRScalar) => {motive_body('vs')}) {r0} {r1} "
            f"(@Eq.symm {VS} {r1} {r0} (ir_resolve_bdst {HARGS} {x})) ({inner})")


# ---- definitions and their pins ------------------------------------------

DEFS_BDST = [
    ("SRC_FRAME_SET_DESTS", "ir_frame_set_dests",
     "def ir_frame_set_dests (f : IRFrame) (d : IRList Nat) : IRFrame := IRFrame.mk (ir_frame_func f) (ir_frame_block f) (ir_frame_pc f) (ir_frame_locals f) d",
     "ir_frame_set_dests: the frame with its dests field replaced. Built from the four PROJECTIONS rather than by IRFrame.rec, so every other field of the result reduces to the same field of `f` by one iota even at an ABSTRACT frame -- which is what lets the fetch, the operand reads and the locals of a rewritten frame be the same terms as the original's. " + D),
    ("SRC_FRAMES_SET_BOT", "ir_frames_set_bot",
     "def ir_frames_set_bot (fs : IRList IRFrame) (d : IRList Nat) : IRList IRFrame := @IRList.rec IRFrame (fun (_ : IRList IRFrame) => IRList IRFrame) (@IRList.nil IRFrame) (fun (x : IRFrame) (t : IRList IRFrame) (ih : IRList IRFrame) => @IRList.rec IRFrame (fun (_ : IRList IRFrame) => IRList IRFrame) (@IRList.cons IRFrame (ir_frame_set_dests x d) (@IRList.nil IRFrame)) (fun (_ : IRFrame) (_ : IRList IRFrame) (_ : IRList IRFrame) => @IRList.cons IRFrame x ih) t) fs",
     "ir_frames_set_bot: *** THE TRANSFORMATION THE AXIS IS ABOUT. *** Rewrite the dests of the LAST frame of a frame list -- the bottom frame, the one a single-frame run was entered at -- and leave every other frame, and the list's length, alone. The empty list is left empty. IRList.rec with an inner case on the tail: a frame whose tail is empty IS the bottom one. " + D),
    ("SRC_MACH_SET_BOT", "ir_mach_set_bot",
     "def ir_mach_set_bot (s : IRMachine) (d : IRList Nat) : IRMachine := @IRMachine.rec (fun (_ : IRMachine) => IRMachine) (fun (fs : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) => IRMachine.mk (ir_frames_set_bot fs d) mem na) s",
     "ir_mach_set_bot: ir_frames_set_bot on a machine's frame list; heap and counter unchanged. " + D),
    ("SRC_CONFIG_SET_BOT", "ir_config_set_bot",
     "def ir_config_set_bot (c : IRConfig) (d : IRList Nat) : IRConfig := @IRConfig.rec (fun (_ : IRConfig) => IRConfig) (fun (s : IRMachine) => IRConfig.running (ir_mach_set_bot s d)) (fun (o : IROutcome) => IRConfig.halted o) c",
     "ir_config_set_bot: the same on a configuration; the IDENTITY on a halted one -- an outcome carries no frame, so a run that halts has nothing left to rewrite. " + D),
]

PINS_BDST = [
    ("SRC_FRAMES_SET_BOT_NIL", "ir_frames_set_bot_nil", "(d : IRList Nat)",
     "(IRList IRFrame)", "(ir_frames_set_bot (@IRList.nil IRFrame) d)", "(@IRList.nil IRFrame)",
     "the empty list is left empty"),
    ("SRC_FRAMES_SET_BOT_ONE", "ir_frames_set_bot_one", "(x : IRFrame) (d : IRList Nat)",
     "(IRList IRFrame)", "(ir_frames_set_bot (@IRList.cons IRFrame x (@IRList.nil IRFrame)) d)",
     "(@IRList.cons IRFrame (ir_frame_set_dests x d) (@IRList.nil IRFrame))",
     "a single frame IS the bottom frame and is rewritten"),
    ("SRC_FRAMES_SET_BOT_TWO", "ir_frames_set_bot_two",
     "(x : IRFrame) (y : IRFrame) (t : IRList IRFrame) (d : IRList Nat)", "(IRList IRFrame)",
     "(ir_frames_set_bot (@IRList.cons IRFrame x (@IRList.cons IRFrame y t)) d)",
     "(@IRList.cons IRFrame x (ir_frames_set_bot (@IRList.cons IRFrame y t) d))",
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
    return G.defn(name, binders, f"@Eq {ty} {lhs} {rhs}", G.refl(ty, rhs))


# ---- C. head-only read ---------------------------------------------------


def c_resolve() -> str:
    mot = lambda v: f"@Eq {VS} (ir_resolve {H1} {v}) (ir_resolve {H0} {v})"
    body = (f"@IRList.rec Nat (fun (ids0 : IRList Nat) => {mot('ids0')}) "
            f"({G.refl(VS, '(@IRList.nil IRScalar)')}) "
            f"(fun (i : Nat) (ids2 : IRList Nat) (ih : {mot('ids2')}) => "
            f"ir_eq_cong {VS} {VS} (fun (vs : IRList IRScalar) => @IRList.cons IRScalar (ir_frame_get {F0} i) vs) "
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
    body = (f"@IRStepResult.rec (fun (r0 : IRStepResult) => {mot('r0')}) "
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
              "(ir_bind_params (ir_func_params g) vs (@IRList.nil IRBinding)) rs)")
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
    mot = lambda vs: f"@Eq IRConfig (ir_jump_func {H1} tgt {vs} {cur}) (ir_config_set_bot {G.at(tpl, H0)} bdn)"
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
    mot = lambda o: (f"@Eq IRConfig {G.switch_n_body('m', H1, o)} "
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
    mot = lambda o: (f"@Eq IRConfig {G.call_exec_body(H1, o)} "
                     f"(ir_config_set_bot {G.call_exec_body(H0, o)} bdn)")
    some_mot = lambda vs: (f"@Eq IRConfig (ir_push {H1} rs g {vs}) "
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
    inner_mot = lambda o: (f"@Eq IRConfig {G.alloca_exec_body(H1, o)} "
                           f"(ir_config_set_bot {G.alloca_exec_body(H0, o)} bdn)")
    inner = G.neutral_opt_rec("Nat", "o1", inner_mot, G.refl("IRConfig", G.tyerr("not_int")), ("k", "Nat"),
                              f"ir_alloca_k_bdst {HARGS} rs k", f"(ir_as_int (ir_frame_get {F0} i))",
                              mot("(@IROption.some Nat i)"))
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
        mot = lambda vs: f"@Eq IRConfig (ir_ret_vals {H1} {vs}) (ir_config_set_bot {G.at(tpl, H0)} bdn)"
        return resolve_subst_h(ids, mot, f"ir_ret_vals_bdst {HARGS} (ir_resolve {H0} {ids})")
    term, resolves = hify(rhs)
    if not resolves:
        return term
    (x,) = resolves
    assert term.startswith(f"ir_bind_result_bdst {HARGS} rs "), (ctor, term)
    evaluator = term[len(f"ir_bind_result_bdst {HARGS} rs "):]
    mot = lambda vs: (f"@Eq IRConfig (ir_bind_result {H1} rs {evaluator.replace(f'(ir_resolve {H0} {x})', vs)}) "
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
    layer = lambda step: (lambda o: f"@Eq IRConfig {step(H1, o)} (ir_config_set_bot {step(H0, o)} bdn)")
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
    inst_rec = f"@IRInst.rec (fun (i0 : IRInst) => {mot_i('i0')}) {' '.join(inst_minors)} i"
    node_rec = f"@IRNode.rec (fun (n0 : IRNode) => {mot_nd('n0')}) (fun (i : IRInst) (rs : IRList Nat) => {inst_rec}) nd"
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
                  f"@Eq IRConfig (ir_step m {H1}) (ir_config_set_bot (ir_step m {H0}) bdn)", f_rec)


# ---- the non-bottom head: stacking, reused -------------------------------
#
# A head `fh` over a nonempty tail `gb :: tb` is the ONE-frame machine [fh] stacked
# over that tail. E1's node-keyed arms state exactly that for every non-ret arm (at
# t = nil the stacked machine IS `fh :: rest`), so the non-ret minors are two
# applications of ir_stkn_arm_<ctor> -- at the rewritten tail and at the original --
# joined by ir_bdst_of_stk; the ret minor is ir_bdst_ret_cons. The tail vocabulary
# (fh gb tb dn) avoids every IRInst field name (ptrfromparts has a field `d`).

T0 = "(@IRList.cons IRFrame gb tb)"
T1 = f"(ir_frames_set_bot {T0} dn)"
C0 = f"(IRMachine.mk (@IRList.cons IRFrame fh {T0}) mem na)"
C1 = f"(IRMachine.mk (@IRList.cons IRFrame fh {T1}) mem na)"
C1F = f"(IRMachine.mk (@IRList.cons IRFrame fh {NILF}) mem na)"

SUPPORT = [
    ("SRC_FRAMES_APP_SET_BOT_PRE", "ir_frames_app_set_bot_pre",
     "def ir_frames_app_set_bot_pre (gb : IRFrame) (tb : IRList IRFrame) (dn : IRList Nat) (fs : IRList IRFrame) : forall (x : IRFrame), @Eq (IRList IRFrame) (ir_frames_set_bot (@IRList.cons IRFrame x (ir_frames_app fs (@IRList.cons IRFrame gb tb))) dn) (@IRList.cons IRFrame x (ir_frames_app fs (ir_frames_set_bot (@IRList.cons IRFrame gb tb) dn))) := @IRList.rec IRFrame (fun (fs0 : IRList IRFrame) => forall (x : IRFrame), @Eq (IRList IRFrame) (ir_frames_set_bot (@IRList.cons IRFrame x (ir_frames_app fs0 (@IRList.cons IRFrame gb tb))) dn) (@IRList.cons IRFrame x (ir_frames_app fs0 (ir_frames_set_bot (@IRList.cons IRFrame gb tb) dn)))) (fun (x : IRFrame) => @Eq.refl (IRList IRFrame) (@IRList.cons IRFrame x (ir_frames_set_bot (@IRList.cons IRFrame gb tb) dn))) (fun (y : IRFrame) (fs2 : IRList IRFrame) (ih : forall (x : IRFrame), @Eq (IRList IRFrame) (ir_frames_set_bot (@IRList.cons IRFrame x (ir_frames_app fs2 (@IRList.cons IRFrame gb tb))) dn) (@IRList.cons IRFrame x (ir_frames_app fs2 (ir_frames_set_bot (@IRList.cons IRFrame gb tb) dn)))) => fun (x : IRFrame) => ir_eq_cong (IRList IRFrame) (IRList IRFrame) (fun (l : IRList IRFrame) => @IRList.cons IRFrame x l) (ir_frames_set_bot (@IRList.cons IRFrame y (ir_frames_app fs2 (@IRList.cons IRFrame gb tb))) dn) (@IRList.cons IRFrame y (ir_frames_app fs2 (ir_frames_set_bot (@IRList.cons IRFrame gb tb) dn))) (ih y)) fs",
     "ir_frames_app_set_bot_pre: rewriting the bottom dests of `x :: fs ++ (gb :: tb)` rewrites them in the appended tail -- the frames stacked above a nonempty tail are never the bottom ones. IRList.rec on fs generalised over the head x, because the bottom-frame case split in ir_frames_set_bot is on the TAIL and needs the tail to be a visible cons at every stage; the cons case is ir_eq_cong of IRList.cons x over the induction hypothesis at the next head. " + D),
    ("SRC_FRAMES_APP_SET_BOT", "ir_frames_app_set_bot",
     "def ir_frames_app_set_bot (gb : IRFrame) (tb : IRList IRFrame) (dn : IRList Nat) (fs : IRList IRFrame) : @Eq (IRList IRFrame) (ir_frames_app fs (ir_frames_set_bot (@IRList.cons IRFrame gb tb) dn)) (ir_frames_set_bot (ir_frames_app fs (@IRList.cons IRFrame gb tb)) dn) := @IRList.rec IRFrame (fun (fs0 : IRList IRFrame) => @Eq (IRList IRFrame) (ir_frames_app fs0 (ir_frames_set_bot (@IRList.cons IRFrame gb tb) dn)) (ir_frames_set_bot (ir_frames_app fs0 (@IRList.cons IRFrame gb tb)) dn)) (@Eq.refl (IRList IRFrame) (ir_frames_set_bot (@IRList.cons IRFrame gb tb) dn)) (fun (x : IRFrame) (fs2 : IRList IRFrame) (_ : @Eq (IRList IRFrame) (ir_frames_app fs2 (ir_frames_set_bot (@IRList.cons IRFrame gb tb) dn)) (ir_frames_set_bot (ir_frames_app fs2 (@IRList.cons IRFrame gb tb)) dn)) => @Eq.symm (IRList IRFrame) (ir_frames_set_bot (@IRList.cons IRFrame x (ir_frames_app fs2 (@IRList.cons IRFrame gb tb))) dn) (@IRList.cons IRFrame x (ir_frames_app fs2 (ir_frames_set_bot (@IRList.cons IRFrame gb tb) dn))) (ir_frames_app_set_bot_pre gb tb dn fs2 x)) fs",
     "ir_frames_app_set_bot: stacking commutes with rewriting the bottom dests of a NONEMPTY tail -- `fs ++ set_bot (gb :: tb) = set_bot (fs ++ (gb :: tb))` for every frame list fs. Case on fs: empty is Eq.refl, a cons is ir_frames_app_set_bot_pre. The tail must be nonempty: over an EMPTY tail the bottom frame would be the last of fs, which stacking does not touch. " + D),
    ("SRC_BDST_STACK_CONS", "ir_bdst_stack_cons",
     "def ir_bdst_stack_cons (c : IRConfig) (gb : IRFrame) (tb : IRList IRFrame) (dn : IRList Nat) : @Eq IRConfig (ir_config_stack c (ir_frames_set_bot (@IRList.cons IRFrame gb tb) dn)) (ir_config_set_bot (ir_config_stack c (@IRList.cons IRFrame gb tb)) dn) := @IRConfig.rec (fun (c0 : IRConfig) => @Eq IRConfig (ir_config_stack c0 (ir_frames_set_bot (@IRList.cons IRFrame gb tb) dn)) (ir_config_set_bot (ir_config_stack c0 (@IRList.cons IRFrame gb tb)) dn)) (fun (s : IRMachine) => @IRMachine.rec (fun (s0 : IRMachine) => @Eq IRConfig (ir_config_stack (IRConfig.running s0) (ir_frames_set_bot (@IRList.cons IRFrame gb tb) dn)) (ir_config_set_bot (ir_config_stack (IRConfig.running s0) (@IRList.cons IRFrame gb tb)) dn)) (fun (fs : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) => ir_eq_cong (IRList IRFrame) IRConfig (fun (l : IRList IRFrame) => IRConfig.running (IRMachine.mk l mem na)) (ir_frames_app fs (ir_frames_set_bot (@IRList.cons IRFrame gb tb) dn)) (ir_frames_set_bot (ir_frames_app fs (@IRList.cons IRFrame gb tb)) dn) (ir_frames_app_set_bot gb tb dn fs)) s) (fun (o : IROutcome) => @Eq.refl IRConfig (IRConfig.halted o)) c",
     "ir_bdst_stack_cons: the configuration-level form -- stacking a configuration over the REWRITTEN tail is rewriting the bottom dests of it stacked over the original tail, for every configuration (a halted one on both sides by Eq.refl). " + D),
    ("SRC_BDST_OF_STK", "ir_bdst_of_stk",
     "def ir_bdst_of_stk (x : IRConfig) (l0 : IRConfig) (l1 : IRConfig) (gb : IRFrame) (tb : IRList IRFrame) (dn : IRList Nat) (e1 : @Eq IRConfig l1 (ir_config_stack x (ir_frames_set_bot (@IRList.cons IRFrame gb tb) dn))) (e0 : @Eq IRConfig l0 (ir_config_stack x (@IRList.cons IRFrame gb tb))) : @Eq IRConfig l1 (ir_config_set_bot l0 dn) := @Eq.trans IRConfig l1 (ir_config_stack x (ir_frames_set_bot (@IRList.cons IRFrame gb tb) dn)) (ir_config_set_bot l0 dn) e1 (@Eq.trans IRConfig (ir_config_stack x (ir_frames_set_bot (@IRList.cons IRFrame gb tb) dn)) (ir_config_set_bot (ir_config_stack x (@IRList.cons IRFrame gb tb)) dn) (ir_config_set_bot l0 dn) (ir_bdst_stack_cons x gb tb dn) (ir_eq_cong IRConfig IRConfig (fun (c1 : IRConfig) => ir_config_set_bot c1 dn) (ir_config_stack x (@IRList.cons IRFrame gb tb)) l0 (@Eq.symm IRConfig l0 (ir_config_stack x (@IRList.cons IRFrame gb tb)) e0)))",
     "ir_bdst_of_stk: the joint every non-ret minor of ir_bdst_step_cons goes through -- if the rewritten-tail step and the original step are the SAME one-frame step x stacked over the two tails, the first is the second with its bottom dests rewritten. Two Eq.trans and ir_bdst_stack_cons. " + D),
    ("SRC_BDST_RET_TO", "ir_bdst_ret_to",
     "def ir_bdst_ret_to (ds : IRList Nat) (dn : IRList Nat) (mem : IRList IRMemSlot) (na : Nat) (vs : IRList IRScalar) (tb : IRList IRFrame) : forall (gb : IRFrame), @Eq IRConfig (ir_ret_to ds (ir_frames_set_bot (@IRList.cons IRFrame gb tb) dn) mem na vs) (ir_config_set_bot (ir_ret_to ds (@IRList.cons IRFrame gb tb) mem na vs) dn) := @IRList.rec IRFrame (fun (t0 : IRList IRFrame) => forall (gb : IRFrame), @Eq IRConfig (ir_ret_to ds (ir_frames_set_bot (@IRList.cons IRFrame gb t0) dn) mem na vs) (ir_config_set_bot (ir_ret_to ds (@IRList.cons IRFrame gb t0) mem na vs) dn)) (fun (gb : IRFrame) => @IRFrame.rec (fun (g0 : IRFrame) => @Eq IRConfig (ir_ret_to ds (ir_frames_set_bot (@IRList.cons IRFrame g0 (@IRList.nil IRFrame)) dn) mem na vs) (ir_config_set_bot (ir_ret_to ds (@IRList.cons IRFrame g0 (@IRList.nil IRFrame)) mem na vs) dn)) (fun (fi : Nat) (bl : Nat) (pc : Nat) (loc : IRList IRBinding) (e : IRList Nat) => @Eq.refl IRConfig (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame (IRFrame.mk fi bl pc (ir_bind_params ds vs loc) dn) (@IRList.nil IRFrame)) mem na))) gb) (fun (g2 : IRFrame) (t3 : IRList IRFrame) (_ : forall (gb : IRFrame), @Eq IRConfig (ir_ret_to ds (ir_frames_set_bot (@IRList.cons IRFrame gb t3) dn) mem na vs) (ir_config_set_bot (ir_ret_to ds (@IRList.cons IRFrame gb t3) mem na vs) dn)) (gb : IRFrame) => @Eq.refl IRConfig (IRConfig.running (IRMachine.mk (@IRList.cons IRFrame (ir_frame_set_many gb ds vs) (ir_frames_set_bot (@IRList.cons IRFrame g2 t3) dn)) mem na))) tb",
     "ir_bdst_ret_to: a return into a caller commutes with rewriting the bottom dests beneath it. IRList.rec on the caller's tail: if the caller IS the bottom frame, the return writes the values into its locals and keeps its dests, so rewriting before or after is the same frame -- IRFrame.rec on the caller, Eq.refl at the constructor (ir_frame_set_many and ir_frame_set_dests touch different fields); if the caller has a caller of its own, the bottom frame is further down and both sides re-cons it verbatim (Eq.refl). " + D),
    ("SRC_BDST_RET_CONS", "ir_bdst_ret_cons",
     f"def ir_bdst_ret_cons (fh : IRFrame) (gb : IRFrame) (tb : IRList IRFrame) (dn : IRList Nat) (mem : IRList IRMemSlot) (na : Nat) (ids : IRList Nat) : @Eq IRConfig (ir_ret_to (ir_frame_dests fh) {T1} mem na (ir_resolve {C1} ids)) (ir_config_set_bot (ir_ret_to (ir_frame_dests fh) {T0} mem na (ir_resolve {C0} ids)) dn) := @Eq.subst {VS} (fun (vs : IRList IRScalar) => @Eq IRConfig (ir_ret_to (ir_frame_dests fh) {T1} mem na vs) (ir_config_set_bot (ir_ret_to (ir_frame_dests fh) {T0} mem na (ir_resolve {C0} ids)) dn)) (ir_resolve {C1F} ids) (ir_resolve {C1} ids) (@Eq.symm {VS} (ir_resolve {C1} ids) (ir_resolve {C1F} ids) (ir_resolve_stack fh {NILF} {T1} mem na ids)) (@Eq.subst {VS} (fun (vs : IRList IRScalar) => @Eq IRConfig (ir_ret_to (ir_frame_dests fh) {T1} mem na (ir_resolve {C1F} ids)) (ir_config_set_bot (ir_ret_to (ir_frame_dests fh) {T0} mem na vs) dn)) (ir_resolve {C1F} ids) (ir_resolve {C0} ids) (@Eq.symm {VS} (ir_resolve {C0} ids) (ir_resolve {C1F} ids) (ir_resolve_stack fh {NILF} {T0} mem na ids)) (ir_bdst_ret_to (ir_frame_dests fh) dn mem na (ir_resolve {C1F} ids) tb gb))",
     "ir_bdst_ret_cons: the ret arm of a NON-bottom head -- the return into `gb :: tb` with its bottom dests rewritten is the rewritten return. The returned values are resolved from the head frame alone, so both resolutions are transported to the one-frame machine's through ir_resolve_stack at an empty tail (one Eq.subst each), then ir_bdst_ret_to. " + D),
]


def g_step_cons() -> str:
    step_f = lambda S, o: f"(ir_step_f m {S} (ir_frame_block fh) (ir_frame_pc fh) {o})"
    step_b = lambda S, o: f"(ir_step_b m {S} (ir_frame_pc fh) {o})"
    step_n = lambda S, o: f"(ir_step_n m {S} {o})"
    exec_node = lambda S, n0: f"(ir_exec_node m {n0} {S})"
    exec_i = lambda S, i0: f"(ir_exec m {i0} rs {S})"
    layer = lambda step: (lambda o: f"@Eq IRConfig {step(C1, o)} (ir_config_set_bot {step(C0, o)} dn)")
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
    inst_rec = f"@IRInst.rec (fun (i0 : IRInst) => {mot_i('i0')}) {' '.join(inst_minors)} i"
    node_rec = f"@IRNode.rec (fun (n0 : IRNode) => {mot_nd('n0')}) (fun (i : IRInst) (rs : IRList Nat) => {inst_rec}) nd"
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
                  f"@Eq IRConfig (ir_step m {C1}) (ir_config_set_bot (ir_step m {C0}) dn)", f_rec)


# ==========================================================================
# AXIS 2 -- the module axis keyed on the OUTCOME class (the ir_mexto family)
# ==========================================================================

FAULTS = [c for c, _ in G.ctors("IRFault")]
OUTCOMES = [c for c, _ in G.ctors("IROutcome")]
assert OUTCOMES == ["ret", "ub", "type_error", "unmodelled", "stuck", "fuel_out"], OUTCOMES
assert "no_func" in FAULTS and "no_global" in FAULTS


def fault_is(name: str, target: str) -> str:
    minors = " ".join("Bool.true" if c == target else "Bool.false" for c in FAULTS)
    return G.defn(name, "(f : IRFault)", "Bool", f"@IRFault.rec (fun (_ : IRFault) => Bool) {minors} f")


NOT_ = "@Bool.rec (fun (_ : Bool) => Bool) Bool.true Bool.false"

DEFS_MEXTO = [
    ("SRC_FAULT_IS_NO_FUNC", "ir_fault_is_no_func", lambda: fault_is("ir_fault_is_no_func", "no_func"),
     f"ir_fault_is_no_func: Bool test for the `no_func` fault -- one IRFault.rec, one minor per constructor READ OFF the inductive declaration ({len(FAULTS)} today), true only at no_func. A new IRFault constructor re-mints it. " + D),
    ("SRC_FAULT_IS_NO_GLOBAL", "ir_fault_is_no_global", lambda: fault_is("ir_fault_is_no_global", "no_global"),
     "ir_fault_is_no_global: the same for the `no_global` fault -- one IRFault.rec with its minors read off the inductive declaration, true only at no_global, the fault a global-address lookup that misses produces. " + D),
    ("SRC_MEXT_OK", "ir_mext_ok", lambda: G.defn(
        "ir_mext_ok", "(c : IRConfig)", "Bool",
        "@IRConfig.rec (fun (_ : IRConfig) => Bool) (fun (_ : IRMachine) => Bool.true) "
        "(fun (o : IROutcome) => @IROutcome.rec (fun (_ : IROutcome) => Bool) "
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
     "def ir_mext_ok_back (m : IRModule) (k : Nat) (c : IRConfig) (h : @Eq Bool (ir_mext_ok (ir_steps k m c)) Bool.true) : @Eq Bool (ir_mext_ok c) Bool.true := @IRConfig.rec (fun (c0 : IRConfig) => @Eq Bool (ir_mext_ok (ir_steps k m c0)) Bool.true -> @Eq Bool (ir_mext_ok c0) Bool.true) (fun (s : IRMachine) (_ : @Eq Bool (ir_mext_ok (ir_steps k m (IRConfig.running s))) Bool.true) => @Eq.refl Bool Bool.true) (fun (o : IROutcome) (h0 : @Eq Bool (ir_mext_ok (ir_steps k m (IRConfig.halted o))) Bool.true) => @Eq.subst IRConfig (fun (c1 : IRConfig) => @Eq Bool (ir_mext_ok c1) Bool.true) (ir_steps k m (IRConfig.halted o)) (IRConfig.halted o) (ir_steps_halted m o k) h0) c h",
     "ir_mext_ok_back: the premise is BACKWARD-closed along a run -- if the configuration k steps later passes, so does this one (a running configuration passes outright; a halted one IS its own k-step successor, ir_steps_halted). The twin of ir_stk_running_back, and what ir_mexto_steps hands the one-step lemma. " + D),
    ("SRC_MEXT_OK_OF_RUNNING", "ir_mext_ok_of_running",
     "def ir_mext_ok_of_running (c : IRConfig) (h : @Eq Bool (ir_stk_running c) Bool.true) : @Eq Bool (ir_mext_ok c) Bool.true := @IRConfig.rec (fun (c0 : IRConfig) => @Eq Bool (ir_stk_running c0) Bool.true -> @Eq Bool (ir_mext_ok c0) Bool.true) (fun (s : IRMachine) (_ : @Eq Bool (ir_stk_running (IRConfig.running s)) Bool.true) => @Eq.refl Bool Bool.true) (fun (o : IROutcome) (h0 : @Eq Bool (ir_stk_running (IRConfig.halted o)) Bool.true) => ir_bool_false_ne_true (@Eq Bool (ir_mext_ok (IRConfig.halted o)) Bool.true) h0) c h",
     "ir_mext_ok_of_running: the running premise implies the new one -- so the running-keyed module axis (ir_mext_step, ir_mext_steps, ir_mext_run) is the special case of the outcome-keyed twin. " + D),
    ("SRC_MEXT_OK_RET_TO", "ir_mext_ok_ret_to",
     "def ir_mext_ok_ret_to (ds : IRList Nat) (mem : IRList IRMemSlot) (na : Nat) (vs : IRList IRScalar) (r : IRList IRFrame) : @Eq Bool (ir_mext_ok (ir_ret_to ds r mem na vs)) Bool.true := @IRList.rec IRFrame (fun (r0 : IRList IRFrame) => @Eq Bool (ir_mext_ok (ir_ret_to ds r0 mem na vs)) Bool.true) (@Eq.refl Bool Bool.true) (fun (g : IRFrame) (r2 : IRList IRFrame) (_ : @Eq Bool (ir_mext_ok (ir_ret_to ds r2 mem na vs)) Bool.true) => @Eq.refl Bool Bool.true) r",
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
    back = (f"@Eq.subst IRConfig (fun (c1 : IRConfig) => @Eq Bool (ir_mext_ok c1) Bool.true) {ho} {s0} "
            f"(@Eq.symm IRConfig {s0} {ho} hh) hok")
    body = (f"@Eq.trans IRConfig {s1} {s0} {ho} "
            f"(@Eq.symm IRConfig {s0} {s1} (ir_mextvo_steps {G.MVARGS} hf hg henc hlen k c ({back}))) hh")
    binders = (f"{G.MVBLOCK} {G.PREMISE['hf']} {G.PREMISE['hg']} {G.PREMISE['he']} {G.PREMISE['hl']} "
               f"(k : Nat) (c : IRConfig) (o : IROutcome) (hh : @Eq IRConfig {s0} {ho}) "
               f"(hok : @Eq Bool (ir_mext_ok {ho}) Bool.true)")
    return G.defn("ir_mextvo_run", binders, f"@Eq IRConfig {s1} {ho}", body)


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
        "@IRConfig.rec (fun (_ : IRConfig) => Bool) (fun (_ : IRMachine) => Bool.false) "
        "(fun (o : IROutcome) => @IROutcome.rec (fun (_ : IROutcome) => Bool) (fun (_ : IRList IRScalar) => Bool.true) "
        "(fun (_ : IRFault) => Bool.false) (fun (_ : IRFault) => Bool.false) (fun (_ : IRFault) => Bool.false) "
        "(fun (_ : IRFault) => Bool.false) Bool.false o) c"),
     "ir_is_ret_halt: Bool test for a configuration that has HALTED WITH A RETURN -- false on a running configuration and on every other outcome. What a bottom ret's step produces (ir_stk_botret_ret). " + D),
    ("SRC_HALT_MID", "ir_halt_mid", lambda: G.defn(
        "ir_halt_mid", "(c : IRConfig)", "Bool",
        "@IRConfig.rec (fun (_ : IRConfig) => Bool) (fun (_ : IRMachine) => Bool.false) "
        "(fun (o : IROutcome) => @IROutcome.rec (fun (_ : IROutcome) => Bool) (fun (_ : IRList IRScalar) => Bool.false) "
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
    yes = lambda b: f"@Eq Bool {b} Bool.true"
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
        none = f"(@IROption.none {param})"
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
    inst_rec = f"@IRInst.rec (fun (i0 : IRInst) => {mot_i('i0')}) {' '.join(inst_minors)} i"
    node_rec = f"@IRNode.rec (fun (n0 : IRNode) => {mot_nd('n0')}) (fun (i : IRInst) (rs : IRList Nat) => {inst_rec}) nd"
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
    t_rec = f"@IRList.rec IRFrame (fun (t0 : IRList IRFrame) => {t_mot('t0')}) ({f_rec}) {t_cons} t"
    step_nil = "(ir_step m " + mk(G.NIL_F) + ")"
    nil_minor = (f"(fun (h : {yes('(ir_stk_botret m ' + mk(G.NIL_F) + ')')}) => "
                 f"ir_bool_false_ne_true ({goal(step_nil)}) h)")
    cons_minor = f"(fun (f : IRFrame) (t : IRList IRFrame) (_ih : {mot_fs('t')}) => {t_rec})"
    list_rec = f"@IRList.rec IRFrame (fun (fs0 : IRList IRFrame) => {mot_fs('fs0')}) {nil_minor} {cons_minor} fs"
    body = (f"@IRMachine.rec (fun (s0 : IRMachine) => {mot_s('s0')}) "
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
TERMS += [(c, n, (lambda n=n, b=b, l=l, r=r: G.defn(n, b, f"@Eq Bool {l} {r}", G.refl("Bool", r))),
           f"{n}: vacuity pin -- {why}. Eq.refl, so ir_mext_ok is held to this spelling. {D}")
          for c, n, b, l, r, why in PINS_MEXTO]
TERMS += [(c, n, _fixed(s), d) for c, n, s, d in SUPPORT_MEXTO]
TERMS += [(c, n, g, d) for c, n, g, d in DEFS_TRI]
TERMS += [(c, n, (lambda n=n, b=b, l=l, r=r: G.defn(n, b, f"@Eq Bool {l} {r}", G.refl("Bool", r))),
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
    "SRC_ADVANCE_BDST": "da9749c30d54a0b6de1de3bbcbc478717d0ad5be73abdbecc53c7ba6370bc6d6",
    "SRC_ADVANCE_SET_MEM_BDST": "0add9bdd45110e016e69495e205c59ea656b917ec5b6fee19b1022623dd2acf1",
    "SRC_ALLOCA_EXEC_BDST": "bf7ab4d73685d4a0a20b7c2ba0d73e70c0fb3944a58d6ff4a42f2de24f3879a9",
    "SRC_ALLOCA_K_BDST": "810dfcbede56ed2f648ece58c5f37f19237a975051f57aefbe3edc6464db76ff",
    "SRC_ASSERT_B_BDST": "a2f4b6647beec896ae319025ca44a91604d3d2f4f7e5428ffc6a6f1455bc8279",
    "SRC_ASSERT_EXEC_BDST": "d336a0f8e226fb1827058058ba3e8cb4294e105e2f273c84db520bc2d5c07537",
    "SRC_BDST_ARM_ALLOCA": "c4c0e11cf03a5706f6d3fe53b881d46a88aedb387013a02e67be64c8130e9632",
    "SRC_BDST_ARM_ASSERT": "c511785c45415d2013cf8bfb9a46daa8a6987f14deeb414c04a3c60c6c4530e1",
    "SRC_BDST_ARM_ATOMIC_FETCH_ADD_RELAXED_U64_SEQ": "43d2c4be823660a345c8a775731026cb023fc25f910ae245ec13913b163b523e",
    "SRC_BDST_ARM_ATOMIC_FETCH_ADD_RELAXED_USIZE_SEQ": "de0de8a37e7e421afd9057118b0c1cb24270a6568e2c548a478b0250d739a2d0",
    "SRC_BDST_ARM_BINOP": "342cf966a34a37be779f8dcafca37fee548b22fb32cd524d0e0310462a61204b",
    "SRC_BDST_ARM_BORROW": "d3332517ba7cd2d2b162d74163b73faebd4fe5cd727e44509a5b1cf29e492ae3",
    "SRC_BDST_ARM_BR": "1a7bc5458a2dc3247ea63c76ef49a0ac8f172f38533700d4d46e0edb894058ba",
    "SRC_BDST_ARM_CALL": "2236b15c14012675af7c334dab51c3964b7196f8d8968de75ea56409981a383b",
    "SRC_BDST_ARM_CALLINDIRECT": "64d21b333d2405808fe94244f2418720d9bc2747989f0fd734a266a609a44aae",
    "SRC_BDST_ARM_CAST": "f8082df6a321b0e257b3610514ffaa3d1e8792646f9ac5e523ed1c5185cd04b4",
    "SRC_BDST_ARM_CONDBR": "acefd247d79c61f536b03cb69dc1e158aae6298490e7df43335fd83191e57000",
    "SRC_BDST_ARM_CONST_": "d823fef902cbf621dede401b20fb1f422d355534f4dea7bfecc3983f0dfe0d38",
    "SRC_BDST_ARM_COPY": "d5182fad14212876ff2c1f9b532b8ca1ba65c0f1347f8a0d6987428dc9b196cc",
    "SRC_BDST_ARM_EXTRACTELEMENT": "837821c1c6740dbbd578069e3cd7abf2c0bb35d1309875983d54811333501d9f",
    "SRC_BDST_ARM_EXTRACTFIELD": "76187c9f1199fad7b74b8b0520530d7403d5a867b498b6ecc698f194826aacf1",
    "SRC_BDST_ARM_FCMP": "838af4ed99590196cafa85bfdc80a21d2abb59b92c60a72ca2239131328f6bfe",
    "SRC_BDST_ARM_GEP": "0d7820e4a1077024b0434238b87b8302ae1df32d0b6bb63cb3240cbbea6d2c0d",
    "SRC_BDST_ARM_GLOBALADDR": "f3e5410700ad4ce502ee297c9a2a0154d6a395c30b61b9ebe8a0a11c3683bf82",
    "SRC_BDST_ARM_ICMP": "ef9452335945d4300c07ff452a44d2a99989e34d8bfc9aed9616fd3d26e39587",
    "SRC_BDST_ARM_INSERTFIELD": "b13a385a473b920b5f3f9f3bc5d37a472bbf134ede2be046d3d0a43123e55b18",
    "SRC_BDST_ARM_LOAD": "08bb6f7f872a8ba48c4d9ac4416617c083daa3c88e329774179d6506844fa88e",
    "SRC_BDST_ARM_OVERFLOW": "549fe3f07d8e0377bc3c89a95a51485306e3c5c2be70f00bc567ab73a8f60a42",
    "SRC_BDST_ARM_PTRDATA": "baa464aa78729eff72f6c7543b350e36ba590ca9371478bed187f1dfb7dc0720",
    "SRC_BDST_ARM_PTRFROMPARTS": "9aabb87741889dacaa1ee711d4f58f6d52dc631e6d73f2fc378691f42a5e28e3",
    "SRC_BDST_ARM_PTRMETADATA": "9856a54495c64ca806c54c8c2ed5cb81ff9d05797114c05bf817a3ad406b9b16",
    "SRC_BDST_ARM_RELEASE": "7173efc9bc809334bfa214399950aa0be5d3a01d5163d83dd76a2528648377a0",
    "SRC_BDST_ARM_RET": "a4c12539bb7b7f755d2564b5016b22f8d6ed7360dc0f1f45ce3f5312e5cf9b73",
    "SRC_BDST_ARM_SELECT": "5e288a7e4bc6303f87a47a47f12755b4661cc9e492f853781d0bea19b2bd9b05",
    "SRC_BDST_ARM_STORE": "1952abe77177d1afd2649fe61e7d28110467b7bd050d7739e6962caed347b002",
    "SRC_BDST_ARM_SWITCH": "cc22184d3b38b2f6190ec3392c70aeb87f3368bbfea09facec6c0afc4a209d68",
    "SRC_BDST_ARM_UNDEF": "5ba06699f2404b9a3108b8d1e8921572cc556450e8bd5fa56ee83093a18886a8",
    "SRC_BDST_ARM_UNOP": "be6ae43201d17ea6f550649c96af73c5052a5cbdc4f08a64869901557f711ee9",
    "SRC_BDST_ARM_UNREACHABLE": "fd8fc772b237a463db1d102594ae2cc00bb5f1b729ff2b5c6622017be6608556",
    "SRC_BDST_OF_STK": "86904f48cb5365c4624a6fb0b92e1a1b7fab783cdc093f170f19d005c4fd9cc7",
    "SRC_BDST_RET_CONS": "e7fc1bd879cff1bad41a6406ed64c48f5c69fec6f8b280929531a7d99cee7bf1",
    "SRC_BDST_RET_TO": "f273f5007f54d70b665deb980a597541f5e39126d011ab290405e21eaa932579",
    "SRC_BDST_STACK_CONS": "3a5aa851b103393b5b9a397d7477fb078a4308e2a110ec5d489b7a4930d4664f",
    "SRC_BDST_STEP1": "afe9c3d5230b22e14b76b0f87519a14fbed071dc09f8e88e5de09caf5633ff9d",
    "SRC_BDST_STEP_CONS": "01f4d401cb1b6687b4adb25b3598113841dafc42fa9029bb2e80a63f59f3ceae",
    "SRC_BIND2_BDST": "c1f5d42ab76f3fed1228af033b8921bf7fcf076f0c4ebf6b35e7e1399317c6ea",
    "SRC_BIND_BDST": "82ebb0304fbf3f0d9ce849f17fe1d60890c2fc400e100709cf078b6a04c2108f",
    "SRC_BIND_RESULT_BDST": "6771e143a368d494b62d646b020ede2f818f3b712a7770b9448530d37a7cf6dd",
    "SRC_CALLIND_EXEC_BDST": "479abd19d6352c8efdc7dd8ab7304bd27021da573fbf0d32a8b8b97359418831",
    "SRC_CALL_EXEC_BDST": "c90fa2079a2d36a77407bbee68f04e9f923352b33a38a5f19e8fe5351e96f52e",
    "SRC_CONDBR_B_BDST": "ff9112f6cb43e4bc8fbe9d4e41a30784adc9953800e7694a9b389f3d0e46beaf",
    "SRC_CONDBR_EXEC_BDST": "8d2ca4ca07a44905a43db44397d1516e5ce9096897afff45a8731509e9ea3b9f",
    "SRC_CONFIG_SET_BOT": "32b7646ed6404ca548cd460b6db236126071f93a96e39a3e9fbba93eb9844868",
    "SRC_CONFIG_SET_BOT_HALTED": "431f245c65b7e3e6cab1532799454e4efa11bf1558209356c3cd4ad55dd5c81a",
    "SRC_FAULT_IS_NO_FRAME": "d6ce9e453d1a6a8159957fb77121b06a78e3ba43419de4e9a6756cb72077ace0",
    "SRC_FAULT_IS_NO_FUNC": "8dbe64df4234f17498b5ad836246005c367c5931a12fc34002e9dccd0f607e50",
    "SRC_FAULT_IS_NO_GLOBAL": "e4fa85948b7be3cc7cfacaabcfcdd6e0aa2db278dc5f86b86b8178390412a834",
    "SRC_FRAMES_APP_SET_BOT": "96abe8ee48d9e14f35eadd5b34b9b8ca6d45a51c5d12e3cf521d19801df710bf",
    "SRC_FRAMES_APP_SET_BOT_PRE": "f2a362d4432522ffbec5ff30a2d514f440ffc02447665e8f9fc9c1bcebe189ca",
    "SRC_FRAMES_SET_BOT": "eed507fea606b35965a6abda0e6583460ce91481c2c92c5cede0f75c0db893b0",
    "SRC_FRAMES_SET_BOT_NIL": "16ebf8a23b8fcb64908244287a2996ce229e274c0b1d0e83d393e4113526dd6e",
    "SRC_FRAMES_SET_BOT_ONE": "743ca17864363151f021407b1db70b9e85383de7e7fa9c9421ad0d4bc249d9e5",
    "SRC_FRAMES_SET_BOT_TWO": "464231da972c0eb0d6686d28a789c6a61cdcecc7c249305392ccf360b872832e",
    "SRC_FRAME_DESTS_SET_DESTS": "985768c804088bbd4da965a1b7ff9ba6ebd9db6c3b75d0751655c8484f98f0e5",
    "SRC_FRAME_FUNC_SET_DESTS": "c168ac21ca4fd1d2b766f80e8b4178f15a60d75cbcf40d58f30d3c3a36ccebfc",
    "SRC_FRAME_SET_DESTS": "97a9bb48a237ce563c7b6d91d3005617f41f995e61a27d55db45b9a3df7e407a",
    "SRC_FRAME_SET_DESTS_MK": "3e6db984092d597c7f9e7c0562727bbfb8024d599d13f6f01ee737384eb64d14",
    "SRC_GOTO_BDST": "2dcbd225782226e2aea05d14c8a90975a89a973f1bf67cd7f9031e14454077a8",
    "SRC_HALT_MID": "8bdd5a9aa9604ce277871aab5a7960e1a143d9bc01d4a00237f355ef6df98d4f",
    "SRC_HALT_MID_ASSERT": "2d62a383851441670de7fd87463ef9abcd0c7799553acfe7e4f68f7779b676cc",
    "SRC_HALT_MID_NO_FRAME": "de353478ebb951e4c1fb0aa02370f2ed818330b51ea18a0428d053fa77a76c82",
    "SRC_HALT_MID_NO_FUNC": "2742b4a083e69af6fc94e4484ad6b80df521e72bcd2fd46a31d21843cdf9ced3",
    "SRC_HALT_MID_RET": "0bca622a0fec2d051ba7f1c1f66c294b9118c8d5484815f6520fc494a68203b5",
    "SRC_HALT_MID_RUNNING": "121616ce43a14b9b4b4af7755e9274d821bda7f63f45c846980b3a0344efc598",
    "SRC_IS_RET_HALT": "b3d5ee9da9f541394fbe335f880ffea5359a2eade5ddd3106aedd3ac3c182340",
    "SRC_IS_RET_HALT_ASSERT": "b743fa065f45559ad2155723bb42b99f7feff959957929a7d2288b12f82fc25d",
    "SRC_IS_RET_HALT_RET": "f17812b90366234adf12414d7d645bd682543d2b061fd5270add31e367042c6b",
    "SRC_JUMP_BDST": "51aea5410514920fa4aea50775c335753bb626ffa8472a9a6cf785d7637439dd",
    "SRC_JUMP_BLOCK_BDST": "270f05e0b4c35c757e616fa06bd9e5853bcfacfe762be81cff909bc92583b2e4",
    "SRC_JUMP_FUNC_BDST": "bd3f05e392362152b9b3ab34aed35d8ca33d162a7e77777a89adaf8db3a721d4",
    "SRC_MACH_SET_BOT": "46bd933f8c3ff7fa1bd4f9bbcb60a14e30c71d7fded4247067c93a5acd6d6e75",
    "SRC_MEXTO_ARM_ALLOCA": "0a2e89b99beedab9739b4d8100f5c46f7e2508ae816cec8009fda79589b49aa6",
    "SRC_MEXTO_ARM_ASSERT": "709c5f796b1501e13ea902ec63777f9f4bc08d3d5f2873157fe19db35de84080",
    "SRC_MEXTO_ARM_ATOMIC_FETCH_ADD_RELAXED_U64_SEQ": "d754e428aa9d544d52dd5996327f2f1f04de1000901198a6fc7a1a59d70defa7",
    "SRC_MEXTO_ARM_ATOMIC_FETCH_ADD_RELAXED_USIZE_SEQ": "538da0aab2669581f49f39f19f83387425c0533deba683a278a16515e3e8b18f",
    "SRC_MEXTO_ARM_BINOP": "d28cad5acebb257c6662e5ab445f66cacceb8d93b0d05094e50212e92a00872c",
    "SRC_MEXTO_ARM_BORROW": "cb0404e5908fdb394e1c146ca207d3dfc33d51c8cfff1f3a6a28650fe1cdae9d",
    "SRC_MEXTO_ARM_BR": "1ade553c361e983358078c2e0cbbef9705adf0db568d1694147b5d78c6b08a05",
    "SRC_MEXTO_ARM_CALL": "a488374c8e1c6d6b6b4a7a426c08ea8171fbc651611b4f98a61d35dbe9d3f6cd",
    "SRC_MEXTO_ARM_CALLINDIRECT": "1bffa8124c84238c006b7fca05fe5f1d0eef5632515d71f4285bb9c96fbfa00d",
    "SRC_MEXTO_ARM_CAST": "fefae7029e1f46afe8204677bad75edfe7bd417709db7db6e3a5255348eff7f2",
    "SRC_MEXTO_ARM_CONDBR": "f3c7719ccc3dbbfc866f11de2c7a9b84903d2dccafd60251a1388fb854ffc772",
    "SRC_MEXTO_ARM_CONST_": "b6075d9b715343f9063ad0668fb2668739e3ca6a09de625cc0393b2d3dfc2c24",
    "SRC_MEXTO_ARM_COPY": "0a5401d89cbaf66d72771d60bef72986d4ce455470576d9bf1c2dc7f7b4d11c9",
    "SRC_MEXTO_ARM_EXTRACTELEMENT": "578e6b199f57045edc22dedc8b13da06e5122762f86fed80ffdda18d3ffa1df9",
    "SRC_MEXTO_ARM_EXTRACTFIELD": "d1a6a6ebdb90447f2afca1f08bf3c9cc65784e1de0da9010662a8dc2a906eb3e",
    "SRC_MEXTO_ARM_FCMP": "280e3d59750bea4c31c380d6531d01b088a564b13d581c250a4bbf15432309e2",
    "SRC_MEXTO_ARM_GEP": "d5babcfe2b698e8be51b806e3f4048ce8aaf425fa600fa641e4fcf0a2add726f",
    "SRC_MEXTO_ARM_GLOBALADDR": "88a6aab8af5577b4fd09d8cee0353cfa68b30c05a2825a706d4687bfb5d7ec5c",
    "SRC_MEXTO_ARM_ICMP": "f559c19f8471b2f08dc98375f278c323a470f589af3a1e8d376af591065d84e1",
    "SRC_MEXTO_ARM_INSERTFIELD": "03031795ebb5d0d52667728d94a90de54f872d57fe2e43c86ead7d029f31750a",
    "SRC_MEXTO_ARM_LOAD": "985a14d2bd772126fe0acc8b65cf7b39b56f0d416638f2b26d8705c1642aa020",
    "SRC_MEXTO_ARM_OVERFLOW": "0bb943d26da122a54d499e746baeb8448d90a31907a1450d1fbee0c87dbc5a4f",
    "SRC_MEXTO_ARM_PTRDATA": "02c9bfd65151db8dbe7c9c956846f3cbf02687710e4553813b84c7e7b8f0c955",
    "SRC_MEXTO_ARM_PTRFROMPARTS": "820e415dcdbfa4a70e7058f735797e27b786297a45f14701b8fc1a60c374fe1d",
    "SRC_MEXTO_ARM_PTRMETADATA": "da9b2a66b60dac57a8f16d8cfc24042fa2ea57f7331b0d1ed97f1d60020ce6c2",
    "SRC_MEXTO_ARM_RELEASE": "6bc346bac022f7372bb7dfec83fe92bf75142e0469d2514fa06ab92e4dbfe4c0",
    "SRC_MEXTO_ARM_RET": "12fadd2af5cf0e913c01884673db63f83ccac49c2bc69dadd88a5dd0eafd6193",
    "SRC_MEXTO_ARM_SELECT": "fe4a908a2762d26ba2cfbe7ab95133a8fc919bb0b1e80418b66b8a59323509b9",
    "SRC_MEXTO_ARM_STORE": "f9c7d0541ab919ad43de9667e5d68bfadf950f8c48c379f9b1f5cdf8c472eb21",
    "SRC_MEXTO_ARM_SWITCH": "95b931923bc1415a1a0791e2675762d03051a24e63ffd5a489bcd73ee850b12e",
    "SRC_MEXTO_ARM_UNDEF": "4ab7fc9c7feb083aa8724c2f37637434ba9350f012acc9e2006a9d87e2e15c07",
    "SRC_MEXTO_ARM_UNOP": "91d68cb528da6bb8b2b1b58d2ca3ec6e7e015931fb9175fa964ec4c2ec9b7957",
    "SRC_MEXTO_ARM_UNREACHABLE": "8d46e5b8b5f786d23c224f5d6158509fa747d4e020c6b927e7e8a1296d77d1ac",
    "SRC_MEXTO_CALLIND_EXEC": "912bf02fd58709662299ed263956aa4f3ac4a235da45c0f9a8cf40939fd141ac",
    "SRC_MEXTO_CALL_EXEC": "f59c540be81283eb71d20958a551c45cb28aa700e1dc6a4083da5b4afde84d7c",
    "SRC_MEXTO_CONDBR_B": "c7e0572b9d9863bb4766900bae2e0a4e83cce2f49e0e7e5cdd7e9163cea4b971",
    "SRC_MEXTO_CONDBR_EXEC": "096828261d78f7e0aa88ea9b0e5a55cefb52effe0edf9c92bb8b4e1bc3569be7",
    "SRC_MEXTO_GLOBALADDR": "c2019eaf0037dbfc05e16dd64f8f079304878a34386cc8368981623e26d8bfbb",
    "SRC_MEXTO_JUMP": "5d5a86d132d49574503873f877f612bba6cb83ffcb040ef3e6c3e0d986eb7ba8",
    "SRC_MEXTO_STEP": "07367034637dff7497f88d33f87f69c89e5441f7bdd3b087916116938ca5f09f",
    "SRC_MEXTO_STEPS": "f8677877cc26c8f6f03a4ca8e48cec5d657f8e23e38ba715e71bf50a720fd03d",
    "SRC_MEXTO_SWITCH_EXEC": "a2d0f495d52be8f1b6ac61b98d421a19bcb22d02232f334143e15d6c954986c0",
    "SRC_MEXTO_SWITCH_N": "b52e917e321537abdf84b5eccd5c3042bcf8ecb362a301f4c3494c7a449c1425",
    "SRC_MEXTVO_ARM_ALLOCA": "3196ee1f87ba27e037f5c020f245ec3145fd0c7d4e2ef58aea393c3feeee1bfb",
    "SRC_MEXTVO_ARM_ASSERT": "3f7e50056330b32f37746872b91dbb5d1a332647255eeac6fd83ebce17a55946",
    "SRC_MEXTVO_ARM_ATOMIC_FETCH_ADD_RELAXED_U64_SEQ": "c4df49501276f4beec5670e6d39ac6bb84e0ed22abade8f607780e25054ea5da",
    "SRC_MEXTVO_ARM_ATOMIC_FETCH_ADD_RELAXED_USIZE_SEQ": "db86189edde9e2085861031493801977464c9ff60022a324b4d3aa8b3fe513d2",
    "SRC_MEXTVO_ARM_BINOP": "4309d8152264fb525588233627eeeffb3c247305412d213284bbd9b0b618eafe",
    "SRC_MEXTVO_ARM_BORROW": "9b2b4368903b0e8d52c77991eeb9eca83997706a726257d4bf045c394342477c",
    "SRC_MEXTVO_ARM_BR": "c553456d540d04ffcb2888517966029fa69b8a90f0c0e21eedaf6a957babc84a",
    "SRC_MEXTVO_ARM_CALL": "c5b7f7f735ce6370ad551ea87088d9a41d20fb2759c75f29f887ac29f462bcc2",
    "SRC_MEXTVO_ARM_CALLINDIRECT": "2fbba3c43d2235ab8e88fc1e856265f2dcf863891135b88f37cfcfcbf16c0692",
    "SRC_MEXTVO_ARM_CAST": "bafbc60d15425ee6b5972393f239ffd916bb563e286ddfcfed301eb4dabc1d76",
    "SRC_MEXTVO_ARM_CONDBR": "2e79dab1b5f150f98b9c858c788fe796639d1339baa47a92adce927ea7fc1b2f",
    "SRC_MEXTVO_ARM_CONST_": "490d3effc6ce3c97fb751ce689b048c9323c029b7d83e57dcde1207ab5427c26",
    "SRC_MEXTVO_ARM_COPY": "92cd66ecb70c9aa97b49a28ac1050d7634881be79de81f6de9271cf8b25eecdf",
    "SRC_MEXTVO_ARM_EXTRACTELEMENT": "56d3300c0a6bcdc4b46f4f362a481a31813ea3bfac15c32feaeaf0a33e75b112",
    "SRC_MEXTVO_ARM_EXTRACTFIELD": "a7058fd9375c11fa96aa50fb26d73bba2ee249eed508e775c4c39dcbf7fb9e41",
    "SRC_MEXTVO_ARM_FCMP": "2d0b4b5d57727511fd7487519877b07e99a4d60f376f69d94f6d12a610ce6e7f",
    "SRC_MEXTVO_ARM_GEP": "8f362395493d82aac5863125bb5de8fe626c31ad48f644df84e185ee6e442b58",
    "SRC_MEXTVO_ARM_GLOBALADDR": "b30c85bc7f0306078c914e81bb32a813fbbb958b22375c0e91db13f6e0392585",
    "SRC_MEXTVO_ARM_ICMP": "95805c5c98b98648435eb31c6e72865813a0aaed86b7c3df032da9e7e21b77ff",
    "SRC_MEXTVO_ARM_INSERTFIELD": "79b02312a0e87b5c41bf1b6fe52fd4cda31996c1f4b1157cf32923f1ffca74d1",
    "SRC_MEXTVO_ARM_LOAD": "e48d3952b49d7e6e15c10c48fe77746cb7fb7f0d4d0199758eb6157bbe979286",
    "SRC_MEXTVO_ARM_OVERFLOW": "c4004b876080663998afdbf44d5fe6c798b3695df3ce673eb169b13832245b8e",
    "SRC_MEXTVO_ARM_PTRDATA": "719ab2a708a4cc6bae936a889e872ef0c9089b5cb40bda76953363c281498a02",
    "SRC_MEXTVO_ARM_PTRFROMPARTS": "75688cc4aca08a6365f67750be77aa6b47ce25c1c0ae2d210582f9969055e5cc",
    "SRC_MEXTVO_ARM_PTRMETADATA": "25c825e277beea51c9940486cfa3436dc8faeeec4865a8c2b8246ed2803673ec",
    "SRC_MEXTVO_ARM_RELEASE": "a41c3823bac49b7d9e99f206827f59cd9f92d232dabe283e03ac3b373380ba45",
    "SRC_MEXTVO_ARM_RET": "66e6cdd8ac5336b00de76d8a042801b46728209312614842d6eeb1221fdb9daf",
    "SRC_MEXTVO_ARM_SELECT": "ef57e671264c77eb291a1e6c3a303dc8e1daa4c726597f1535ab2ebb506e163e",
    "SRC_MEXTVO_ARM_STORE": "137051bc9a303a700887d9ca3ba33be2e766f974b831aaa1775ff10e8d64ddb5",
    "SRC_MEXTVO_ARM_SWITCH": "0b1ddfacb8ef8c19f1c9939bc9bdf7030fb373fa5e6818ab32ed4e87cdf2613a",
    "SRC_MEXTVO_ARM_UNDEF": "3a213fa3c691dbac00dd4cb4d378f58ad742518f3e8e2231b3b572fe2f905e9e",
    "SRC_MEXTVO_ARM_UNOP": "1af22eaf3880fbf60c91c49422457751ee1344c6648691cc7fcf6967de5eb930",
    "SRC_MEXTVO_ARM_UNREACHABLE": "8f6fb663ba7846dd1bf4711971bed3e3ce235755278e2e4f02921ffaa8b835fc",
    "SRC_MEXTVO_CALLIND_EXEC": "f9bc0147a064e0c101c17a1ab46202663ccdd9a8210b13428f1b560e6b764883",
    "SRC_MEXTVO_CALL_EXEC": "d37bb5d7f94533e998a0e73f4bec110f3595d6586c0170b3a2b98b629ff72621",
    "SRC_MEXTVO_CONDBR_B": "59c174579fa1d7a344f47aa838ce2a46187795d9f60d83e5674925e0b1171a19",
    "SRC_MEXTVO_CONDBR_EXEC": "b1a6b4fefcb7c31c3146dad44342cec647468b9d0b02992054438ce125385c3c",
    "SRC_MEXTVO_GLOBALADDR": "19329e60101e517096fb50b1703f4e21a9d6a7e2f9d6986653879e940e277a81",
    "SRC_MEXTVO_JUMP": "4d95280a74187a3f24c750971112ba548394516f2ccee9d6d4c59ace732fd60f",
    "SRC_MEXTVO_RUN": "5d614b05be64aa05ea2f1bb22c744cae005f82ab0f05919b4b03114b1322d160",
    "SRC_MEXTVO_STEP": "27ffa902eed680c0c04b3777a19e57f228095314d1313fb169e3d00af070e46c",
    "SRC_MEXTVO_STEPS": "724326fed37a4297749d72f63ddecf4874fb055288fb2ee8a8e5e576947e9288",
    "SRC_MEXTVO_SWITCH_EXEC": "373fdaee2e84f749c1fc1c11c60b66772ac49e549079c4f240228bfa87ef3bd7",
    "SRC_MEXTVO_SWITCH_N": "3207ee60ab3e3cb525a7d1f926e022230249f4988cf9ce2b07c3e2d1cd87c4b2",
    "SRC_MEXT_OK": "19e25cbc7d7d563cd5bbbd25294eab6050d911f6d18b4099bfb059f6b806fc67",
    "SRC_MEXT_OK_ASSERT": "444b8aceebb3cedea059da1e4024c5dc297096f59ddb57955ed1b631484b9beb",
    "SRC_MEXT_OK_BACK": "70e2b66328a3562494444499c04fb7f3e7b5adfea4b81c4383827cf65867917f",
    "SRC_MEXT_OK_NO_FUNC": "724088f74f81abd6cfb4eff2a4136cbb9b7b6fab9877239723d0ee8434dc830d",
    "SRC_MEXT_OK_NO_GLOBAL": "f231b4eab134b0a2720929667ffd2b00b7468b341d39b6bd3e86713fb1f824a3",
    "SRC_MEXT_OK_OF_RUNNING": "7de79ee85fed50c5768d0034cf6a6275401ddd71089eb245423e8e8afca384d3",
    "SRC_MEXT_OK_RET": "9f10ee7b50d35707febb420d0a448293f2c6d8548b4d4cf1b1e2d488b3b34d6d",
    "SRC_MEXT_OK_RET_TO": "c5b6df329423d1e62616e4d5f5e9280aeb379910553064e09c82def3f4ab1260",
    "SRC_MEXT_OK_RUNNING": "d7f03fc1a249237f7cfcf890a61664edd00badd775ed9744149e817fab9f09c1",
    "SRC_MEXT_OK_STUCK_NO_BLOCK": "d18cf75d8afdf66d69fd987a9bef46fb0b5ea16d6fe473b829d3c42e5f7391cd",
    "SRC_MEXT_OK_TYPE_ERROR_NOT_INT": "706786f4513c9001efc6f8705bf915fda82d4de54ddfd8ce3ac1a54863a6261e",
    "SRC_OVERFLOW_EXEC_BDST": "196059fd9aef83f547195d66c5267b26579464c07d3d987a34c4bcad27729cbc",
    "SRC_OVERFLOW_INTS_BDST": "03af3f3942f18f44f68dcc98370781b49b9b342f7db5ad7dee290f1ac502cdb7",
    "SRC_OVERFLOW_VALS_BDST": "766612145d0a96758f745a5b1626fb9c6a2808d50c9c4262e4ce92930d4e7eef",
    "SRC_PUSH_BDST": "1a3917e4551cb0d8240557838da9e1800f5bd6c75f9f6826525c6ffbcc8299b1",
    "SRC_RESOLVE_BDST": "a03ed4e3bfab394c1c242b59a923c33e73eef4268a590db2d65c33a6e6316fdb",
    "SRC_RET_VALS_BDST": "920dbf4532743a9f13f7ebf969e6563429688565f3bdebfbffb5fabd15087eeb",
    "SRC_STK_BOTRET_RET": "a9cc90a33f991f0c547278bcbc70d91494a63a1e1d2e11f270f1ee9e17755b5c",
    "SRC_STORE_CHECKED_BDST": "0443b9cc04279cd2ea7b681a4e10742708a617f52ed63e69b1fdf819a0fbd3c7",
    "SRC_STORE_EXEC_BDST": "55ad1a295a496df91701fcf2082d1aa71d3f88cee57e6f7c2c873e9933462c46",
    "SRC_STORE_LIVE_BDST": "319d40b4b4dc794208cf375cd4624fb1ce6b5d2161e174f1cc0ff58b860793dd",
    "SRC_SWITCH_EXEC_BDST": "326fc3a958e719e6124424d09c1556af024b7e021cc1b1bd169c7766a2b025a7",
    "SRC_SWITCH_N_BDST": "9a6e47b385e5859fdab75cefcd11e6d2ba2900ffee69ee50e8214e2cfc131ebb",
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
