#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0

"""Derive the EvalIR adequacy grid as a machine-read artifact (plan W5, §4(c)).

The B-SEM exit replaces the trust-ir constructor-NAME parity check's role
("cannot see semantic depth") with a per-constructor, per-FIELD account of
exactly what the Clean encoding preserves, drops, and why. This script makes
that account a generated artifact rather than prose: it emits
`data/evalir_adequacy_grid.json`, one row per syntax field of every `IRInst`
constructor plus the erased-slot and measured-divergence rows, each in exactly
one state:

  relevant-by-design            the `ir_exec` dispatch arm READS the field —
                                the semantics consults it, so no irrelevance
                                theorem is possible and none is claimed; the
                                field is measured by the battery rows instead.
  irrelevance-proved-await-mint the dispatch BINDS AND DROPS the field, and a
                                kernel-checked Eq.refl theorem states the step
                                is identical at every value of it. "await-mint"
                                because the current tree's kernel runs are the
                                big-box obligation (data/evalir_w5.PENDING.md);
                                per docs/SUITE_STATE.md that is recorded state,
                                never rounded up.
  audit-pin                     the field is ERASED — it has no `IRInst` slot
                                at all (the `align` operands) — so no theorem
                                can quantify over it; the mint parses the slot
                                fail-closed and records it, and a lineage test
                                pins the whole boundary as a stated, dated
                                model boundary.
  declared-delta                a MEASURED executor divergence from the W1-W4
                                and float-residue waves; the grid is its
                                permanent home, with the dated cite and the
                                committed witness/battery anchors.

Derivation rule — mechanical, fail-closed:

  * The field surface comes from the `IRInst` telescopes in
    `eval_ir_syntax.rs`; the per-field read/drop verdict comes from the
    `ir_exec` dispatch in `eval_ir_machine.rs` (word-boundary occurrence of
    the arm's pattern variable in the arm's RHS). The two sources must agree
    on the constructor set and on every arity. A new field is therefore
    classified the moment it exists or the derivation aborts — it cannot be
    silently unclassified.
  * Every dropped field MUST have a theorem row in THEOREMS below, and every
    THEOREMS entry must name a dropped field whose `def <name> ` exists in its
    stated source file. Both directions abort on mismatch.
  * Every erased-slot and delta row carries anchors — (file, verbatim
    substring) pairs that must be present, the blind-slot ledger row included
    — so a closed erasure or a moved witness breaks the derivation instead of
    outliving it.

The output is deterministic (content-derived provenance, no timestamps), so
re-running on an unchanged tree is a no-op diff.

Usage:
  python3 scripts/evalir_adequacy_grid.py               # derive + write
  python3 scripts/evalir_adequacy_grid.py --check       # fail if committed file differs
  python3 scripts/evalir_adequacy_grid.py --self-test   # mutation arms
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

CORE = "crates/clean-verify/src/spec/core_spec"
SYNTAX_PATH = f"{CORE}/eval_ir_syntax.rs"
MACHINE_PATH = f"{CORE}/eval_ir_machine.rs"
ADEQUACY_PATH = f"{CORE}/eval_ir_adequacy.rs"
W2A_SYNTH_PATH = f"{CORE}/eval_ir_w2a_synth.rs"
W2B_SYNTH_PATH = f"{CORE}/eval_ir_w2b_synth.rs"
W2C_SYNTH_PATH = f"{CORE}/eval_ir_w2c_synth.rs"
FCMP_PATH = f"{CORE}/eval_ir_fcmp.rs"
FLOAT_RES_PATH = f"{CORE}/eval_ir_float_res.rs"
FLOAT_RES_W_PATH = f"{CORE}/eval_ir_float_res_witnesses.rs"
MINT_PATH = "crates/clean-verify/src/ir_mint/emitted_inst.rs"
LEDGER_PATH = "data/crystal_mint_blind_slots.json"
AUDIT_PATH = "crates/clean-verify/tests/crystal_a1_lineage/operand_audit.rs"
SEMDIFF = "crates/clean-verify/tests/crystal_a3_semdiff"
SYNTH_CHAINS_PATH = f"{SEMDIFF}/synth_chains.rs"
W2B_CHAINS_PATH = f"{SEMDIFF}/w2b_chains.rs"
W2C_CHAINS_PATH = f"{SEMDIFF}/w2c_chains.rs"
WFR_CHAINS_PATH = f"{SEMDIFF}/wfr_chains.rs"
OUTPUT_PATH = "data/evalir_adequacy_grid.json"
SCHEMA = "evalir-adequacy-grid/v1"

INPUT_PATHS = [
    SYNTAX_PATH,
    MACHINE_PATH,
    ADEQUACY_PATH,
    W2A_SYNTH_PATH,
    W2B_SYNTH_PATH,
    W2C_SYNTH_PATH,
    FCMP_PATH,
    FLOAT_RES_PATH,
    FLOAT_RES_W_PATH,
    MINT_PATH,
    LEDGER_PATH,
    AUDIT_PATH,
    SYNTH_CHAINS_PATH,
    W2B_CHAINS_PATH,
    W2C_CHAINS_PATH,
    WFR_CHAINS_PATH,
]

STATE_PROVED = "irrelevance-proved-await-mint"
STATE_RELEVANT = "relevant-by-design"
STATE_AUDIT = "audit-pin"
STATE_DELTA = "declared-delta"

SINCE_PRE_W5 = (
    "pre-W5 (operand-audit era; registered beside the dispatch, kernel-run GREEN "
    "in prior suite passes)"
)
SINCE_W5 = "W5 2026-08-25 (authored; first kernel run is the big-box obligation)"

# (constructor, dispatch pattern variable) -> (theorem, source file, since).
THEOREMS: dict[tuple[str, str], tuple[str, str, str]] = {
    ("load", "t"): ("ir_exec_load_ty_irrelevant", ADEQUACY_PATH, SINCE_W5),
    ("load", "vol"): ("ir_exec_load_vol_irrelevant", ADEQUACY_PATH, SINCE_W5),
    ("store", "t"): ("ir_exec_store_ty_irrelevant", ADEQUACY_PATH, SINCE_W5),
    ("store", "vol"): ("ir_exec_store_vol_irrelevant", ADEQUACY_PATH, SINCE_W5),
    ("alloca", "t"): ("ir_exec_alloca_ty_irrelevant", ADEQUACY_PATH, SINCE_W5),
    ("gep", "t"): ("ir_exec_gep_ty_irrelevant", ADEQUACY_PATH, SINCE_W5),
    ("gep", "inb"): ("ir_exec_gep_inbounds_irrelevant", ADEQUACY_PATH, SINCE_W5),
    ("ptrdata", "t"): ("ir_exec_ptrdata_ty_irrelevant", ADEQUACY_PATH, SINCE_W5),
    ("ptrmetadata", "pt"): ("ir_exec_ptrmeta_pt_irrelevant", ADEQUACY_PATH, SINCE_W5),
    ("ptrmetadata", "mt"): ("ir_exec_ptrmeta_mt_irrelevant", ADEQUACY_PATH, SINCE_W5),
    ("ptrfromparts", "pt"): ("ir_exec_ptrparts_pt_irrelevant", ADEQUACY_PATH, SINCE_W5),
    ("ptrfromparts", "mt"): ("ir_exec_ptrparts_mt_irrelevant", ADEQUACY_PATH, SINCE_W5),
    ("switch", "exh"): ("ir_exec_switch_exh_irrelevant", MACHINE_PATH, SINCE_PRE_W5),
    ("callindirect", "sig"): ("ir_exec_callind_sig_irrelevant", MACHINE_PATH, SINCE_PRE_W5),
    ("callindirect", "cc"): ("ir_exec_callind_conv_irrelevant", MACHINE_PATH, SINCE_PRE_W5),
    ("extractfield", "t"): ("ir_exec_extractfield_ty_irrelevant", ADEQUACY_PATH, SINCE_W5),
    ("insertfield", "t"): ("ir_exec_insertfield_ty_irrelevant", ADEQUACY_PATH, SINCE_W5),
    ("extractelement", "t"): (
        "ir_exec_extractelement_ty_irrelevant",
        ADEQUACY_PATH,
        SINCE_W5,
    ),
    ("undef", "t"): ("ir_exec_undef_ty_irrelevant", ADEQUACY_PATH, SINCE_W5),
    ("select", "t"): ("ir_exec_select_ty_irrelevant", ADEQUACY_PATH, SINCE_W5),
}

AUDIT_PIN_TEST = "the_alignment_operand_reaches_the_mint_and_its_exec_erasure_is_pinned"

# The three erased `align` slots: constructor -> (its pinned IRInst declaration
# line, the mint anchors proving the slot is parsed fail-closed).
ERASED_DECLS = {
    "load": "| load : IRTy → Nat → Bool → IRInst",
    "store": "| store : IRTy → Nat → Nat → Bool → IRInst",
    "alloca": "| alloca : IRTy → IROption Nat → IRInst",
}
ERASED_MINT_ANCHORS = {
    "load": [
        'r.r_align(format!("load:{align:?}"));',
        "is not an operand this reader knows on a `load`",
    ],
    "store": [
        'r.r_align(format!("store:{align:?}"));',
        "is not an operand this reader knows on a `store`",
    ],
    # No emitted chained body allocas, so the mint has NO alloca arm at all:
    # the whole instruction (align included) falls through to the fail-closed
    # NoImage refusal. The derivation additionally checks the mnemonic is
    # absent from the reader.
    "alloca": ['CoreError::NoImage(format!("printed instruction'],
}

DELTAS = [
    {
        "id": "undef-execution",
        "constructor": "undef",
        "clean": (
            "the dispatch arm binds the one untyped poison value IRScalar.undef_ and the "
            "module returns it (kernel witness ir_w2a_ud_on_run)"
        ),
        "e2": (
            "the pinned reference interpreter refuses to EXECUTE Inst::Undef — 'executing "
            "undef would read an undefined value' — and faults undefined_behavior"
        ),
        "measured": (
            "2026-08-25 at trust-ir a4e81b6, interpret.rs:619-623; the battery row is a "
            "SynthExpect::DeclaredDelta, asserted to reproduce exactly and never counted as "
            "agreement"
        ),
        "recorded_in": (
            "data/evalir_w2a.PENDING.md delta 2 (the undef coverage-policy question for the "
            "big-box mint session rides there)"
        ),
        "anchors": [
            (SYNTH_CHAINS_PATH, "interpret.rs:619-623"),
            (W2A_SYNTH_PATH, "ir_w2a_ud_on_run"),
        ],
    },
    {
        "id": "extractelement-oob-class",
        "constructor": "extractelement",
        "clean": (
            "index 3 on a three-element container is type_error bad_field, fail-closed at "
            "every triple (kernel witness ir_w2a_ee_oob)"
        ),
        "e2": "the same read is undefined_behavior ('element 3 is out of bounds')",
        "measured": (
            "2026-08-25 at trust-ir a4e81b6, interpret.rs:4507-4516; the fault CLASSES "
            "differ, and the battery carries the row as a declared delta rather than mapping "
            "one class onto the other"
        ),
        "recorded_in": "data/evalir_w2a.PENDING.md delta 3",
        "anchors": [
            (W2A_SYNTH_PATH, "ir_w2a_ee_oob"),
            (SYNTH_CHAINS_PATH, "interpret.rs:4507-4516"),
        ],
    },
    {
        "id": "null-callee-code",
        "constructor": "callindirect",
        "clean": (
            "calling through the null function pointer is ub null_deref at every payload "
            "(kernel witness ir_w2c_ci_on_null)"
        ),
        "e2": (
            "the interpreter reports its own invalid_function_pointer code ('CallIndirect: "
            "null function pointer'), NOT undefined_behavior"
        ),
        "measured": (
            "2026-08-25 at trust-ir a4e81b6, interpret.rs:1415-1421; "
            "invalid_function_pointer is outside the two-class outcome map on purpose, so "
            "the row is a declared delta, never class agreement"
        ),
        "recorded_in": "data/evalir_w2c.PENDING.md delta 1",
        "anchors": [
            (W2C_SYNTH_PATH, "ir_w2c_ci_on_null"),
            (W2C_CHAINS_PATH, "interpret.rs:1415-1421"),
        ],
    },
    {
        "id": "uninit-fault-site",
        "constructor": "load",
        "clean": (
            "ir_load_value faults ub uninit AT THE LOAD of a fresh cell (kernel witness "
            "ir_w2b_al_on_uninit)"
        ),
        "e2": (
            "a plain load of uninitialized bytes yields inert PartialBytes poison; "
            "undefined_behavior fires only when the value is INSPECTED — for synth_alloca at "
            "the ret signature check (reject_partial)"
        ),
        "measured": (
            "2026-08-25 at trust-ir a4e81b6, interpret.rs:5402-5403; the battery row is "
            "UbAgree(Uninit) — class agreement, site divergence — because that module's only "
            "path from the poisoned load ends in an inspection"
        ),
        "residue": (
            "a program that loads uninitialized memory and only COPIES/STORES it onward is "
            "UB under Clean's semantics and defined under the interpreter's "
            "copy-propagates-poison discipline — a real divergence class no battery row "
            "measures; this grid row is its recorded owner (the W2b handoff assigned it to "
            "the adequacy stream)"
        ),
        "recorded_in": "data/evalir_w2b.PENDING.md delta 1",
        "anchors": [
            (W2B_SYNTH_PATH, "ir_w2b_al_on_uninit"),
            (W2B_CHAINS_PATH, "reject_partial"),
        ],
    },
    {
        "id": "f32-compares",
        "constructor": "fcmp",
        "clean": (
            "the comparison domain decides binary64 only; float_ w with w != 64 is the "
            "tagged unmodelled float_domain outcome, kernel-witnessed universally over every "
            "operator and operand pair (ir_fcmp_f32_unmodelled)"
        ),
        "e2": "the pinned interpreter ANSWERS binary32 compares (eval_fcmp_f32)",
        "measured": (
            "2026-08-25 at trust-ir a4e81b6, interpret.rs:6038-6054; a tagged refusal and an "
            "answer share no row vocabulary, so the boundary has no battery row by design "
            "and can never become a wrong answer"
        ),
        "recorded_in": "data/evalir_w4.PENDING.md delta 2",
        "anchors": [
            (FCMP_PATH, "ir_fcmp_f32_unmodelled"),
            (FCMP_PATH, "eval_fcmp_f32"),
        ],
    },
    {
        "id": "junk-bit-nan",
        "constructor": "fcmp",
        "clean": (
            "any float_ bit pattern n >= 2^64 classifies nan_, and a comparison on it "
            "ANSWERS with the NaN verdicts (ordered false / unordered true) — kernel "
            "witnesses ir_exact_fcmp_junk_oeq / ir_exact_fcmp_junk_ueq"
        ),
        "e2": (
            "no E2 leg exists BY CONSTRUCTION: trust-ir's FloatBits(u64) cannot carry 2^64, "
            "so the junk fragment is a Clean-only inhabitant"
        ),
        "measured": (
            "2026-08-25; kernel-witnessed and stated rather than battery-measured — unlike "
            "the arithmetic lane, where every junk operation is unmodelled, comparisons "
            "return the NaN answer"
        ),
        "recorded_in": "data/evalir_w4.PENDING.md delta 3",
        "anchors": [
            (FCMP_PATH, "ir_exact_fcmp_junk_oeq"),
            (FCMP_PATH, "ir_exact_fcmp_junk_ueq"),
        ],
    },
    {
        "id": "frem-answers-in-e2",
        "constructor": "binop",
        "clean": (
            "frem is the tagged unmodelled float_domain outcome at every type and operand "
            "pair — a DATED refusal, kernel-witnessed universally (ir_frem_unmodelled)"
        ),
        "e2": "the pinned interpreter ANSWERS f64 frem (eval_float_binop, `lhs % rhs`)",
        "measured": (
            "2026-08-25 at trust-ir a4e81b6, interpret.rs:5946; an exact float remainder "
            "needs the quotient's significand at guard precision — the measured "
            "fdiv-finite cost class (eval_ir_float_fin's named build item) — so the "
            "refusal stands, tagged, until that build item lands; a refusal and an answer "
            "share no row vocabulary, so no battery row exists by design"
        ),
        "recorded_in": "data/evalir_float_residue.PENDING.md",
        "anchors": [
            (FLOAT_RES_W_PATH, "ir_frem_unmodelled"),
            (FLOAT_RES_W_PATH, "eval_float_binop"),
        ],
    },
    {
        "id": "fsqrt-answers-in-e2",
        "constructor": "unop",
        "clean": (
            "fsqrt is the tagged unmodelled float_domain outcome at every type and operand "
            "— a DATED refusal, kernel-witnessed universally (ir_fsqrt_unmodelled)"
        ),
        "e2": "the pinned interpreter ANSWERS f64 fsqrt (eval_float_unop, `operand.sqrt()`)",
        "measured": (
            "2026-08-25 at trust-ir a4e81b6, interpret.rs:5994; a correctly-rounded square "
            "root is an iterated guard-precision division on this substrate — the "
            "fdiv-finite cost class compounded — the refusal the plan itself reserved "
            "('fsqrt is the hard one and can carry a dated refusal')"
        ),
        "recorded_in": "data/evalir_float_residue.PENDING.md",
        "anchors": [
            (FLOAT_RES_W_PATH, "ir_fsqrt_unmodelled"),
            (FLOAT_RES_W_PATH, "operand.sqrt()"),
        ],
    },
    {
        "id": "round-nan-payload",
        "constructor": "unop",
        "clean": (
            "ffloor/fceil/ftrunc REFUSE a NaN operand (the rounded result is *a* NaN whose "
            "payload the host libm chooses) — kernel witness ir_exact_ffloor_nan_refused; "
            "every non-NaN pattern answers exactly"
        ),
        "e2": (
            "the interpreter answers a NaN through host floor/ceil/trunc, with whatever "
            "payload the host returns"
        ),
        "measured": (
            "2026-08-25 at trust-ir a4e81b6, interpret.rs:5995-5997; the same "
            "implementation-defined-payload boundary the arithmetic lane carries, at the "
            "rounding family — the battery's rounding chain carries NO NaN row by design "
            "(wfr_chains.rs module doc)"
        ),
        "recorded_in": "data/evalir_float_residue.PENDING.md",
        "anchors": [
            (FLOAT_RES_W_PATH, "ir_exact_ffloor_nan_refused"),
            (WFR_CHAINS_PATH, "the rounding family on a NaN"),
        ],
    },
    {
        "id": "minmax-ambiguous-cells",
        "constructor": "binop",
        "clean": (
            "fmin/fmax REFUSE exactly two cells: BOTH operands NaN (result payload "
            "implementation-defined) and the OPPOSITE-signed zero pair (llvm.minnum/maxnum "
            "'returns either one of the operands' when they compare equal) — kernel "
            "witnesses ir_exact_fmin_nan_both_refused, ir_exact_fmin_zero_pair_refused, "
            "ir_exact_fmax_zero_pair_refused; every other classified cell answers, one-NaN "
            "cells included (the other operand is returned)"
        ),
        "e2": (
            "the interpreter answers both cells with whatever host f64::min/max return "
            "there — a value a conforming host is free to vary"
        ),
        "measured": (
            "2026-08-25 at trust-ir a4e81b6, interpret.rs:5947-5948; an answer here could "
            "be refuted by a conforming host and a tagged refusal cannot, so the cells are "
            "refused and carry NO battery row (wfr_chains.rs module doc)"
        ),
        "recorded_in": "data/evalir_float_residue.PENDING.md",
        "anchors": [
            (FLOAT_RES_W_PATH, "ir_exact_fmin_nan_both_refused"),
            (FLOAT_RES_W_PATH, "ir_exact_fmin_zero_pair_refused"),
        ],
    },
    {
        "id": "fp-casts-answer-in-e2",
        "constructor": "cast",
        "clean": (
            "all eight fp casts (fptrunc/fpext/fptoui/fptosi/uitofp/sitofp/fptosisat/"
            "fptouisat) are the tagged unmodelled float_domain outcome at every source "
            "type, destination type and operand — DATED refusals, kernel-witnessed "
            "universally (ir_cast_fptrunc_unmodelled and its seven siblings)"
        ),
        "e2": (
            "the pinned interpreter ANSWERS all eight (FPTrunc/FPExt through host "
            "formats, FPToUI/FPToSI with range UB, the saturating pair, UIToFP/SIToFP "
            "rounding)"
        ),
        "measured": (
            "2026-08-25 at trust-ir a4e81b6, interpret.rs:4005-4143; fp<->int conversion "
            "needs significand scaling plus rounding (the fdiv-finite cost class) and "
            "fptrunc/fpext need the binary32 format this domain does not model — each "
            "refusal is a fragment boundary of THIS model, never silence"
        ),
        "recorded_in": "data/evalir_float_residue.PENDING.md",
        "anchors": [
            (FLOAT_RES_W_PATH, "ir_cast_fptrunc_unmodelled"),
            (FLOAT_RES_W_PATH, "interpret.rs:4005-4143"),
        ],
    },
]


class GridError(Exception):
    """Fail-closed: any input we cannot fully account for aborts the run."""


# ------------------------------------------------------------------- parsing


def parse_irinst_fields(text: str) -> list[tuple[str, list[str]]]:
    """`IRInst` constructor telescopes from eval_ir_syntax.rs."""
    lines = text.splitlines()
    at = [i for i, ln in enumerate(lines) if "inductive IRInst : Type" in ln]
    if len(at) != 1:
        raise GridError(
            f"{SYNTAX_PATH}: expected exactly one `inductive IRInst : Type`, found {len(at)}"
        )
    out: list[tuple[str, list[str]]] = []
    for ln in lines[at[0] + 1 :]:
        m = re.match(r"^\s*\|\s*([A-Za-z_][A-Za-z0-9_]*)\s*:\s*(.+)$", ln)
        if not m:
            break
        parts = [p.strip() for p in m.group(2).split("→")]
        if not parts or parts[-1].rstrip('",') != "IRInst":
            raise GridError(f"{SYNTAX_PATH}: constructor `{m.group(1)}` does not end in IRInst")
        out.append((m.group(1), parts[:-1]))
    if len(out) != len({n for n, _ in out}):
        raise GridError(f"{SYNTAX_PATH}: duplicate IRInst constructor names")
    if not out:
        raise GridError(f"{SYNTAX_PATH}: IRInst constructor list parsed empty")
    return out


def parse_dispatch(text: str) -> list[tuple[str, list[str], str]]:
    """The `ir_exec` dispatch arms: (ctor, pattern vars, rhs)."""
    lines = text.splitlines()
    at = [
        i
        for i, ln in enumerate(lines)
        if "def ir_exec (m : IRModule) (i : IRInst)" in ln
    ]
    if len(at) != 1:
        raise GridError(f"{MACHINE_PATH}: expected exactly one ir_exec definition, found {len(at)}")
    out: list[tuple[str, list[str], str]] = []
    for ln in lines[at[0] + 1 :]:
        t = ln.strip()
        if not t.startswith("| IRInst."):
            break
        t = t.removeprefix("| IRInst.")
        t = t.removesuffix('",')
        if " => " not in t:
            raise GridError(f"{MACHINE_PATH}: malformed dispatch arm `{t}`")
        lhs, rhs = t.split(" => ", 1)
        toks = lhs.split()
        out.append((toks[0], toks[1:], rhs))
    if not out:
        raise GridError(f"{MACHINE_PATH}: ir_exec dispatch arms parsed empty")
    return out


def var_used(rhs: str, var: str) -> bool:
    return re.search(rf"\b{re.escape(var)}\b", rhs) is not None


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


# -------------------------------------------------------------------- derive


def read_inputs(root: str) -> dict[str, str]:
    inputs: dict[str, str] = {}
    for rel in INPUT_PATHS:
        p = os.path.join(root, rel)
        if not os.path.isfile(p):
            raise GridError(f"input source missing: {rel}")
        with open(p, encoding="utf-8") as f:
            inputs[rel] = f.read()
    return inputs


def require_anchor(inputs: dict[str, str], path: str, needle: str, who: str) -> None:
    if needle not in inputs[path]:
        raise GridError(f"{who}: anchor text not found in {path}: {needle!r}")


def derive(
    inputs: dict[str, str],
    theorems: dict[tuple[str, str], tuple[str, str, str]] | None = None,
) -> dict:
    theorems = THEOREMS if theorems is None else theorems
    ctors = parse_irinst_fields(inputs[SYNTAX_PATH])
    arms = parse_dispatch(inputs[MACHINE_PATH])

    ctor_names = [n for n, _ in ctors]
    arm_names = [c for c, _, _ in arms]
    if set(ctor_names) != set(arm_names):
        raise GridError(
            "syntax and dispatch DISAGREE on the constructor set: "
            f"only in syntax {sorted(set(ctor_names) - set(arm_names))}; "
            f"only in dispatch {sorted(set(arm_names) - set(ctor_names))}"
        )
    if len(ctor_names) != 28:
        raise GridError(f"IRInst constructor census must be 28, found {len(ctor_names)}")
    arm_by_name = {c: (vs, rhs) for c, vs, rhs in arms}

    rows: list[dict] = []
    n_relevant = 0
    n_proved = 0
    used_theorems: set[tuple[str, str]] = set()
    dispatch_doc: dict[str, dict] = {}

    for ctor, fields in ctors:
        vars_, rhs = arm_by_name[ctor]
        if len(vars_) != len(fields):
            raise GridError(
                f"{ctor}: dispatch binds {len(vars_)} variables for {len(fields)} declared "
                "fields — the two sources have drifted"
            )
        dispatch_doc[ctor] = {"vars": vars_, "rhs": rhs}
        for i, (ty, var) in enumerate(zip(fields, vars_)):
            used = var_used(rhs, var)
            key = (ctor, var)
            if used:
                if key in theorems:
                    raise GridError(
                        f"{ctor}.{var}: THEOREMS claims an irrelevance theorem for a field "
                        "the dispatch arm READS — the theorem is impossible; fix the table "
                        "or the dispatch"
                    )
                rows.append(
                    {
                        "kind": "field",
                        "constructor": ctor,
                        "index": i,
                        "var": var,
                        "ty": ty,
                        "state": STATE_RELEVANT,
                    }
                )
                n_relevant += 1
            else:
                if key not in theorems:
                    raise GridError(
                        f"{ctor}.{var}: the dispatch DROPS this field and no irrelevance "
                        "theorem is registered for it — an unclassified erasure; add the "
                        "theorem (the eval_ir_adequacy.rs pattern) and its THEOREMS row"
                    )
                name, src_path, since = theorems[key]
                if f"def {name} " not in inputs[src_path]:
                    raise GridError(
                        f"{ctor}.{var}: theorem `{name}` is not defined in {src_path}"
                    )
                used_theorems.add(key)
                rows.append(
                    {
                        "kind": "field",
                        "constructor": ctor,
                        "index": i,
                        "var": var,
                        "ty": ty,
                        "state": STATE_PROVED,
                        "theorem": name,
                        "theorem_source": src_path,
                        "since": since,
                    }
                )
                n_proved += 1

    stale = set(theorems) - used_theorems
    if stale:
        raise GridError(
            f"THEOREMS names fields that do not exist or are not dropped: {sorted(stale)}"
        )

    # Erased `align` slots (audit-pin rows).
    ledger = json.loads(inputs[LEDGER_PATH])
    align_rows = [s for s in ledger.get("slots", []) if s.get("id") == "align"]
    if len(align_rows) != 1 or align_rows[0].get("kind") != "compared":
        raise GridError(
            f"{LEDGER_PATH}: expected exactly one slot with id `align`, kind `compared` "
            "(the R8 ledger row the audit-pin rows cite)"
        )
    require_anchor(inputs, AUDIT_PATH, f"fn {AUDIT_PIN_TEST}", "audit-pin")
    if "alloca" in inputs[MINT_PATH]:
        raise GridError(
            f"{MINT_PATH}: now mentions `alloca` — the audit-pin rows claim the mint has NO "
            "alloca arm (the mnemonic falls through to the fail-closed NoImage refusal); "
            "re-derive the alloca.align row against the new reader"
        )
    erased_rows = []
    for ctor in ("load", "store", "alloca"):
        require_anchor(inputs, SYNTAX_PATH, ERASED_DECLS[ctor], f"{ctor}.align")
        for needle in ERASED_MINT_ANCHORS[ctor]:
            require_anchor(inputs, MINT_PATH, needle, f"{ctor}.align")
        erased_rows.append(
            {
                "kind": "erased",
                "constructor": ctor,
                "name": "align",
                "state": STATE_AUDIT,
                "trust_field": "align : Option<u64>",
                "boundary": (
                    "ERASED, not modelled: the cell-addressed machine has no byte offsets, "
                    "so alignment is not observable in it and `IRInst` has no slot to carry "
                    "it — that unobservability is itself the adequacy statement (plan §4(c) "
                    "option (ii), adopted W5 2026-08-25). The mint reads the printed slot "
                    "fail-closed (an unrecognised trailing operand is refused, killing the "
                    "silently-dropped class) and records it in the `aligns` lane, so the "
                    "erasure is a stated, dated model boundary, not silence."
                ),
                "ledger": (
                    f"{LEDGER_PATH} slot id `align` (kind: compared, HALF-CLOSED "
                    "2026-08-20) — the R8 ledger row"
                ),
                "pinned_by": (
                    f"crystal_a1_lineage::operand_audit::{AUDIT_PIN_TEST}"
                ),
                "anchors": [
                    {"file": MINT_PATH, "text": t} for t in ERASED_MINT_ANCHORS[ctor]
                ]
                + [{"file": SYNTAX_PATH, "text": ERASED_DECLS[ctor]}],
            }
        )

    # Declared-delta rows.
    delta_rows = []
    for d in DELTAS:
        if d["constructor"] not in set(ctor_names):
            raise GridError(f"delta {d['id']}: unknown constructor {d['constructor']}")
        for path, needle in d["anchors"]:
            require_anchor(inputs, path, needle, f"delta {d['id']}")
        row = {
            "kind": "delta",
            "id": d["id"],
            "constructor": d["constructor"],
            "state": STATE_DELTA,
            "clean": d["clean"],
            "e2": d["e2"],
            "measured": d["measured"],
            "recorded_in": d["recorded_in"],
            "anchors": [{"file": p, "text": t} for p, t in d["anchors"]],
        }
        if "residue" in d:
            row["residue"] = d["residue"]
        delta_rows.append(row)

    all_rows = rows + erased_rows + delta_rows
    totals = {
        "rows": len(all_rows),
        "field_rows": len(rows),
        STATE_RELEVANT: n_relevant,
        STATE_PROVED: n_proved,
        STATE_AUDIT: len(erased_rows),
        STATE_DELTA: len(delta_rows),
    }

    return {
        "schema": SCHEMA,
        "what": (
            "Per-constructor, per-field adequacy account of EvalIR's encoding of the "
            "28 constructed trust_ir::Inst variants — the B-SEM §4(c) grid. Every syntax "
            "field of every IRInst constructor is classified; the erased align slots and "
            "the measured W1-W4 and float-residue executor divergences have their "
            "permanent rows here."
        ),
        "constructors": len(ctor_names),
        "rows": all_rows,
        "dispatch": dispatch_doc,
        "totals": totals,
        "provenance": {
            "derived_by": "scripts/evalir_adequacy_grid.py",
            "rule": (
                "field surface = IRInst telescopes (eval_ir_syntax.rs); read/drop verdict "
                "= word-boundary use of the arm's pattern variable in the ir_exec arm RHS "
                "(eval_ir_machine.rs); dropped fields must name a registered theorem; "
                "erased and delta rows must anchor to live source. Fail-closed on any "
                "mismatch. Gate: tests/eval_ir/adequacy_grid.rs re-derives the surface "
                "independently."
            ),
            "inputs": [
                {"path": rel, "sha256": sha256_text(inputs[rel])} for rel in INPUT_PATHS
            ],
        },
    }


def render(result: dict) -> str:
    return json.dumps(result, indent=2, sort_keys=False, ensure_ascii=False) + "\n"


# ----------------------------------------------------------------- self-test


def self_test(root: str) -> int:
    """Mutation arms: every planted defect must be DETECTED (raise), and the
    unmutated pipeline must succeed. Prints one line per arm."""
    failures = 0
    real = read_inputs(root)

    def arm(name: str, fn) -> None:
        nonlocal failures
        try:
            fn()
        except GridError as e:
            print(f"  self-test ARM ok: {name} -> detected ({e})")
            return
        print(f"  self-test ARM FAILED: {name} -> mutation NOT detected")
        failures += 1

    def mutated(path: str, old: str, new: str) -> dict[str, str]:
        # Replace EVERY occurrence: an anchor that also appears in a doc
        # comment or a registration table must disappear everywhere for the
        # arm to prove the detection is real.
        if old not in real[path]:
            raise SystemExit(f"self-test substrate drift: {old!r} not in {path}")
        m = dict(real)
        m[path] = m[path].replace(old, new)
        return m

    # 1. Syntax gains a field the dispatch does not bind (arity drift).
    arm(
        "planted extra field on IRInst.load (syntax/dispatch arity drift)",
        lambda: derive(
            mutated(
                SYNTAX_PATH,
                "| load : IRTy → Nat → Bool → IRInst",
                "| load : IRTy → Nat → Nat → Bool → IRInst",
            )
        ),
    )

    # 2. Syntax gains a constructor with no dispatch arm.
    arm(
        "planted constructor in IRInst (constructor-set drift)",
        lambda: derive(
            mutated(
                SYNTAX_PATH,
                "| select : IRTy → Nat → Nat → Nat → IRInst",
                "| select : IRTy → Nat → Nat → Nat → IRInst\n| planted : IRInst",
            )
        ),
    )

    # 3. A dropped field loses its theorem row (unclassified erasure).
    def no_load_ty():
        t = {k: v for k, v in THEOREMS.items() if k != ("load", "t")}
        derive(real, theorems=t)

    arm("theorem row deleted for dropped field load.t", no_load_ty)

    # 4. The theorem's definition disappears from its source file.
    arm(
        "theorem definition removed from eval_ir_adequacy.rs",
        lambda: derive(
            mutated(ADEQUACY_PATH, "def ir_exec_load_ty_irrelevant ", "def ir_exec_gone ")
        ),
    )

    # 5. A theorem claimed for a field the dispatch READS.
    def claim_used():
        t = dict(THEOREMS)
        t[("binop", "op")] = ("ir_exec_binop_op_irrelevant", ADEQUACY_PATH, SINCE_W5)
        derive(real, theorems=t)

    arm("theorem claimed for a read field binop.op", claim_used)

    # 6. The dispatch starts READING a field a theorem claims is dropped.
    arm(
        "dispatch arm starts reading load's dropped type",
        lambda: derive(
            mutated(
                MACHINE_PATH,
                "| IRInst.load t p vol => ir_bind_result s rs (ir_load_eval s (ir_getd s p))",
                "| IRInst.load t p vol => ir_bind_result s rs (ir_load_eval s (ir_getd s t))",
            )
        ),
    )

    # 7. An erased-slot mint anchor disappears (the align lane closed or moved).
    arm(
        "mint align anchor removed",
        lambda: derive(
            mutated(MINT_PATH, 'r.r_align(format!("load:{align:?}"));', "")
        ),
    )

    # 8. A delta anchor disappears (a witness renamed or a cite dropped).
    arm(
        "delta anchor removed (ir_w2c_ci_on_null)",
        lambda: derive(
            mutated(W2C_SYNTH_PATH, "ir_w2c_ci_on_null", "ir_w2c_ci_renamed")
        ),
    )

    # 9. The R8 ledger row's id changes.
    arm(
        "ledger align row renamed",
        lambda: derive(mutated(LEDGER_PATH, '"id": "align"', '"id": "aligned"')),
    )

    # Baseline: the unmutated pipeline must derive successfully.
    try:
        result = derive(real)
    except GridError as e:
        print(f"  self-test BASELINE FAILED: real derivation errored: {e}")
        return 1
    t = result["totals"]
    print(
        f"  self-test baseline ok: {t['rows']} rows — {t[STATE_RELEVANT]} relevant, "
        f"{t[STATE_PROVED]} proved, {t[STATE_AUDIT]} audit-pin, {t[STATE_DELTA]} delta"
    )
    if failures:
        print(f"self-test: {failures} arm(s) FAILED", file=sys.stderr)
        return 1
    print("self-test: all arms green")
    return 0


# ---------------------------------------------------------------------- main


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true", help="fail if the committed output is stale")
    ap.add_argument("--self-test", action="store_true", help="run the mutation arms")
    args = ap.parse_args()

    if args.self_test:
        return self_test(REPO_ROOT)

    try:
        result = derive(read_inputs(REPO_ROOT))
    except GridError as e:
        print(f"evalir_adequacy_grid: FAIL-CLOSED: {e}", file=sys.stderr)
        return 1

    out_path = os.path.join(REPO_ROOT, OUTPUT_PATH)
    rendered = render(result)
    t = result["totals"]
    summary = (
        f"{t['rows']} rows — {t[STATE_RELEVANT]} relevant-by-design, "
        f"{t[STATE_PROVED]} irrelevance-proved-await-mint, {t[STATE_AUDIT]} audit-pin, "
        f"{t[STATE_DELTA]} declared-delta"
    )
    if args.check:
        try:
            with open(out_path, encoding="utf-8") as f:
                committed = f.read()
        except OSError:
            print(
                f"evalir_adequacy_grid: --check: {OUTPUT_PATH} missing; run without --check",
                file=sys.stderr,
            )
            return 1
        if committed != rendered:
            print(
                f"evalir_adequacy_grid: --check: {OUTPUT_PATH} is STALE; regenerate",
                file=sys.stderr,
            )
            return 1
        print(f"evalir_adequacy_grid: {OUTPUT_PATH} up to date: {summary}")
        return 0

    with open(out_path, "w", encoding="utf-8") as f:
        f.write(rendered)
    print(f"evalir_adequacy_grid: wrote {OUTPUT_PATH}: {summary}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
