#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0

"""Crystal link 4: can the DEPLOYED callees execute in EvalIR at all? A ratchet.

    python3 scripts/crystal_link4_executability.py --artifact-dir DIR          # gate
    python3 scripts/crystal_link4_executability.py --artifact-dir DIR --report OUT.json
    python3 scripts/crystal_link4_executability.py --artifact-dir DIR --rebase --reason TEXT
    python3 scripts/crystal_link4_executability.py --artifact-dir DIR --init --reason TEXT
    python3 scripts/crystal_link4_executability.py --artifact-dir DIR --reseat --reason TEXT
    python3 scripts/crystal_link4_executability.py --self-test

DIR is a trust dump directory holding `callees/<crate>.callees.manifest.json` and
`callees/<crate>.callees.trust-ir.txt` (the callee SIDECAR: the module link 4's
`ir_it_ag_correct` is stated over). Measured 2026-09-23 on
`target/crystal-lane/dump-link-O3-dp`.

WHY THIS EXISTS. `ir_it_ag_correct` is kernel-checked, and at the deployed module
it is VACUOUS: its callee hypotheses can be satisfied only by callees that reach
`ret` in `ir_eval`, and the deployed ones cannot (decision memo 2026-09-23, B3
and D5; the l4 review measured 1,442 of 2,508 closure bodies with no fault-free
path to `ret`). That figure lived in a review transcript. This script DERIVES it
from the artifact, every run, and refuses to let it get worse.

THREE MEASUREMENTS, per call closure (infer_type_fast's, and separately
infer_type's and tick_heartbeat's; the closure is the `call @func.N` graph of
the sidecar text, cross-checked edge-for-edge against the manifest's `member`
calls):

 (a) PROJECTABILITY. A body is unprojectable if it holds an instruction with no
     Clean `IRInst` image. The image set is DERIVED, never typed: the
     constructors of `inductive IRInst` are parsed out of the Lean source that
     `eval_ir_syntax.rs` registers; they must equal `EMITTED_INSTS` in
     `crates/clean-verify/tests/eval_ir/census.rs`; and the projector that maps
     `trust_ir::Inst` onto them (`scripts/crystal_a2_project/src/main.rs`,
     `fn inst`) must be a BIJECTION onto that set, arm by arm (crystal D1: one
     arm may image several variants only when SHARED_IMAGE_ARMS declares them --
     `Borrow | BorrowMut`, one arm in trust-ir's reference interpreter). A variant
     with no projector arm (`EndBorrow` among them) has no image. A second,
     stricter level also refuses an OPERATOR the projector's `mod ops` does not
     map (`band`/`bor`/`bxor`, the saturating float casts). The text mnemonic
     -> `trust_ir::Inst` variant table below is the trust-ir printer
     (`display.rs::write_inst` and the `Display` impls in `inst.rs`), and an
     unknown mnemonic is a REFUSAL, never "projectable". A third level,
     `unprojectable_bodies_projector`, is what the projector ACTUALLY refuses:
     [crystal D10, decision memo §15, 2026-09-25: a NATIVE atomic -- atomicrmw xchg/add/sub/
     and/or/xor, strong cmpxchg, atomic_load, atomic_store, fence -- is IMAGED, by the
     projector's `fn seq_atomic_image` EXPANSION into existing load/binop/icmp/select/store
     nodes, exact only under the ENVIRONMENT premise SEQ; its operand type is imaged as a
     load's, and its pointer is a load/store base for the undef rule. The imaged variants and
     rmw ops are DERIVED from that function (`derive_seq_atomic_image`); a max/min rmw and a
     weak cmpxchg stay unimaged. The model agreed with the real `a2project --usize-bits 64`
     on all 118 atomic-bearing bodies of dump-link-O3-me3off (scratch check, 2026-09-25).]
     Beyond kinds, it also refuses a body over an OPERAND -- a type its `fn ty` has no arm
     for (`fatptr<slice ..>`, `closure.N`, `[ty.N x M]`, `char`,
     recursively under `&`/`*`/`Rc<>`; `fatptr<dyn.N>`, `fatptr<container_len>` and
     `fatptr<container_vtable>` have arms since crystal E5; `functy.N` has an arm
     since crystal plan step 18), a constant its `fn cst` refuses (a negative
     `Int` inside an aggregate; a TOP-LEVEL negative `Int` at an integer type is imaged as
     its width-W bit pattern since decision memo §18, `fn negative_int_const_image`,
     DERIVED) or a global its global loop refuses (an
     array global takes `array[..]`; since step 18 a struct/tuple global takes
     an aggregate whose `symaddr<NAME>` images only as the address of exactly
     the module function NAME, read against the text's own function names). The accepted sets are derived from those arms; the model
     agreed body-for-body with the prebuilt `a2project --usize-bits 64` run on
     every one of the 2,783 sidecar members (2026-09-23 review).

 (b) RETURN-REACHABILITY, a LEAST fixpoint. A body RETURNS iff some path from
     its entry block reaches a `ret` through blocks that hold no definite EvalIR
     fault and whose every `call` targets a body already known to return. Least,
     not greatest: a recursion with no base case never returns, and only the
     least fixpoint is sound for the claim "this body cannot return" (a
     returning run has a finite call tree; induct on it). A fault counts only if
     it is DEFINITE on every execution reaching it, so the count is a sound
     LOWER bound on non-returning bodies: every rule below is a fact of EvalIR,
     pinned to the Lean text it rests on (ANCHORS), and a rule whose anchor is
     gone is REFUSED rather than silently applied. The rule families:
       undef_insertfield             a havoc `undef` as an `insertfield` aggregate base
                                     (the l4 review's rule; `ir_insert_field` faults)
       unimaged_kind / unimaged_op   no IRInst / operator image (see (a))
       unreachable                   `IRInst.unreachable` halts ub [memo §18: also an
                                     `assert` an undefined-behaviour halt obligation SITES,
                                     which the projector's `fn ub_halt_image` images as
                                     `unreachable` -- never the sanctioned-panic assert]
       assert_false                  `assert` of a `const bool false` (or its copy)
       undef_branch                  a havoc `undef` feeding condbr/switch/select/assert
       undef_other                   a havoc `undef` as load/store/gep base, a gep INDEX,
                                     borrow, call_indirect callee or copy operand
       cast_unmodelled               casts EvalIR never models (derived from the
                                     `ir_cast_eval` arms: ir_width_fault/ir_float_fault),
                                     a bitcast that is not int->int at one width,
                                     and binops whose arm is ir_float_fault (frem).
                                     [crystal D12, decision memo §18: a `bitcast ptr -> ptr`
                                     is the identity, imaged by the projector's `fn
                                     ptr_bitcast_identity_image` as `copy (ptr)` -- DERIVED
                                     from that function -- so it is not this family; its
                                     operand is then a `copy` operand for the undef rule and
                                     a callee reached through it is `callee_not_fnptr`.]
       call_unknown                  `call_indirect`: an unknown callee does NOT return
                                     (POLICY, not an EvalIR fact; its weight is reported)
       callee_not_fnptr              (crystal D1) a `call_indirect` whose callee is a `copy` at a
                                     non-`functy` type: the copy binds only a value of its type's
                                     shape class, the function class is `func_`'s alone, and
                                     `callindirect` halts on every non-`fnptr_` (ANCHORS
                                     callee_not_fnptr) -- so the copy or the call faults
     [crystal D1, 2026-09-25: a call_indirect DISPATCHED BY VALUE is not `call_unknown`. It is
     credited (`annotate_by_value`) only when its block carries no `assert` of a const false, the
     producer names `indirect-by-value`, every indirect escaping row of the member states an
     all-member, scan-complete enumeration whose target list is an UNAMBIGUOUS tiling of member
     names (the same set on every row), every target is declared at the call's own functy
     DEFINITION, and the call passes that functy's arity; then its block passes when SOME target
     returns (EvalIR's `callindirect` runs whichever function the `fnptr_` names, ANCHORS
     call_indirect_by_value), and the closure follows the targets. The trust sidecar's
     `shim-adapter` lane is what makes a closure shim's call match: the call passes the shim's
     own `((), (A..))` at the shim's signature. `borrow_mut` is imaged as `borrow` (a DECLARED
     shared arm, SHARED_IMAGE_ARMS: trust-ir's reference interpreter executes both in one arm).
     Decision D11: a `trust_rust.thread_local_addr` op is imaged, as the projector's `fn
     tls_input_image` says, only when the manifest's `tls_cells` rows CERTIFY its symbol.]
     [crystal D13, decision memo §18: the trust sidecar's `fnptr-thunks` lane types a thunked
     site's fn pointer `functy (A..) -> R` and supplies, per shim, an ABI THUNK `fn(A..) -> R`
     (`; #producer: "trust-abi-thunk"`, after the supplied intrinsic bodies) that calls the shim
     with `((), (A..))`; every value naming the shim at a functy names the thunk. A thunk must be
     EXACTLY that spread (`check_thunk`), only a producer naming the lane may carry one, and a site
     whose enumerated targets are shims is credited through their thunks when each thunk is at the
     call's functy definition and no `fndef<func.K>` anywhere names a shim K as a value; the
     closure then follows the thunks to the shims. A thunk is named by no call, so it is exempt
     from the called-declaration rule.]
     A call to a bodiless DECLARATION (the trust bridge's `premise-decls` lane lowers a
     FOREIGN premise as `call @decl` instead of `assert false; undef`) blocks its block the
     way a call to any non-returning body does: the declaration is not a body, it is never in
     the returning set, and it is never counted as a closure member. That is an EvalIR fact
     once the projector omits it (`ir_call_exec` is `stuck no_func`, ANCHORS
     "call_nonreturning"); a declared premise that RETURNS UNDER ITS CONTRACT is E-phase work
     and is not modelled, so today the site blocks exactly as the halting `assert false` it
     replaces did. The text must carry the members first and then only such declarations.
       unimaged_operand              a type / constant / global with no projector image
                                     (same standing as unimaged_kind: no image, no step)
     "Havoc undef" is a must-analysis: the ids an `undef` binds, closed under the
     EvalIR evaluators that PROPAGATE `undef_` (extractfield, ptr_data,
     ptr_metadata, ptr_from_parts' data, ptrtoptr/reify casts, a select of two
     undefs, a block parameter every incoming edge feeds an undef). Not modelled,
     so the bound stays a bound: arithmetic/icmp/overflow on undef, loads of
     never-written cells, and undefs passed into a callee's parameters.

 (c) VALUE HAVOCS: `undef`s used at least once as something OTHER than an
     `insertfield` aggregate base (the producer's aggregate-construction idiom).

READING THE M0 PRODUCER (C-M0, 2026-09-27; decision memo §21). Three reader repairs, none of
which moves a figure on a legacy artifact (`dump-link-O3-dp` and the d13 arms reproduce exactly):
  * SYMBOLS. A `fn` header's and a `global`'s name is read by `scripts/crystal_trust_ir_symbols.py`,
    the ONE symbol reader this script shares with link 3: trust-ir's WS4.3 printer (trust-ir
    `dcc5b9a3`) QUOTES a non-bare name, and a module mixing a quoted and a raw name is REFUSED.
    The instrument digest (`script_sha256`) covers that module too, so a change to it re-seats.
  * A `const`'s TYPE is read with the type grammar (`parse_ty_text`), never `^(\\S+|\\(.*?\\))`,
    which read the D3 arm's `const (i32, ptr) { 0, 0 }` as type `(i32,` and refused its exact
    two-lane ABI thunk (#2990).
  * D14 (memo §20), imaged by E5 (memo §23): the projector CERTIFIES every use of a vtable word --
    the metadata of a vtable-carrying fat pointer, followed through copy, a thin-to-thin cast and a
    byte gep of constant indices -- and refuses the body at the first use it does not certify
    (`fn d14_vtable_certify`); certified are a `load usize` of the size (+8) or align (+16) slot and
    the unchanged word as a new trait object's metadata. The model marks exactly that first use
    (`annotate_d14`, every rule DERIVED from the projector's functions). E5 also images the three
    kinds themselves (`container_len`, `container_vtable`, `dyn.N`: `fn ty`'s FatPtr arms, derived
    like every other type), and refuses a non-canonical metadata type (`fn check_metadata_ty`) and a
    constant at those kinds -- both modelled in `unimaged_operand` -- so the refused-body sets move by
    exactly the bodies whose only refusals were those kinds or D14's read.

RECONCILIATION with the l4 review's figures is part of every report: the
review's own rule (insertfield on an `undef`, matched with `insertfield \\S+`,
GREATEST fixpoint) is re-run literally, then a ladder adds one correction or
rule family at a time up to the gated model, so every difference between the
review's number and this one is attributed to a named step; a leave-one-out
table gives each family's weight in the gated model; and the review's
value-havoc rule is re-run literally beside the corrected count, split into
the parts that differ. A last, NOT gated, rung treats a body the projector
refuses as absent (its every block blocked). Each non-returning target carries
its blocked frontier and one chain of first blockers down to a local fault.

RATCHET. Every gated metric is a BAD count (lower is better). Against the
committed baseline (`data/crystal_link4_executability_baseline.json`):
  * any metric HIGHER than baseline                          -> exit 1 REGRESSION
  * same measurement IDENTITY (artifact digests + derived semantics digest +
    script digest) and any metric DIFFERENT from baseline     -> exit 1: the
    baseline claims a state its own artifact does not support (hand-edited)
  * the baseline's payload digest does not match its payload  -> exit 2 (tampered)
  * any metric LOWER with a changed identity                  -> exit 0, "rebase"
--rebase --reason TEXT rewrites the baseline only when the ARTIFACT changed, no
metric is worse and one is better (or every metric is equal: a re-pin). A lower
count on the SAME artifact is the instrument's doing, never the artifact's, so
--rebase refuses it. --reseat --reason TEXT is the one way to move a baseline
over an instrument change (this script or the EvalIR semantics / projector it
derives), up or down, and the one way to change the metric SET: the ARTIFACT
digests must equal the baseline's; it is recorded in the history with its reason.

FAIL-CLOSED (exit 2, never a count of zero): a missing or unreadable input; an
unknown manifest schema; a manifest missing `members`, `lowering`, `escaping`,
`artifacts` or `artifacts.text_bytes`; a v3 manifest whose `fuel`,
`fuel_exhausted`, a member's `mir_digest` or a call row's `bb` is missing or
malformed; `lowering` other than "ok"; a text whose
byte size is not the manifest's `text_bytes` (truncation); a `fn` with no
closing brace; a block with no terminator or a terminator mid-block; an
instruction whose shape does not parse; an unknown mnemonic or top-level form;
a function or global id out of range; a text/manifest join mismatch (count, id
or name); a bodiless member, a body past the members, or a declaration that is not
an `{extern#N}` foreign item, is declared twice, is called by no member, or is
called from a member whose manifest rows do not name it; IR and manifest call edges that disagree; a target root that is
absent or ambiguous; an IRInst set that disagrees between its sources; a
projector arm onto no constructor; a missing ANCHOR; an operand (type,
constant, global or type-table row) the printer grammar does not produce; a
projector arm that images a field the text model does not read; a moved
projector global rule; a baseline that is
missing, malformed, re-digested by hand, inconsistent with its own last history
entry, or names a different metric set; any internal error.

Exit codes: 0 pass, 1 fail (regression / baseline better than its artifact /
refused rebase), 2 refusal (malformed input, stale semantics, bad invocation).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys
import tempfile
from collections import Counter, deque

if os.path.dirname(os.path.abspath(__file__)) not in sys.path:
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
# The ONE reader of trust-ir's definition-site symbols (quoted since WS4.3), shared with link 3.
import crystal_trust_ir_symbols as tir_symbols  # noqa: E402

SCHEMA = "crystal-link4-executability/v1"
BASELINE_SCHEMA = "crystal-link4-executability-baseline/v1"
# Keyed on the manifest's own `schema` field. v3 (trust callee_sidecar.rs, 2026-09-24) adds a
# `bb` on every call row, a `mir_digest` on every member and the top-level `fuel` /
# `fuel_exhausted`; v2 stays readable for the artifacts cut before it. A manifest that CLAIMS
# v3 and lacks one of those, or carries it malformed, is REFUSED (`check_v3_fields`). This
# instrument validates them and reads none of them, so a v2 and a v3 manifest of one bundle
# measure identically (self-test arm "manifest v3").
MANIFEST_SCHEMA_V3 = "trust-ir-callee-sidecar-v3"
KNOWN_MANIFEST_SCHEMAS = ("trust-ir-callee-sidecar-v2", MANIFEST_SCHEMA_V3)
# `ProofDigest`'s display form; the all-zero digest is Trust's "no digest" value (and the
# placeholder its own layout fixture carries), so it is refused as a member's digest.
MIR_DIGEST_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
ZERO_MIR_DIGEST = "sha256:" + "0" * 64
TEXT_HEADER = "; TrustIr text format v1"
CRATE = "clean_kernel"
TARGETS = ("infer_type_fast", "infer_type", "tick_heartbeat")
TARGET_PREFIX = "clean_kernel::tc::"
# `usize`/`isize` are target-dependent; the projector refuses them unless a
# width is STATED, and the crystal lane states 64 (scripts/crystal_lzd_project.sh
# `--usize-bits 64`, the aarch64-apple-darwin target). Recorded in every report.
USIZE_BITS = 64

EXIT_PASS, EXIT_FAIL, EXIT_REFUSED = 0, 1, 2

SCRIPTS_DIR = os.path.dirname(os.path.abspath(__file__))
# Read by check_gate_registry.py (PINNED_INPUTS_MARKER): `--pinned-inputs` prints the first-party
# modules this script executes besides itself (derived from its imports: the symbol reader and
# crystal_a0_census's comment lexer), and its registry row pins them.
ANSWERS_PINNED_INPUTS = True
REPO_ROOT = os.path.dirname(SCRIPTS_DIR)
DEFAULT_BASELINE = os.path.join("data", "crystal_link4_executability_baseline.json")

SEMANTICS_SOURCES = {
    "syntax": "crates/clean-verify/src/spec/core_spec/eval_ir_syntax.rs",
    "machine": "crates/clean-verify/src/spec/core_spec/eval_ir_machine.rs",
    "ops": "crates/clean-verify/src/spec/core_spec/eval_ir_ops.rs",
    "float_ops": "crates/clean-verify/src/spec/core_spec/eval_ir_float_ops.rs",
    "census": "crates/clean-verify/tests/eval_ir/census.rs",
    # The projector is ONE source file (its `the_projector_is_one_source_file` test pins that):
    # the operator alphabets are its inline `mod ops`, read out of this text by `_ops_module`.
    "projector": "scripts/crystal_a2_project/src/main.rs",
    # Crystal E3b: reader B (the in-tree TEXT reader) and the core shape table, read ONLY to
    # derive the PENDING-PIN image of `Constant::Uninit` (see `pending_const_images`).
    "reader_b": "crates/clean-verify/src/ir_mint/emitted.rs",
    "core_shapes": "crates/clean-verify/src/ir_mint/shape.rs",
}
LEAN_SOURCES = ("syntax", "machine", "ops", "float_ops")


class Refusal(Exception):
    """Fail-closed: an input this script cannot fully account for (exit 2)."""


# ---------------------------------------------------------------------------
# The trust-ir text printer, transcribed: mnemonic -> trust_ir::Inst variant.
# Source: trust-ir crates/trust-ir/src/display.rs `write_inst` and the Display
# impls of BinOp/UnOp/OverflowOp/ICmpOp/FCmpOp/CastOp in inst.rs (read at
# trust wmain a5bcc7a688, 2026-09-23). An unlisted mnemonic is a REFUSAL.
# ---------------------------------------------------------------------------
BINOP_TEXT = {
    "add": "Add", "sub": "Sub", "mul": "Mul", "udiv": "UDiv", "sdiv": "SDiv",
    "urem": "URem", "srem": "SRem", "fadd": "FAdd", "fsub": "FSub",
    "fmul": "FMul", "fdiv": "FDiv", "frem": "FRem", "fmin": "FMin",
    "fmax": "FMax", "and": "And", "or": "Or", "xor": "Xor", "shl": "Shl",
    "lshr": "LShr", "ashr": "AShr", "band": "BAnd", "bor": "BOr", "bxor": "BXor",
}
UNOP_TEXT = {
    "neg": "Neg", "fneg": "FNeg", "fabs": "FAbs", "fsqrt": "FSqrt",
    "ffloor": "FFloor", "fceil": "FCeil", "ftrunc": "FTrunc", "not": "Not",
    "ctpop": "CtPop",
}
OVERFLOW_TEXT = {
    "add.overflow": "AddOverflow", "sub.overflow": "SubOverflow",
    "mul.overflow": "MulOverflow",
}
ICMP_TEXT = {
    "eq": "Eq", "ne": "Ne", "ult": "Ult", "ule": "Ule", "ugt": "Ugt",
    "uge": "Uge", "slt": "Slt", "sle": "Sle", "sgt": "Sgt", "sge": "Sge",
}
FCMP_TEXT = {
    "oeq": "OEq", "one": "ONe", "olt": "OLt", "ole": "OLe", "ogt": "OGt",
    "oge": "OGe", "ueq": "UEq", "une": "UNe", "ult": "ULt", "ule": "ULe",
    "ugt": "UGt", "uge": "UGe",
}
CAST_TEXT = {
    "trunc": "Trunc", "zext": "ZExt", "sext": "SExt", "fptrunc": "FPTrunc",
    "fpext": "FPExt", "fptoui": "FPToUI", "fptosi": "FPToSI", "uitofp": "UIToFP",
    "sitofp": "SIToFP", "ptrtoint": "PtrToInt", "inttoptr": "IntToPtr",
    "ptrtoptr": "PtrToPtr", "bitcast": "Bitcast", "transmute": "Transmute",
    "reify_fn_pointer": "ReifyFnPointer", "fptosi.sat": "FPToSISat",
    "fptoui.sat": "FPToUISat",
}
KIND_TEXT = {
    "load": "Load", "store": "Store", "drop": "Drop", "alloca": "Alloca",
    "heap_alloc": "HeapAlloc", "gep": "GEP", "ptr_data": "PtrData",
    "ptr_metadata": "PtrMetadata", "ptr_from_parts": "PtrFromParts",
    "atomic_load": "AtomicLoad", "atomic_store": "AtomicStore",
    "atomicrmw": "AtomicRMW", "cmpxchg": "CmpXchg", "fence": "Fence", "br": "Br",
    "condbr": "CondBr", "switch": "Switch", "call": "Call",
    "call_indirect": "CallIndirect", "ret": "Return", "extractfield": "ExtractField",
    "insertfield": "InsertField", "extractelement": "ExtractElement",
    "insertelement": "InsertElement", "const": "Const", "null": "NullPtr",
    "global_addr": "GlobalAddr", "undef": "Undef", "assume": "Assume",
    "assert": "Assert", "unreachable": "Unreachable", "copy": "Copy",
    "select": "Select", "borrow": "Borrow", "borrow_mut": "BorrowMut",
    "end_borrow": "EndBorrow", "retain": "Retain", "release": "Release",
    "is_unique": "IsUnique", "dealloc": "Dealloc", "open_frame": "OpenFrame",
    "bind_slot": "BindSlot", "load_slot": "LoadSlot", "close_frame": "CloseFrame",
    "coro_suspend": "CoroSuspend", "invoke": "Invoke", "landingpad": "LandingPad",
    "resume": "Resume", "dialect_op": "DialectOp", "seq_map_add_k": "SeqMapAddK",
    "seq_map_not": "SeqMapNot", "seq_map": "SeqMap", "icmp": "ICmp", "fcmp": "FCmp",
}
TERMINATORS = {"br", "condbr", "switch", "ret", "unreachable", "invoke", "resume"}
OPERATOR_FAMILIES = {
    # Inst variant -> (mnemonic table, projector `mod ops` function, Lean alphabet)
    "BinOp": (BINOP_TEXT, "binop", "IRBinOp"),
    "UnOp": (UNOP_TEXT, "unop", "IRUnOp"),
    "Overflow": (OVERFLOW_TEXT, "ovop", "IROverflowOp"),
    "ICmp": (ICMP_TEXT, "icmp", "IRICmpOp"),
    "FCmp": (FCMP_TEXT, "fcmp", "IRFCmpOp"),
    "Cast": (CAST_TEXT, "cast", "IRCastOp"),
}


def classify_mnemonic(word, rest):
    """(mnemonic, Inst variant, operator variant or None) for one instruction."""
    if word in BINOP_TEXT:
        return word, "BinOp", BINOP_TEXT[word]
    if word in UNOP_TEXT:
        return word, "UnOp", UNOP_TEXT[word]
    if word in OVERFLOW_TEXT:
        return word, "Overflow", OVERFLOW_TEXT[word]
    if word in CAST_TEXT:
        return word, "Cast", CAST_TEXT[word]
    if word in ("icmp", "fcmp"):
        table = ICMP_TEXT if word == "icmp" else FCMP_TEXT
        pred = rest.split(" ", 1)[0]
        if pred not in table:
            raise Refusal(f"unknown {word} predicate {pred!r}")
        return word, KIND_TEXT[word], table[pred]
    if word in KIND_TEXT:
        return word, KIND_TEXT[word], None
    raise Refusal(f"unknown trust-ir mnemonic {word!r}: extend the printer table "
                  f"(display.rs write_inst) before this artifact can be measured")


# ---------------------------------------------------------------------------
# Reading Rust sources: comments blanked by the tree's own nesting-aware lexer
# (`_blank_comments`, scripts/crystal_a0_census.py -- comment-only, string
# literals KEPT because the Lean spec source lives inside them), then only the
# FIRST string-literal argument of each `add_recursive_def(` / `add_inductive(`
# call is read. A comment, a doc string or a test literal can never satisfy an
# anchor or contribute a constructor.
# ---------------------------------------------------------------------------
def _lexer():
    sys.path.insert(0, SCRIPTS_DIR)
    try:
        from crystal_a0_census import _blank_comments  # noqa: PLC0415
    except Exception as exc:  # pragma: no cover - environment
        raise Refusal(f"cannot import the comment lexer _blank_comments: {exc}") from exc
    finally:
        sys.path.pop(0)
    return _blank_comments


def _read_literal(code, i):
    """Decode the Rust string literal at code[i]; return (text, end index)."""
    n = len(code)
    if code[i] == "r":
        j = i + 1
        fence = 0
        while j < n and code[j] == "#":
            fence += 1
            j += 1
        if j >= n or code[j] != '"':
            raise Refusal("malformed raw string literal in a semantics source")
        end = '"' + "#" * fence
        k = code.find(end, j + 1)
        if k < 0:
            raise Refusal("unterminated raw string literal in a semantics source")
        return code[j + 1:k], k + len(end)
    if code[i] != '"':
        raise Refusal("expected a string literal in a semantics source")
    j = i + 1
    out = []
    simple = {"n": "\n", "t": "\t", "r": "\r", "\\": "\\", '"': '"', "'": "'", "0": "\0"}
    while j < n:
        c = code[j]
        if c == "\\":
            d = code[j + 1:j + 2]
            if d == "\n":
                j += 2
                while j < n and code[j] in " \t\r\n":
                    j += 1
                continue
            if d in simple:
                out.append(simple[d])
                j += 2
                continue
            if d == "u":
                k = code.find("}", j)
                out.append(chr(int(code[j + 3:k], 16)))
                j = k + 1
                continue
            raise Refusal(f"unsupported escape \\{d} in a semantics source")
        if c == '"':
            return "".join(out), j + 1
        out.append(c)
        j += 1
    raise Refusal("unterminated string literal in a semantics source")


def _skip_ws(code, i):
    while i < len(code) and code[i] in " \t\r\n":
        i += 1
    return i


def registered_lean(src, blank):
    """{name: Lean text} for every literal `add_recursive_def`/`add_inductive`."""
    code = blank(src)
    out = {}
    for m in re.finditer(r"\.add_(?:recursive_def|inductive)\s*\(", code):
        i = _skip_ws(code, m.end())
        if code.startswith("concat!(", i):
            i = _skip_ws(code, i + len("concat!("))
            parts = []
            while i < len(code) and code[i] != ")":
                text, i = _read_literal(code, i)
                parts.append(text)
                i = _skip_ws(code, i)
                if code[i:i + 1] == ",":
                    i = _skip_ws(code, i + 1)
            text = "".join(parts)
        elif code[i:i + 1] == '"' or code[i:i + 2] in ('r"', "r#"):
            text, i = _read_literal(code, i)
        else:
            continue  # a registration through a named constant (a witness)
        mm = re.match(r"(?:def|inductive|theorem)\s+([^\s(:]+)", text)
        if not mm:
            continue
        name = mm.group(1)
        if name in out:
            raise Refusal(f"Lean name {name} is registered twice in one source")
        out[name] = text
    return out


def _braced_body(code, start):
    """Text between the `{` at/after `start` and its matching `}` (literal-aware)."""
    i = code.find("{", start)
    if i < 0:
        raise Refusal("expected a braced body in a projector source")
    depth = 0
    j = i
    n = len(code)
    while j < n:
        c = code[j]
        if c == '"' or (c == "r" and code[j + 1:j + 2] in ('"', "#")
                        and not (code[j - 1:j].isalnum() or code[j - 1:j] == "_")):
            if c == "r" and code[j + 1:j + 2] == "#" and '"' not in code[j + 1:j + 8]:
                j += 1
                continue
            _, j = _read_literal(code, j)
            continue
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0:
                return code[i + 1:j]
        j += 1
    raise Refusal("unbalanced braces in a projector source")


def _literals_in(code):
    """Every normal string literal in a (comment-blanked) Rust fragment."""
    out = []
    i, n = 0, len(code)
    while i < n:
        if code[i] == '"':
            text, i = _read_literal(code, i)
            out.append(text)
        elif code[i] == "'" and code[i + 2:i + 3] == "'":
            i += 3  # a char literal such as '"' must not open a string
        else:
            i += 1
    return out


def inductive_ctors(lean, name):
    text = lean.get(name)
    if text is None:
        raise Refusal(f"`inductive {name}` is not registered in the EvalIR sources")
    lines = text.splitlines()
    if not lines or not lines[0].startswith(f"inductive {name} : Type"):
        raise Refusal(f"`inductive {name}` has an unexpected header")
    ctors = []
    for ln in lines[1:]:
        m = re.match(r"^\|\s*([A-Za-z_][A-Za-z0-9_]*)\s*:", ln)
        if not m:
            raise Refusal(f"`inductive {name}`: unparsed constructor line {ln!r}")
        ctors.append(m.group(1))
    if not ctors or len(ctors) != len(set(ctors)):
        raise Refusal(f"`inductive {name}`: empty or duplicated constructor list")
    return ctors


def _norm(s):
    return re.sub(r"\s+", " ", s).strip()


def _nat_value(s):
    """The Nat a shape-class arm denotes -- a decimal numeral (`10`) or a `Nat.succ (..)` tower
    over `Nat.zero` -- or None for anything else. The shape functions spell classes both ways
    (the appended IRTy arms of 2026-09-25 are numerals), so a class is compared by VALUE: two
    spellings of one Nat are one class, and an unreadable arm is never read as nonzero."""
    t = _norm(s)
    depth = 0
    while True:
        while t.startswith("(") and t.endswith(")"):
            t = t[1:-1].strip()
        if t.startswith("Nat.succ "):
            depth += 1
            t = t[len("Nat.succ "):].strip()
            continue
        if t == "Nat.zero":
            return depth
        if re.fullmatch(r"\d+", t):
            return depth + int(t)
        return None


def match_arms(text, scrut_type):
    """{constructor: rhs} of a `match v with | T.c ... => rhs` Lean def."""
    arms = {}
    for ln in text.splitlines()[1:]:
        m = re.match(rf"^\|\s*{re.escape(scrut_type)}\.([A-Za-z_0-9]+)\b[^=]*=>\s*(.*)$", ln)
        if m:
            arms[m.group(1)] = m.group(2).strip()
    return arms


# Every rule the analysis applies, pinned to the EvalIR text that makes it true.
# (def, fragment): the fragment must occur, whitespace-normalised, in that def's
# registered Lean text. ("undef_arm", def, verdict): the def is a `match` over
# IRScalar whose `undef_` arm FAULTS (ends the step) or PROPAGATES (value undef_).
ANCHORS = {
    "bind_result_halts_on_fault": [
        ("ir_bind_result", "(fun (o : IROutcome) => IRConfig.halted o) r"),
    ],
    "undef_binds_undef": [
        ("ir_exec", "| IRInst.undef t => ir_bind s rs IRScalar.undef_"),
    ],
    "unreachable": [
        ("ir_exec", "| IRInst.unreachable => IRConfig.halted (IROutcome.ub IRFault.unreachable)"),
    ],
    "assert_false": [
        ("ir_exec", "| IRInst.assert c => ir_assert_exec s (ir_getd s c)"),
        ("ir_assert_exec", "(fun (b : Bool) => ir_assert_b s b) (ir_as_bool c)"),
        ("ir_assert_b", "Bool.rec (fun (_ : Bool) => IRConfig) (IRConfig.halted (IROutcome.ub "
                        "IRFault.assert_failed)) (ir_advance s) b"),
        ("ir_const_eval", "| IRConst.bool_ b => IRStepResult.value (IRScalar.bool_ b)"),
    ],
    "undef.condbr.cond": [
        ("ir_exec", "| IRInst.condbr c tt targs et eargs => ir_condbr_exec m s (ir_getd s c) "
                    "tt targs et eargs"),
        ("ir_condbr_exec", "IROption.rec Bool (fun (_ : IROption Bool) => IRConfig) (IRConfig.halted "
                           "(IROutcome.type_error IRFault.not_bool)) (fun (b : Bool) => "
                           "ir_condbr_b m s tt targs et eargs b) (ir_as_bool c)"),
        ("undef_arm", "ir_as_bool", "none"),
    ],
    "undef.switch.selector": [
        ("ir_exec", "| IRInst.switch v dflt dargs cases exh => ir_switch_exec m s (ir_getd s v) "
                    "dflt dargs cases"),
        ("ir_switch_exec", "IROption.rec Nat (fun (_ : IROption Nat) => IRConfig) (IRConfig.halted "
                           "(IROutcome.type_error IRFault.not_int)) (fun (n : Nat) => "
                           "ir_switch_n m s dflt dargs cases n) (ir_as_int v)"),
        ("undef_arm", "ir_as_int", "none"),
    ],
    "undef.select.cond": [
        ("ir_exec", "| IRInst.select t c a b => ir_bind_result s rs (ir_select_eval (ir_getd s c) "
                    "(ir_getd s a) (ir_getd s b))"),
        ("ir_select_eval", "IROption.rec Bool (fun (_ : IROption Bool) => IRStepResult) "
                           "(IRStepResult.fault (IROutcome.type_error IRFault.not_bool))"),
        ("ir_select_eval", "(IRStepResult.value b) (IRStepResult.value a) x) (ir_as_bool c)"),
        ("undef_arm", "ir_as_bool", "none"),
    ],
    "undef.assert.cond": [
        ("ir_exec", "| IRInst.assert c => ir_assert_exec s (ir_getd s c)"),
        ("ir_assert_exec", "IROption.rec Bool (fun (_ : IROption Bool) => IRConfig) (IRConfig.halted "
                           "(IROutcome.type_error IRFault.not_bool)) (fun (b : Bool) => "
                           "ir_assert_b s b) (ir_as_bool c)"),
        ("undef_arm", "ir_as_bool", "none"),
    ],
    "undef.insertfield.aggregate": [
        ("ir_exec", "| IRInst.insertfield t a k v => ir_bind_result s rs (ir_insert_field "
                    "(ir_getd s a) k (ir_getd s v))"),
        ("ir_insert_field", "def ir_insert_field (a : IRScalar) (k : Nat) (v : IRScalar) : "
                            "IRStepResult := match a with"),
        ("undef_arm", "ir_insert_field", "fault"),
    ],
    "undef.load.ptr": [
        ("ir_exec", "| IRInst.load t p vol => ir_bind_result s rs (ir_load_view (ir_mod_encs m) t "
                    "(ir_load_eval s (ir_getd s p)))"),
        ("ir_load_eval", "def ir_load_eval (s : IRMachine) (p : IRScalar) : IRStepResult := "
                         "ir_load_at (ir_mach_mem s) p"),
        ("ir_load_at", "def ir_load_at (mem : IRList IRMemSlot) (p : IRScalar) : IRStepResult := "
                       "match p with"),
        ("undef_arm", "ir_load_at", "fault"),
        ("ir_load_view", "IROption.rec IREnc (fun (_ : IROption IREnc) => IRStepResult) r "
                         "(fun (e : IREnc) => ir_view_result encs e r)"),
        ("ir_view_result", "| IRStepResult.fault o => IRStepResult.fault o"),
    ],
    "undef.store.ptr": [
        ("ir_exec", "| IRInst.store t p v vol => ir_store_exec s (ir_getd s p) (ir_getd s v)"),
        ("ir_store_exec", "def ir_store_exec (s : IRMachine) (p : IRScalar) (v : IRScalar) : "
                          "IRConfig := match p with"),
        ("undef_arm", "ir_store_exec", "fault"),
    ],
    "undef.gep.base": [
        ("ir_exec", "| IRInst.gep t b idxs inb => ir_bind_result s rs (ir_gep_eval (ir_getd s b) "
                    "(ir_resolve s idxs))"),
        ("ir_gep_eval", "(IRStepResult.fault (IROutcome.type_error IRFault.not_int)) "
                        "(fun (off : Nat) => ir_gep_base base off) (ir_sum_idx idxs)"),
        ("ir_gep_base", "def ir_gep_base (base : IRScalar) (off : Nat) : IRStepResult := "
                        "match base with"),
        ("undef_arm", "ir_gep_base", "fault"),
    ],
    # A gep INDEX (2026-09-24, crystal E3): `ir_gep_eval` sums its indices through `ir_as_int`,
    # whose `undef_` arm is `none`, and `ir_opt_add` propagates a `none`, so ONE undef index
    # makes the whole gep `type_error not_int`. The Lever-A offset GEPs index with exactly such
    # an `undef u64`. Without this rule a body whose seed faults are lifted (E3's typed seeds)
    # reads as returning while its next instruction faults.
    "undef.gep.index": [
        ("ir_exec", "| IRInst.gep t b idxs inb => ir_bind_result s rs (ir_gep_eval (ir_getd s b) "
                    "(ir_resolve s idxs))"),
        ("ir_resolve", "IRList.cons IRScalar (ir_getd s i) ih) ids"),
        ("ir_gep_eval", "(IRStepResult.fault (IROutcome.type_error IRFault.not_int)) "
                        "(fun (off : Nat) => ir_gep_base base off) (ir_sum_idx idxs)"),
        ("ir_sum_idx", "(fun (x : IRScalar) (_ : IRList IRScalar) (ih : IROption Nat) => "
                       "ir_opt_add (ir_as_int x) ih) l"),
        ("ir_opt_add", "IROption.rec Nat (fun (_ : IROption Nat) => IROption Nat) "
                       "(IROption.none Nat) (fun (x : Nat) => IROption.rec Nat (fun (_ : "
                       "IROption Nat) => IROption Nat) (IROption.none Nat) (fun (y : Nat) => "
                       "IROption.some Nat (Nat.add x y)) b) a"),
        ("undef_arm", "ir_as_int", "none"),
    ],
    "undef.borrow.ptr": [
        ("ir_exec", "| IRInst.borrow p => ir_bind_result s rs (ir_borrow_eval (ir_mach_mem s) "
                    "(ir_getd s p))"),
        ("ir_borrow_eval", "def ir_borrow_eval (mem : IRList IRMemSlot) (v : IRScalar) : "
                           "IRStepResult := match v with"),
        ("undef_arm", "ir_borrow_eval", "fault"),
    ],
    "undef.call_indirect.callee": [
        ("ir_exec", "| IRInst.callindirect cid sig args cc => ir_callind_exec m s rs "
                    "(ir_getd s cid) args"),
        ("undef_arm", "ir_callind_exec", "fault"),
    ],
    "undef.copy.operand": [
        ("ir_exec", "| IRInst.copy t a => ir_bind_result s rs (ir_copy_eval t (ir_getd s a))"),
        ("ir_copy_eval", "Bool.rec (fun (_ : Bool) => IRStepResult) (IRStepResult.fault "
                         "(IROutcome.type_error (ir_ty_fault t))) (IRStepResult.value v) "
                         "(ir_nat_eqb (ir_ty_shape t) (ir_scalar_shape v))"),
        ("undef_arm", "ir_scalar_shape", "zero"),
        ("shape_never_zero", "ir_ty_shape", None),
    ],
    "propagate.extractfield": [
        ("ir_exec", "| IRInst.extractfield t a k => ir_bind_result s rs (ir_ef_at (ir_getd s a) k)"),
        ("undef_arm", "ir_ef_at", "propagate"),
    ],
    "propagate.ptr_data": [
        ("ir_exec", "| IRInst.ptrdata t p => ir_bind_result s rs (ir_ptrdata_eval (ir_getd s p))"),
        ("undef_arm", "ir_ptrdata_eval", "propagate"),
    ],
    "propagate.ptr_metadata": [
        ("ir_exec", "| IRInst.ptrmetadata pt mt p => ir_bind_result s rs "
                    "(ir_ptrmeta_eval mt (ir_getd s p))"),
        ("undef_arm", "ir_ptrmeta_eval", "propagate"),
    ],
    "propagate.ptr_from_parts": [
        ("ir_exec", "| IRInst.ptrfromparts pt mt d md => ir_bind_result s rs "
                    "(ir_ptrparts_eval (ir_getd s d) (ir_getd s md))"),
        ("undef_arm", "ir_ptrparts_eval", "propagate"),
    ],
    "propagate.cast": [
        ("ir_exec", "| IRInst.cast op sr ds a => ir_bind_result s rs "
                    "(ir_cast_eval op sr ds (ir_getd s a))"),
        ("ir_cast_eval", "| IRCastOp.ptrtoptr => ir_ptrcast_eval a"),
        ("ir_cast_eval", "| IRCastOp.reifyfnpointer => ir_reifyfn_eval a"),
        ("undef_arm", "ir_ptrcast_eval", "propagate"),
        ("undef_arm", "ir_reifyfn_eval", "propagate"),
    ],
    "propagate.select": [
        ("ir_select_eval", "(IRStepResult.value b) (IRStepResult.value a) x) (ir_as_bool c)"),
    ],
    "cast_unmodelled": [
        ("ir_exec", "| IRInst.cast op sr ds a => ir_bind_result s rs "
                    "(ir_cast_eval op sr ds (ir_getd s a))"),
        ("ir_exec", "| IRInst.binop op t a b => ir_bind_result s rs "
                    "(ir_binop_eval op t (ir_getd s a) (ir_getd s b))"),
        ("ir_width_fault", "def ir_width_fault : IRStepResult := IRStepResult.fault "
                           "(IROutcome.unmodelled IRFault.width_bounded)"),
        ("ir_float_fault", "def ir_float_fault : IRStepResult := IRStepResult.fault "
                           "(IROutcome.unmodelled IRFault.float_domain)"),
        ("ir_cast_eval", "| IRCastOp.bitcast => ir_bitcast_eval src dst a"),
        ("ir_bitcast_eval", "IROption.rec Nat (fun (_ : IROption Nat) => IRStepResult) "
                            "ir_width_fault (fun (sw : Nat) => IROption.rec Nat (fun (_ : "
                            "IROption Nat) => IRStepResult) ir_width_fault (fun (dw : Nat) => "
                            "ir_bitcast_int sw dw a) (ir_ty_int_width dst)) (ir_ty_int_width src)"),
        ("ir_bitcast_int", "Bool.rec (fun (_ : Bool) => IRStepResult) ir_width_fault"),
        ("ir_bitcast_int", "(ir_nat_eqb sw dw)"),
        ("int_width_arms", "ir_ty_int_width", None),
    ],
    # Crystal E3b: what EvalIR does with an UNWRITTEN aggregate lane, imaged `IRConst.undef_`:
    # the constant materialises the lane as `IRScalar.undef_` (ir_const_value's fifth minor)
    # inside an `aggv`, `insertfield` REPLACES a lane whatever it holds, and `extractfield`
    # hands the lane back (a later use of `undef_` is the fault). Read by the PENDING-PIN image
    # only (`pending_const_images`), never by a gated rule.
    "uninit.lane": [
        ("ir_const_eval", "| IRConst.undef_ => IRStepResult.value IRScalar.undef_"),
        ("ir_const_eval", "| IRConst.aggv sp => ir_const_agg_eval t sp"),
        ("ir_const_agg_eval", "(IRStepResult.value (IRScalar.aggv (ir_const_value sp)))"),
        ("ir_const_value", "IRScalar.unit_ IRScalar.nullptr_ IRScalar.undef_ "
                           "(fun (n : Nat) => IRScalar.float_ n)"),
        ("ir_insert_field", "| IRScalar.aggv sp => ir_if_at sp k v"),
        ("ir_if_at", "(IRStepResult.value (IRScalar.aggv (ir_vals_set sp k v)))"),
        ("ir_ef_at", "| IRScalar.aggv sp => ir_field_result (ir_vals_get sp k)"),
    ],
    "call_unknown_policy": [],  # a policy, not an EvalIR fact: nothing to anchor
    # Crystal D1: a `call_indirect` DISPATCHED BY VALUE (no marker; an exact, complete,
    # all-member dispatch set; every target's signature equal to the call's) runs whichever
    # target the pointer names: EvalIR's `callindirect` ignores its signature and calls the
    # `fnptr_` function with the call's own arguments, binding them positionally.
    "call_indirect_by_value": [
        ("ir_exec", "| IRInst.callindirect cid sig args cc => ir_callind_exec m s rs "
                    "(ir_getd s cid) args"),
        ("ir_callind_exec", "| IRScalar.fnptr_ f => ir_call_exec m s rs f args"),
        ("ir_call_exec", "(fun (f : IRFunc) => ir_push s rs f (ir_resolve s args))"),
    ],
    # Crystal D1: a `call_indirect` whose callee is the result of a `copy` at a NON-function type
    # never dispatches. `copy t` binds its value only when the value's SHAPE CLASS is t's; the
    # function class is `func_`'s alone, and `callindirect` runs only an `fnptr_` -- every other
    # value halts. So such a copy, or the call it feeds, definitely faults: the fn pointer the
    # const image supplies is an `fnptr_`, and `LocalKey::try_with` copies it at `ptr`.
    "callee_not_fnptr": [
        ("ir_exec", "| IRInst.copy t a => ir_bind_result s rs (ir_copy_eval t (ir_getd s a))"),
        ("ir_copy_eval", "Bool.rec (fun (_ : Bool) => IRStepResult) (IRStepResult.fault "
                         "(IROutcome.type_error (ir_ty_fault t))) (IRStepResult.value v) "
                         "(ir_nat_eqb (ir_ty_shape t) (ir_scalar_shape v))"),
        ("func_class_unique", None, None),
        ("callind_only_fnptr", "ir_callind_exec", None),
    ],
    # Crystal D11: the TLS input image is a `globaladdr` of the cell, whose value is the
    # cell's address (the global's id) whenever the module declares the global.
    "tls_input_globaladdr": [
        ("ir_exec", "| IRInst.globaladdr g => ir_bind_result s rs (ir_globaladdr_eval m g)"),
        ("ir_globaladdr_eval", "(fun (_ : IRGlobal) => IRStepResult.value (IRScalar.ptr_ g))"),
    ],
    "call_nonreturning": [
        ("ir_exec", "| IRInst.call fid args => ir_call_exec m s rs fid args"),
        ("ir_call_exec", "(IRConfig.halted (IROutcome.stuck IRFault.no_func)) "
                         "(fun (f : IRFunc) => ir_push s rs f (ir_resolve s args))"),
    ],
}

# Which ANCHORS groups each rule family rests on.
FAMILY_ANCHORS = {
    "unreachable": ["unreachable"],
    "assert_false": ["assert_false"],
    "undef_branch": ["undef.condbr.cond", "undef.switch.selector", "undef.select.cond",
                     "undef.assert.cond", "undef_binds_undef", "bind_result_halts_on_fault"],
    "undef_insertfield": ["undef.insertfield.aggregate", "undef_binds_undef",
                          "bind_result_halts_on_fault"],
    "undef_other": ["undef.load.ptr", "undef.store.ptr",
                    "undef.gep.base", "undef.gep.index", "undef.borrow.ptr",
                    "undef.call_indirect.callee",
                    "undef.copy.operand", "undef_binds_undef", "bind_result_halts_on_fault"],
    "propagate": ["propagate.extractfield", "propagate.ptr_data", "propagate.ptr_metadata",
                  "propagate.ptr_from_parts", "propagate.cast", "propagate.select"],
    "cast_unmodelled": ["cast_unmodelled", "bind_result_halts_on_fault"],
    "call_nonreturning": ["call_nonreturning"],
    "call_indirect_by_value": ["call_indirect_by_value", "call_nonreturning"],
    "callee_not_fnptr": ["callee_not_fnptr", "bind_result_halts_on_fault"],
    "tls_input": ["tls_input_globaladdr"],
}

# The undef-operand positions each family covers: (mnemonic, role).
UNDEF_BRANCH_ROLES = {("condbr", "cond"), ("switch", "selector"), ("select", "cond"),
                      ("assert", "cond")}
UNDEF_OTHER_ROLES = {("load", "ptr"), ("store", "ptr"), ("gep", "base"), ("borrow", "ptr"),
                     # Crystal D1: `borrow_mut` projects to `borrow` (one arm), so the same fault.
                     ("borrow_mut", "ptr"),
                     ("call_indirect", "callee"), ("copy", "operand"),
                     # Crystal D10: an imaged atomic's pointer is its image's load/store base.
                     ("atomic_load", "ptr"), ("atomic_store", "ptr"), ("atomicrmw", "ptr"),
                     ("cmpxchg", "ptr")}


def _undef_verdict(rhs):
    r = _norm(rhs)
    if r.startswith(("IRStepResult.fault (", "IRConfig.halted (")):
        return "fault"
    if r == "IRStepResult.value IRScalar.undef_" or r == "IRScalar.undef_":
        return "propagate"
    if r.startswith("IROption.none "):
        return "none"
    if r == "Nat.zero":
        return "zero"
    return "other:" + r


# Crystal D10 (decision memo §15): the projector images a NATIVE atomic by EXPANSION into existing
# IRInst nodes (`fn seq_atomic_image`), exact under the ENVIRONMENT premise SEQ. The expansion is
# DERIVED from that function, never typed here: its arms are the trust_ir::Inst variants it
# images, the `(load`/`(store`/`(binop`/`(icmp`/`(select` spellings its nodes use must be IRInst
# constructors (and its binop names operators `mod ops` images), and its inner `match op` lists the
# AtomicRMW ops it computes. An arm it refuses (`return Err(`) images nothing.
SEQ_VARIANTS = ("AtomicLoad", "AtomicStore", "AtomicRMW", "CmpXchg", "Fence")


def derive_seq_atomic_image(proj, irinst, op_image):
    at = proj.find("fn seq_atomic_image(")
    if at < 0:
        return {}
    body = _braced_body(proj, at)
    # The fall-through arm: every variant that is NOT a native atomic, named (no wildcard -- the
    # projector's crate forbids one), handing the node back to `fn inst` with `return Ok(None)`.
    arm_pat = r"Inst::[A-Za-z]+\s*(?:\{[^{}]*\}|\([^()]*\))?"
    stop = re.search(rf"((?:{arm_pat}\s*\|\s*)*{arm_pat})\s*=>\s*return\s+Ok\(None\)", body)
    if stop is None:
        raise Refusal("projector `fn seq_atomic_image`: its `=> return Ok(None)` fall-through not found")
    passed = set(re.findall(r"Inst::([A-Za-z]+)", stop.group(1)))
    if passed & set(SEQ_VARIANTS):
        raise Refusal(f"projector `fn seq_atomic_image` hands native atomics "
                      f"{sorted(passed & set(SEQ_VARIANTS))} back to `fn inst`")
    arms = [a for a in re.finditer(r"Inst::([A-Za-z]+)\s*(?:\{[^{}]*\})?\s*=>", body)
            if a.start() < stop.start()]
    if not arms:
        raise Refusal("projector `fn seq_atomic_image`: no arm before its fall-through")
    image = {}
    for n, am in enumerate(arms):
        v = am.group(1)
        if v not in SEQ_VARIANTS:
            raise Refusal(f"projector `fn seq_atomic_image` images Inst::{v}, not a native atomic")
        if v in image:
            raise Refusal(f"projector `fn seq_atomic_image` has two arms for Inst::{v}")
        end = arms[n + 1].start() if n + 1 < len(arms) else stop.start()
        seg = body[am.end():end]
        ctors = set()
        for lit in _literals_in(seg):
            for w in re.findall(r"\((load|store|binop|icmp|select|node|results)\b", lit):
                if w in ("node", "results"):
                    continue
                if w not in irinst:
                    raise Refusal(f"`fn seq_atomic_image` Inst::{v} emits `({w}`, no IRInst constructor")
                ctors.add(w)
        entry = {"ctors": sorted(ctors)}
        if v == "AtomicRMW":
            ops = {}
            for om in re.finditer(r"\bA::([A-Za-z]+)\s*=>\s*(None|Some\(\"([a-z_]+)\"\))", seg):
                ops[om.group(1)] = om.group(3) or "xchg"
            # `mod ops`'s image of a BinOp is its Lean constructor; the core text spells it without
            # the trailing underscore a keyword-named constructor carries (`and` -> `and_`).
            binop_ctors = set(op_image["BinOp"].values())
            for rmw, b in ops.items():
                if b != "xchg" and b not in binop_ctors and b + "_" not in binop_ctors:
                    raise Refusal(f"`fn seq_atomic_image` computes atomicrmw {rmw} with binop `{b}`, "
                                  f"which `mod ops` does not image")
            if not ops:
                raise Refusal("`fn seq_atomic_image` AtomicRMW arm names no imaged op")
            entry["rmw_ops"] = {k.lower(): v_ for k, v_ in sorted(ops.items())}
        image[v] = entry
    return dict(sorted(image.items()))


# Crystal D11 (decision memo §17): the projector images a `trust_rust.thread_local_addr` op as the
# `globaladdr` of an INPUT cell (`fn tls_input_image`), only for a symbol the callee sidecar's
# manifest certifies (`tls_cells`). DERIVED from that function, never typed here: it must decode
# the op with trust-ir's own `decode_thread_local_addr`, gate on the certificate
# (`self.tls_certified.contains_key(`), emit exactly one `(globaladdr` node, and be called from
# `project_one`; `globaladdr` must be an IRInst constructor. Absent, nothing is imaged.
TLS_OP_TEXT = ('trust_rust.thread_local_addr() -> ptr [schema=str:"trust-rust.thread-local-addr/v1"] '
               '[symbol=str:"')


def derive_tls_input_image(proj, irinst):
    at = proj.find("fn tls_input_image(")
    if at < 0:
        return {}
    body = _braced_body(proj, at)
    for need in ("trust_ir::dialect::trust_rust::decode_thread_local_addr(",
                 "self.tls_certified.contains_key("):
        if need not in body:
            raise Refusal(f"projector `fn tls_input_image` does not contain {need!r}")
    ctors = set()
    for lit in _literals_in(body):
        for w in re.findall(r"\((globaladdr|load|store|binop|const|node|results)\b", lit):
            if w in ("node", "results"):
                continue
            if w not in irinst:
                raise Refusal(f"`fn tls_input_image` emits `({w}`, no IRInst constructor")
            ctors.add(w)
    if ctors != {"globaladdr"}:
        raise Refusal(f"`fn tls_input_image` emits {sorted(ctors)}, expected exactly (globaladdr")
    po = proj.find("fn project_one(")
    if po < 0 or "self.tls_input_image(" not in _braced_body(proj, po):
        raise Refusal("projector `fn project_one` does not call `self.tls_input_image(`")
    return {"op": "trust_rust.thread_local_addr", "schema": "trust-rust.thread-local-addr/v1",
            "ctor": "globaladdr", "certificate": "a manifest `tls_cells` row with certified=true"}


def _called_from_project_one(proj, call):
    po = proj.find("fn project_one(")
    return po >= 0 and call in _braced_body(proj, po)


def derive_ptr_bitcast_image(proj, irinst):
    """Crystal D12 (decision memo §18): the projector images `bitcast ptr -> ptr` as `copy (ptr)`
    (`fn ptr_bitcast_identity_image`) under its opt-in `--ptr-bitcast-identity`, which this model
    assumes passed -- as it assumes `--usize-bits 64` and `--tls-cells <manifest>` (the image is
    off by default only so that committed chains re-project byte-identical). DERIVED: the function
    must be gated on that flag, match exactly that cast, emit one `(copy (ptr)` node and be called
    from `project_one`; `copy` must be an IRInst constructor. Absent, a pointer bitcast keeps the
    `cast_unmodelled` rule."""
    at = proj.find("fn ptr_bitcast_identity_image(")
    if at < 0:
        return {}
    body = _norm(_braced_body(proj, at))
    if _norm("if !self.ptr_bitcast_identity { return Ok(None); }") not in body \
            or '"--ptr-bitcast-identity"' not in proj:
        raise Refusal("projector `fn ptr_bitcast_identity_image` is not gated on `--ptr-bitcast-identity`")
    # Since the 2026-09-27 merge of origin/main (its lint r11 refuses the `let .. else` over a
    # nested `Cast { op: Bitcast, src_ty: Ty::Ptr, dst_ty: Ty::Ptr, .. }` pattern this was): the
    # cast's fields bound whole, then ONE guard naming all three, pinned whole.
    # Since the train-clean-1 merge (2026-10-14; main's lint r11b refuses the `!=` comparisons
    # this guard was) the three tests are named matches in two free functions, each pinned by its
    # one `=> true` arm.
    for need in ("Inst::Cast { op, src_ty, dst_ty, operand, } => (op, src_ty, dst_ty, operand),",
                 "if !(cast_is_bitcast(op) && ty_is_bare_ptr(src_ty) && ty_is_bare_ptr(dst_ty)) "
                 "{ return Ok(None); }"):
        if _norm(need) not in body:
            raise Refusal(f"projector `fn ptr_bitcast_identity_image` does not match {need!r}")
    for fn, need in (("fn cast_is_bitcast(", "CastOp::Bitcast => true,"),
                     ("fn ty_is_bare_ptr(", "Ty::Ptr => true,")):
        k = proj.find(fn)
        fbody = _norm(_braced_body(proj, k)) if k >= 0 else ""
        if _norm(need) not in fbody or fbody.count("=> true") != 1:
            raise Refusal(f"projector `{fn}` is missing or not exactly `{need}`")
    lits = _literals_in(_braced_body(proj, at))
    if not any(lit.startswith("(node (results {}) (copy (ptr) {}))") for lit in lits):
        raise Refusal("projector `fn ptr_bitcast_identity_image` does not emit `(copy (ptr)`")
    if "copy" not in irinst:
        raise Refusal("`copy` is not an IRInst constructor")
    if not _called_from_project_one(proj, "self.ptr_bitcast_identity_image("):
        raise Refusal("projector `fn project_one` does not call `self.ptr_bitcast_identity_image(`")
    return {"cast": "bitcast ptr -> ptr", "ctor": "copy", "ty": "ptr", "flag": "--ptr-bitcast-identity"}


def derive_negative_int_image(proj):
    """Crystal memo §18: the projector images a NEGATIVE `Constant::Int` at an integer type as its
    width-W bit pattern (`fn negative_int_const_image`). DERIVED: the integer types it takes are
    read off its width match; it must guard `*v >= 0`, mask the two's-complement carrier, emit
    `(const .. (int ..))` and be called from `project_one`. Absent, the negative constant keeps
    the `unimaged_operand` refusal."""
    at = proj.find("fn negative_int_const_image(")
    if at < 0:
        return {}
    raw = _braced_body(proj, at)
    body = _norm(raw)
    for need in ("value: Constant::Int(v),", "if *v >= 0 { return Ok(None); }",
                 "let pattern = (*v as u128) & mask;"):
        if _norm(need) not in body:
            raise Refusal(f"projector `fn negative_int_const_image` does not contain {need!r}")
    if not any("(const {t} (int {pattern})))" in lit for lit in _literals_in(raw)):
        raise Refusal("projector `fn negative_int_const_image` does not emit `(const {t} (int ..))`")
    # The width match's fall-through is NAMED, not `_` (the projector's crate forbids the wildcard
    # lints): every type with no integer width, listed, handed back with `return Ok(None)`. The
    # imaged types are the ones named in the arms BEFORE it. (Merge of crystal D1b onto the lane,
    # 2026-09-25: the D1b spelling `_ => return Ok(None),` does not compile under those lints.)
    wa = raw.find("let width: u32 = match ty")
    if wa < 0:
        raise Refusal("projector `fn negative_int_const_image`: its width match is not found")
    wbody = _braced_body(raw, wa)
    ty_arm = r"Ty::[A-Za-z0-9]+\s*(?:\([^()]*\))?"
    stop = re.search(rf"((?:{ty_arm}\s*\|\s*)*{ty_arm})\s*=>\s*return\s+Ok\(None\)", wbody)
    if stop is None:
        raise Refusal("projector `fn negative_int_const_image`: its width match's named "
                      "`=> return Ok(None)` fall-through is not found")
    tys = sorted(set(re.findall(r"Ty::([A-Z][A-Za-z0-9]*)", wbody[:stop.start()])))
    ints = {"I8", "I16", "I32", "I64", "I128", "U8", "U16", "U32", "U64", "U128", "Isize", "Usize"}
    if not tys or not set(tys) <= ints:
        raise Refusal(f"projector `fn negative_int_const_image` takes non-integer types {tys}")
    if not _called_from_project_one(proj, "self.negative_int_const_image("):
        raise Refusal("projector `fn project_one` does not call `self.negative_int_const_image(`")
    return {"const": "Int < 0", "image": "the width-W bit pattern", "types": tys}


def derive_ub_halt_image(proj, irinst):
    """Crystal memo §15 (lead's ruling on D10), executed in §18: the projector images the `assert`
    an undefined-behaviour halt obligation SITES as `unreachable` (`fn ub_halt_image`), keyed by
    the bridge's exact wording (`fn is_ub_halt_description`). DERIVED; absent, such an assert is
    the ordinary `assert_false` it looks like."""
    at = proj.find("fn ub_halt_image(")
    if at < 0:
        return {}
    raw = _braced_body(proj, at)
    if '"(node (results) (unreachable))"' not in raw:
        raise Refusal("projector `fn ub_halt_image` does not emit `(unreachable)`")
    # Since the train-clean-1 merge (2026-10-14) trust-ir's `Assert` carries a kind (v52) and a
    # site (v54); only a kindless, siteless assert -- the one `fn inst` images -- is a halt here.
    for need in ("Inst::Assert { cond, kind, site }",
                 "kind.is_unspecified() && site.is_none()",
                 "m.results.as_slice() == [*cond] && inst_is_const_bool_false(&m.inst)"):
        if _norm(need) not in _norm(raw):
            raise Refusal(f"projector `fn ub_halt_image` does not contain {need!r}")
    # The `const bool false` test, a named match since the train-clean-1 merge (lint r11b refuses
    # the `==` against a built `Inst::Const` it was).
    kf = proj.find("fn inst_is_const_bool_false(")
    fbody = _norm(_braced_body(proj, kf)) if kf >= 0 else ""
    for need in ("Inst::Const { ty, value } => {", "Ty::Bool => true,",
                 "Constant::Bool(b) => !*b,", "bool_ty && false_value"):
        if _norm(need) not in fbody:
            raise Refusal(f"projector `fn inst_is_const_bool_false` does not contain {need!r}")
    wd = proj.find("fn is_ub_halt_description(")
    if wd < 0 or UB_HALT_WORDING not in " ".join(_literals_in(_braced_body(proj, wd))):
        raise Refusal("projector `fn is_ub_halt_description` is missing or not the bridge's wording")
    if "unreachable" not in irinst:
        raise Refusal("`unreachable` is not an IRInst constructor")
    if not _called_from_project_one(proj, "self.ub_halt_image("):
        raise Refusal("projector `fn project_one` does not call `self.ub_halt_image(`")
    return {"site": "an undefined-behaviour halt obligation's sited assert", "ctor": "unreachable"}


def derive_d14_vtable_certify(proj):
    """Crystal D14, imaged by E5 (memo §23): the projector CERTIFIES every use a body makes of a
    VTABLE word and refuses the body, by name and before any per-node refusal, at the first use it
    does not certify (`fn d14_vtable_certify`, called from `fn project_one`). DERIVED: the seed
    kinds are the `=> true` arm of `fn carries_vtable`; the rest -- which pointers follow a seed,
    what a gep may add, which loads and which rebuild are certified, the 64-bit width -- must be the
    shapes those functions spell, or this refuses. Absent, no vtable use is so refused."""
    at = proj.find("fn d14_vtable_certify(")
    if at < 0:
        return {}
    for fn, needs in (
            ("fn d14_vtable_certify(", (
                "VtNode::Meta(Some(kind)) => carries_vtable(kind).then_some((res.0, 0)),",
                "Some((seed, gep_bytes(seed, off, pointee, indices, &consts)?))",
                "VtNode::Copy(operand) => derived.get(&operand).copied(),",
                "if usize_bits != Some(64) {",
                "if usize_word && (off == 8 || off == 16) {",
                "base == v && indices.iter().all(|ix| ix.0 != v)",
                "VtNode::Cast { ptr_to_ptr, .. } => ptr_to_ptr,",
                "} => carries_vtable(kind) && metadata == v && data != v && off == 0,")),
            ("fn gep_bytes(", ("VtTy::Byte => 1,", "VtTy::Thin | VtTy::Usize | VtTy::Other if c == 0 => 0,")),
            ("fn vt_ty(", ("Ty::I8 | Ty::U8 => VtTy::Byte,", "Ty::Usize => VtTy::Usize,",
                           "Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_) | Ty::Rc(_) => {")),
            ("fn is_ptr_identity_cast(", ("CastOp::Bitcast | CastOp::PtrToPtr => true,",)),
            ("fn const_int(", ("Constant::Int(v) => Some(*v),",))):
        k = proj.find(fn)
        if k < 0:
            raise Refusal(f"projector `fn d14_vtable_certify` without `{fn}`")
        raw = _norm(_braced_body(proj, k))
        for need in needs:
            if _norm(need) not in raw:
                raise Refusal(f"projector `{fn}` does not contain {need!r}")
    cv = proj.find("fn carries_vtable(")
    if cv < 0:
        raise Refusal("projector `fn d14_vtable_certify` without `fn carries_vtable`")
    kp = r"trust_ir::FatPtrKind::[A-Za-z]+(?:\s*\{\s*\.\.\s*\}|\([^()]*\))?"
    arm = re.search(rf"((?:{kp}\s*\|\s*)*{kp})\s*=>\s*true", _braced_body(proj, cv))
    if arm is None:
        raise Refusal("projector `fn carries_vtable` has no `=> true` arm")
    kinds = sorted(set(re.findall(r"FatPtrKind::([A-Za-z]+)", arm.group(1))))
    if not _called_from_project_one(proj, "d14_vtable_certify(f, self.usize_bits)"):
        raise Refusal("projector `fn project_one` does not call `d14_vtable_certify(f, self.usize_bits)`")
    return {"seed_kinds": kinds, "follows": ["gep", "copy", "cast"], "byte_pointees": ["I8", "U8"],
            "thin_ptr_tys": sorted(THIN_PTR_TYS), "load_ty": "Usize", "load_slots": [8, 16],
            "rebuild": "ptr_from_parts", "width": 64}


# Crystal E5 (memo §23): the projector's `fn check_metadata_ty` refuses a `ptr_metadata` /
# `ptr_from_parts` whose declared metadata type is not the pointer type's canonical one. The table
# is trust-ir's own (`PointerMetadataShape::metadata_ty` at the pinned 64-bit width), which the
# projector calls rather than restates; a thin pointer's canonical metadata type is `()`.
THIN_PTR_TYS = frozenset({"Ptr", "PtrConst", "PtrMut", "Ref", "RefMut", "Rc"})
CANONICAL_METADATA = {"Slice": "U64", "Str": "U64", "ContainerLen": "U64",
                      "TraitObject": "Ptr", "ContainerVtable": "Ptr"}


def derive_metadata_ty_check(proj):
    """Crystal E5: DERIVED from the projector -- both lane operations call `check_metadata_ty`, and
    it answers `kind.metadata_ty(bits)` for a fat kind and `()` for a thin pointer. Absent, no
    metadata type is refused."""
    k = proj.find("fn check_metadata_ty(")
    if k < 0:
        return {}
    raw = _norm(_braced_body(proj, k))
    # Since the train-clean-1 merge (2026-10-14; main's lint r11b refuses the `&canonical !=
    # metadata_ty` comparison) the pair is compared through `metadata_ty_key`, a named match.
    for need in ("kind.metadata_ty(bits)", "VtTy::Thin => Ty::Unit,",
                 "let canonical_key = metadata_ty_key(&canonical);",
                 "if canonical_key.is_none() || canonical_key != metadata_ty_key(metadata_ty) {"):
        if _norm(need) not in raw:
            raise Refusal(f"projector `fn check_metadata_ty` does not contain {need!r}")
    ib = _norm(_braced_body(proj, proj.find("fn inst(&mut self, i: &Inst) -> R<String>")))
    ops = [op for op in ("ptr_metadata", "ptr_from_parts")
           if _norm(f'self.check_metadata_ty("{op}", ptr_ty, metadata_ty)?;') in ib]
    if not ops:
        raise Refusal("projector `fn check_metadata_ty` is called by neither lane operation")
    return {"ops": ops, "canonical": dict(sorted(CANONICAL_METADATA.items())), "thin": "Unit"}


def derive_fat_const_refusal(proj):
    """Crystal E5: the fat kinds whose CONSTANT the projector refuses (its `Inst::Const` arm, the
    kinds before `return Err(`). Absent, none is refused."""
    ib = _braced_body(proj, proj.find("fn inst(&mut self, i: &Inst) -> R<String>"))
    m = re.search(r"if let Some\(kind\) = fat_kind_of\(ty\) \{\s*match kind \{\s*"
                  r"((?:trust_ir::FatPtrKind::[A-Za-z]+(?:\s*\{\s*\.\.\s*\})?\s*\|?\s*)+)=>\s*\{\s*"
                  r"return Err\(", ib)
    if m is None:
        return {}
    return {"kinds": sorted(set(re.findall(r"FatPtrKind::([A-Za-z]+)", m.group(1))))}


def check_anchor(lean, anchor):
    kind = anchor[0]
    if kind == "undef_arm":
        _, name, want = anchor
        text = lean.get(name)
        if text is None:
            return f"{name} is not registered"
        arms = match_arms(text, "IRScalar")
        if "undef_" not in arms:
            return f"{name} has no `| IRScalar.undef_ =>` arm"
        got = _undef_verdict(arms["undef_"])
        return None if got == want else f"{name}: undef_ arm is {got}, rule needs {want}"
    if kind == "shape_never_zero":
        text = lean.get(anchor[1])
        if text is None:
            return f"{anchor[1]} is not registered"
        arms = match_arms(text, "IRTy")
        if not arms or any((_nat_value(v) or 0) <= 0 for v in arms.values()):
            return (f"{anchor[1]}: some IRTy arm is not a nonzero Nat, so undef_ may pass the "
                    f"shape check")
        return None
    if kind == "func_class_unique":
        # ir_ty_shape's `func_` arm and ir_scalar_shape's `fnptr_` arm are ONE class, which no
        # other arm of either takes.
        ty_arms = match_arms(lean.get("ir_ty_shape", ""), "IRTy")
        sc_arms = match_arms(lean.get("ir_scalar_shape", ""), "IRScalar")
        if "func_" not in ty_arms or "fnptr_" not in sc_arms:
            return "ir_ty_shape has no func_ arm or ir_scalar_shape no fnptr_ arm"
        unread = sorted([f"IRTy.{k}" for k, v in ty_arms.items() if _nat_value(v) is None] +
                        [f"IRScalar.{k}" for k, v in sc_arms.items() if _nat_value(v) is None])
        if unread:
            return f"shape arms that are not a Nat literal or Nat.succ tower: {unread}"
        f = _nat_value(ty_arms["func_"])
        if _nat_value(sc_arms["fnptr_"]) != f:
            return "the func_ and fnptr_ shape classes differ"
        others = [k for k, v in ty_arms.items() if k != "func_" and _nat_value(v) == f] + \
                 [k for k, v in sc_arms.items() if k != "fnptr_" and _nat_value(v) == f]
        return f"other arms share the function class: {others}" if others else None
    if kind == "callind_only_fnptr":
        arms = match_arms(lean.get(anchor[1], ""), "IRScalar")
        if "fnptr_" not in arms:
            return f"{anchor[1]} has no fnptr_ arm"
        bad = [k for k, v in arms.items() if k != "fnptr_" and not _norm(v).startswith("IRConfig.halted (")]
        return f"{anchor[1]}: non-fnptr_ arms that do not halt: {bad}" if bad else None
    if kind == "int_width_arms":
        text = lean.get(anchor[1])
        if text is None:
            return f"{anchor[1]} is not registered"
        arms = match_arms(text, "IRTy")
        some = sorted(k for k, v in arms.items() if _norm(v).startswith("IROption.some "))
        if some != ["int_", "uint_"]:
            return f"{anchor[1]}: IRTy constructors with a width are {some}, rule needs int_/uint_"
        return None
    name, frag = anchor
    text = lean.get(name)
    if text is None:
        return f"{name} is not registered"
    return None if _norm(frag) in _norm(text) else f"{name}: fragment not found: {frag!r}"


def pending_const_images(texts, blank, operand_image):
    """Crystal E3b: constants the BINARY projector (reader A, `scripts/crystal_a2_project`) has no
    arm for because its pinned trust-ir predates them, but which reader B (the in-tree TEXT
    reader, `ir_mint/emitted.rs`) images and EvalIR evaluates. Today exactly one:
    `Constant::Uninit` (an UNWRITTEN lane, binary v42 on the crystal lineage), which reader B reads
    as the core constant `(undef)` = `IRConst.undef_`. Reader A cannot image it at any rev it can
    be pinned to without the trust-ir lineages merging: trust-ir main has no `Constant::Uninit`,
    and a v42 blob of the crystal lineage is not readable by main's decoder (v40-v42 collide).

    DERIVED, never typed: reader B's lane arm, the core shape table's row for that core spelling,
    and the anchored EvalIR arms (ANCHORS "uninit.lane") must all be present; an absent piece
    means no pending image, never a guessed one. NOT gated: only the informational
    `pending_pin_images` figure reads this. When reader A gains the arm the entry disappears here
    and the gated model images the constant itself."""
    if "Uninit" in operand_image["const_variants"]:
        return {}
    rb = blank(texts["reader_b"])
    at = rb.find("fn cst(&mut self, s: &str)")
    if at < 0:
        raise Refusal("reader B emitted.rs: `fn cst(&mut self, s: &str)` not found")
    m = re.search(r'if\s+e\s*==\s*"uninit"\s*\{\s*elems\.push\(\s*Sx::tag\(\s*"([a-z_]+)"\s*,\s*'
                  r'vec!\[\]\s*\)\s*\)\s*;\s*continue\s*;\s*\}', _braced_body(rb, at))
    if not m:
        return {}
    core = m.group(1)
    sm = re.search(r'core:\s*"' + re.escape(core) + r'"\s*,\s*clean:\s*"(IRConst\.[A-Za-z_]+)"',
                   blank(texts["core_shapes"]))
    if not sm:
        raise Refusal(f"reader B images `uninit` as core `({core})`, which the core shape table "
                      f"(ir_mint/shape.rs CONSTS) does not declare")
    if sm.group(1) != "IRConst.undef_":
        raise Refusal(f"reader B images `uninit` as {sm.group(1)}; the anchored EvalIR lane "
                      f"semantics (ANCHORS uninit.lane) is IRConst.undef_'s")
    return {"Uninit": {"reader_b_core": f"({core})", "clean": sm.group(1)}}


def derive_semantics(texts):
    """Everything the analysis believes about EvalIR, parsed from `texts` {key: src}."""
    blank = _lexer()
    lean = {}
    for key in LEAN_SOURCES:
        for name, text in registered_lean(texts[key], blank).items():
            if name in lean:
                raise Refusal(f"Lean name {name} registered in two semantics sources")
            lean[name] = text
    irinst = inductive_ctors(lean, "IRInst")
    alphabets = {fam[2]: inductive_ctors(lean, fam[2]) for fam in OPERATOR_FAMILIES.values()}

    # Second source: census.rs EMITTED_INSTS must name exactly the same set.
    census_code = blank(texts["census"])
    m = re.search(r"EMITTED_INSTS\s*:\s*&\[&str\]\s*=\s*&\[(.*?)\];", census_code, re.DOTALL)
    if not m:
        raise Refusal("census.rs: EMITTED_INSTS not found")
    census = re.findall(r'"([A-Za-z_][A-Za-z0-9_]*)"', m.group(1))
    if sorted(census) != sorted(irinst) or len(census) != len(set(census)):
        raise Refusal(f"IRInst constructors disagree: syntax {sorted(irinst)} vs "
                      f"census.rs EMITTED_INSTS {sorted(census)}")

    # Third: the projector's `fn inst` arms, trust_ir::Inst variant -> IRInst.
    proj = blank(texts["projector"])
    at = proj.find("fn inst(&mut self, i: &Inst)")
    if at < 0:
        raise Refusal("projector main.rs: `fn inst(&mut self, i: &Inst)` not found")
    body = _braced_body(proj, at)
    kind_image = {}
    refused_kinds = set()
    # An arm head is an ALTERNATION of patterns (`Inst::A { .. } | Inst::B(..) | Inst::C =>`);
    # every variant it names is read, not only the last one.
    arm_pat = r"Inst::[A-Za-z]+\s*(?:\{[^{}]*\}|\([^()]*\))?"
    arms = list(re.finditer(rf"((?:{arm_pat}\s*\|\s*)*{arm_pat})\s*=>", body))
    stop = re.search(r"\bother\s*=>", body)
    imaging = []
    for n, am in enumerate(arms):
        end = arms[n + 1].start() if n + 1 < len(arms) else (stop.start() if stop else len(body))
        variants = re.findall(r"Inst::([A-Za-z]+)", am.group(1))
        seg = body[am.end():end]
        named = set()
        for lit in _literals_in(seg):
            if lit.startswith("("):
                spelling = lit[1:].split(" ", 1)[0].rstrip(")")
                named.update(c for c in irinst if c in (spelling, spelling + "_"))
        for v in variants:
            if v in kind_image or v in refused_kinds:
                raise Refusal(f"projector has two arms for Inst::{v}")
        # An EXPLICIT refusal arm (it names no constructor and its body returns Err) means
        # what the `other =>` wildcard used to mean: these variants have no image. Anything
        # else that names no constructor is still refused -- the parse must not guess.
        if not named and re.match(r"\s*\{?\s*(?:return\s+)?Err\s*\(", seg):
            refused_kinds.update(variants)
            continue
        if len(named) != 1:
            raise Refusal(f"projector arm Inst::{'|'.join(variants)} names {sorted(named)} IRInst "
                          f"constructors (need exactly one)")
        image = named.pop()
        for v in variants:
            kind_image[v] = image
        imaging.append((variants, seg))
    known = set(KIND_TEXT.values()) | set(OPERATOR_FAMILIES)
    if not set(kind_image) <= known:
        raise Refusal(f"projector arms for variants the printer table cannot spell: "
                      f"{sorted(set(kind_image) - known)}")
    # Crystal D1: ONE arm may image several variants onto one constructor only when that
    # variant set is DECLARED in SHARED_IMAGE_ARMS -- the alternation in the arm head is the
    # projector's own statement that they are imaged identically, and the declaration is ours
    # that the semantics agree. Injectivity is then required across ARMS.
    for variants, _seg in imaging:
        if len(variants) > 1 and frozenset(variants) not in SHARED_IMAGE_ARMS:
            raise Refusal(f"projector arm Inst::{'|'.join(variants)} images several variants onto "
                          f"one IRInst constructor, and SHARED_IMAGE_ARMS does not declare it")
    # Injective onto IRInst, and every IRInst constructor the projector does NOT image is
    # declared, by name, with where it comes from instead -- so a constructor added later
    # fails closed here until somebody says whether this projector should produce it.
    images = sorted(kind_image[vs[0]] for vs, _seg in imaging)
    unimaged_ctors = sorted(set(irinst) - set(images))
    if len(images) != len(set(images)) or not set(images) <= set(irinst):
        raise Refusal(f"projector arms are not injective into IRInst: arms {images} vs IRInst "
                      f"{sorted(irinst)}")
    if unimaged_ctors != sorted(IRINST_NOT_FROM_PROJECTOR):
        raise Refusal(f"IRInst constructors the projector does not image {unimaged_ctors} differ "
                      f"from the declared IRINST_NOT_FROM_PROJECTOR "
                      f"{sorted(IRINST_NOT_FROM_PROJECTOR)}")
    # Which fields of each arm go through `self.ty(..)` / `self.cst(..)`: must be
    # exactly the positions `operand_nodes` reads off the text.
    for variants, seg in imaging:
        got_ty = tuple(sorted(set(re.findall(r"self\.ty\(\s*([a-z_]+)\s*\)", seg))))
        got_cst = tuple(sorted(set(re.findall(r"self\.cst\(\s*([a-z_]+)\s*\)", seg))))
        for v in variants:
            want_ty = tuple(sorted(TYPED_FIELDS.get(v, ())))
            want_cst = ("value",) if v == "Const" else ()
            if got_ty != want_ty or got_cst != want_cst:
                raise Refusal(f"projector arm Inst::{v} images types {got_ty} / constants "
                              f"{got_cst}; the text positions read are {want_ty} / {want_cst}")
    operand_image = projector_operand_images(proj)
    pending_images = pending_const_images(texts, blank, operand_image)

    # Operator level: the projector's `mod ops` arms, each onto its Lean alphabet.
    ops_code = _ops_module(proj)
    op_image = {}
    for kind, (table, fn_name, alpha) in OPERATOR_FAMILIES.items():
        fm = re.search(rf"fn {fn_name}\(", ops_code)
        if not fm:
            raise Refusal(f"projector `mod ops`: fn {fn_name} not found")
        fbody = _braced_body(ops_code, fm.end())
        mapped = {}
        for om in re.finditer(r"\b[A-Z]::([A-Za-z]+)\s*=>\s*\"([a-z_]+)\"", fbody):
            spelling = om.group(2)
            ctor = [c for c in alphabets[alpha] if c in (spelling, spelling + "_")]
            if len(ctor) != 1:
                raise Refusal(f"`mod ops` {fn_name}: {om.group(1)} -> {spelling!r} names no "
                              f"{alpha} constructor")
            mapped[om.group(1)] = ctor[0]
        if not mapped:
            raise Refusal(f"projector `mod ops`: fn {fn_name} parsed no arms")
        unknown = sorted(set(mapped) - set(table.values()))
        if unknown:
            raise Refusal(f"`mod ops` {fn_name} maps variants the printer table does not know: "
                          f"{unknown}")
        op_image[kind] = mapped

    anchor_failures = []
    for group, anchors in ANCHORS.items():
        for a in anchors:
            err = check_anchor(lean, a)
            if err:
                anchor_failures.append(f"{group}: {err}")
    if anchor_failures:
        raise Refusal("EvalIR semantics moved; the rules resting on it must be re-derived:\n  "
                      + "\n  ".join(anchor_failures))

    # The ops EvalIR NEVER models, read off the dispatch arms themselves.
    def fault_ops(defname, alpha):
        arms = match_arms(lean[defname], alpha)
        if sorted(arms) != sorted(alphabets[alpha]):
            raise Refusal(f"{defname} does not have exactly one arm per {alpha} constructor")
        return sorted(k for k, v in arms.items() if _norm(v) in ("ir_width_fault", "ir_float_fault"))
    if "ir_cast_eval" not in lean or "ir_binop_eval" not in lean:
        raise Refusal("ir_cast_eval / ir_binop_eval are not registered")
    unmodelled_casts = fault_ops("ir_cast_eval", "IRCastOp")
    unmodelled_binops = fault_ops("ir_binop_eval", "IRBinOp")

    exec_arms = match_arms(lean["ir_exec"], "IRInst")
    if sorted(exec_arms) != sorted(irinst):
        raise Refusal("ir_exec does not have exactly one arm per IRInst constructor")

    seq_image = derive_seq_atomic_image(proj, irinst, op_image)
    tls_image = derive_tls_input_image(proj, irinst)
    ptr_bitcast = derive_ptr_bitcast_image(proj, irinst)
    neg_int = derive_negative_int_image(proj)
    ub_halt = derive_ub_halt_image(proj, irinst)
    d14_read = derive_d14_vtable_certify(proj)
    meta_check = derive_metadata_ty_check(proj)
    fat_consts = derive_fat_const_refusal(proj)

    sem = {
        "irinst_constructors": irinst,
        "alphabets": alphabets,
        "kind_image": dict(sorted(kind_image.items())),
        "refused_kinds": sorted(refused_kinds),
        "operator_image": {k: dict(sorted(v.items())) for k, v in sorted(op_image.items())},
        "unmodelled_cast_ops": unmodelled_casts,
        "unmodelled_binops": unmodelled_binops,
        "operand_image": operand_image,
        "seq_atomic_image": seq_image,
        "tls_input_image": tls_image,
        "ptr_bitcast_identity": ptr_bitcast,
        "negative_int_image": neg_int,
        "ub_halt_image": ub_halt,
        "d14_vtable_certify": d14_read,
        "metadata_ty_check": meta_check,
        "fat_const_refusal": fat_consts,
        "shared_image_arms": sorted("|".join(sorted(v)) for v in SHARED_IMAGE_ARMS),
        "pending_const_images": pending_images,
        "anchors_checked": sum(len(v) for v in ANCHORS.values()),
        "usize_bits": USIZE_BITS,
    }
    sem["digest"] = hashlib.sha256(
        json.dumps({k: v for k, v in sem.items()}, sort_keys=True).encode()).hexdigest()
    return sem


# ---------------------------------------------------------------------------
# OPERAND images. The projector refuses a body over a TYPE, a CONSTANT or a
# GLOBAL it cannot image (main.rs `fn ty`, `fn cst`, `fn global_ty_resolved`,
# `fn global_init` and the global loop of `project_chain`), not only over an
# instruction KIND. Added 2026-09-23 by the adversarial review: the kind-only
# model called 400 of infer_type_fast's 2,508 closure bodies projectable that
# the prebuilt projector (`a2project --usize-bits 64`, run once per body over
# the sidecar .bin) refuses -- infer_type_fast itself among them, over
# `Ty::Closure`. The accepted variant sets are DERIVED from the projector's
# arms; the text spellings below transcribe the trust-ir printer (ty.rs
# `impl Display for Ty`, display.rs `impl Display for Constant`, parser.rs
# `parse_global`, at the projector's pinned trust-ir b094459). An unparsed type
# or constant is a REFUSAL, never "imaged".
# ---------------------------------------------------------------------------
TYPED_FIELDS = {
    # Inst variant -> the fields its projector arm passes to `self.ty(..)`.
    "BinOp": ("ty",), "UnOp": ("ty",), "Overflow": ("ty",), "ICmp": ("ty",), "FCmp": ("ty",),
    "Cast": ("dst_ty", "src_ty"), "Load": ("ty",), "Store": ("ty",), "Alloca": ("ty",),
    "Copy": ("ty",), "GEP": ("pointee_ty",), "PtrData": ("ptr_ty",),
    "PtrMetadata": ("metadata_ty", "ptr_ty"), "PtrFromParts": ("metadata_ty", "ptr_ty"),
    "ExtractField": ("ty",), "InsertField": ("ty",), "ExtractElement": ("ty",),
    "Const": ("ty",), "Undef": ("ty",), "Select": ("ty",),
    # Crystal D10: `fn seq_atomic_image` images the operand type of each native atomic but Fence.
    "AtomicLoad": ("ty",), "AtomicStore": ("ty",), "AtomicRMW": ("ty",), "CmpXchg": ("ty",),
}
TY_ATOMS = {
    "i8": "I8", "i16": "I16", "i32": "I32", "i64": "I64", "i128": "I128", "u8": "U8",
    "u16": "U16", "u32": "U32", "u64": "U64", "u128": "U128", "isize": "Isize",
    "usize": "Usize", "char": "Char", "f16": "F16", "f32": "F32", "f64": "F64",
    "bool": "Bool", "ptr": "Ptr",
}
TY_IDS = {"struct": "Struct", "enum": "Enum", "functy": "Func", "record": "Record",
          "closure": "Closure"}
TY_ANGLE = {"fatptr": "FatPtr", "set": "Set", "seq": "Sequence", "refine": "Refine",
            "dialect": "Dialect", "handle": "Handle", "Rc": "Rc"}
FAT_KINDS = (("slice ty.", "Slice"), ("str", "Str"), ("dyn.", "TraitObject"),
             ("container_len", "ContainerLen"), ("container_vtable", "ContainerVtable"))
_TY_WORD = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
_NUM = re.compile(r"-?\d+(?:\.\d*)?(?:[eE][-+]?\d+)?")
I128_MAX = (1 << 127) - 1
# Global-loop and global-helper refusals the global model rests on (main.rs).
PROJECTOR_GLOBAL_ANCHORS = (
    "if g.mutable { return Err(",
    "if let Some(tls) = g.tls { return Err(",
    "if let Some(align) = g.align { return Err(",
    "let init = g.initializer.as_ref().ok_or_else(",
    "let resolved = self.global_ty_resolved(module, &g.name, &g.ty)?;",
    "let c = self.global_init(module, &g.ty, init)?;",
    # A struct/tuple global's type is its `fn ty` image; every other type falls through to the
    # array rule below. Pinned WHOLE: since the 2026-09-26 merge of origin/main this is a `match`
    # naming every `Ty` variant (main's check_lint_coverage.py refuses the `matches!` it was),
    # so a variant moved into the `true` arm, or a second `true` arm, moves the anchor. Since the
    # train-clean-1 merge (2026-10-14) its first arm is trust-ir D1b's uninhabited `Ty::Ext`.
    "let aggregate = match ty { Ty::Ext(e) => e.unreachable(), "
    "Ty::Struct(_) | Ty::Tuple(_) => true, Ty::Array(..) | Ty::Ptr "
    "| Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_) | Ty::I8 | Ty::I16 | Ty::I32 "
    "| Ty::I64 | Ty::I128 | Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 | Ty::U128 | Ty::Isize "
    "| Ty::Usize | Ty::Char | Ty::Error | Ty::F16 | Ty::F32 | Ty::F64 | Ty::Bool | Ty::Unit "
    "| Ty::Never | Ty::Enum(_) | Ty::Rc(_) | Ty::Vector(..) | Ty::FatPtr(_) | Ty::Func(_) "
    "| Ty::Set(..) | Ty::Sequence(_) | Ty::Record(_) | Ty::Closure(_) | Ty::Refine(..) "
    "| Ty::Dialect(_) | Ty::Handle(_) => false, }; if aggregate { return self.ty(ty); }",
    # The array rule: since the 2026-09-27 merge of origin/main (its lint r11 refuses the
    # `let .. else` this was) a `match` whose one accepted arm is `Ty::Array`, pinned by its head
    # (after trust-ir D1b's uninhabited `Ty::Ext`, since the train-clean-1 merge).
    "let (elem, len) = match ty { Ty::Ext(e) => e.unreachable(), Ty::Array(elem, len) => (elem, len),",
    'if elem_text.contains("ty.") { return Err(',
    "(Ty::Array(..), Constant::Array(v)) => { let mut s = String::from(\"(agg\"); for e in v { "
    "s.push(' '); s.push_str(&self.cst(e)?);",
    # Crystal plan step 18 (`const-images`): a struct/tuple global takes an aggregate whose
    # elements go through `global_elem`, where a function address is the one new form.
    "(Ty::Struct(_) | Ty::Tuple(_), Constant::Aggregate(v)) => { let mut s = String::from(\"(agg\"); "
    "for e in v { s.push(' '); s.push_str(&self.global_elem(module, e)?);",
    "Constant::SymbolAddr { symbol, addend: 0 } => { let mut named = "
    "module.functions.iter().filter(|f| f.name == *symbol);",
    "let (Some(f), None) = (named.next(), named.next()) else { return Err(",
    # Since the train-clean-1 merge (2026-10-14): trust-ir v50's `Constant::Splat` joins the
    # elements handed to `cst`, which refuses it by name, and v49's `Constant::Uninit` is refused
    # by name in `global_elem` itself (trust-ir-build's validator refuses it anywhere in a global
    # initializer); until then it was handed to `cst`, which refused it too.
    "| Constant::SymbolAddr { .. } | Constant::PhantomData | Constant::Splat { .. }) => self.cst(other),",
    "Constant::Uninit => Err(String::from(",
)


def _close_of(s, i, open_c, close_c):
    """Index of the `close_c` matching the `open_c` at s[i] (double-quote aware)."""
    depth, j, n = 0, i, len(s)
    while j < n:
        c = s[j]
        if c == '"':
            k = s.find('"', j + 1)
            if k < 0:
                raise Refusal(f"unterminated quote in operand text {s[i:i + 60]!r}")
            j = k + 1
            continue
        if c == open_c:
            depth += 1
        elif c == close_c:
            depth -= 1
            if depth == 0:
                return j
        j += 1
    raise Refusal(f"unbalanced {open_c}{close_c} in operand text {s[i:i + 60]!r}")


def parse_ty_text(s, i=0):
    """(node, end) for the trust-ir type printed at s[i:]. node = (variant, detail, kids)."""
    for pre, var in (("&mut ", "RefMut"), ("&", "Ref"), ("*const ", "PtrConst"),
                     ("*mut ", "PtrMut")):
        if s.startswith(pre, i):
            inner, j = parse_ty_text(s, i + len(pre))
            return (var, None, [inner]), j
    for lit, var in (("{error}", "Error"), ("(,)", "Tuple"), ("()", "Unit"), ("!", "Never")):
        if s.startswith(lit, i):
            return (var, 0 if var == "Tuple" else None, []), i + len(lit)
    if s.startswith("(", i):
        kids, j = [], i + 1
        while True:
            k, j = parse_ty_text(s, j)
            kids.append(k)
            if s.startswith(", ", j):
                j += 2
                continue
            if s.startswith(")", j):
                return ("Tuple", len(kids), kids), j + 1
            raise Refusal(f"unparsed tuple type in {s!r}")
    m = re.compile(r"\[ty\.(\d+) x (\d+)\]").match(s, i)
    if m:
        return ("Array", int(m.group(1)), []), m.end()
    m = re.compile(r"<(\d+) x ").match(s, i)
    if m:
        inner, j = parse_ty_text(s, m.end())
        if not s.startswith(">", j):
            raise Refusal(f"unparsed vector type in {s!r}")
        return ("Vector", int(m.group(1)), [inner]), j + 1
    m = _TY_WORD.match(s, i)
    if not m:
        raise Refusal(f"unparsed trust-ir type at {s[i:i + 60]!r}")
    word, j = m.group(0), m.end()
    if word in TY_ANGLE and s.startswith("<", j):
        close = _close_of(s, j, "<", ">")
        inside = s[j + 1:close]
        if word == "Rc":
            inner, k = parse_ty_text(inside, 0)
            if k != len(inside):
                raise Refusal(f"unparsed Rc<> type in {s!r}")
            return ("Rc", None, [inner]), close + 1
        if word == "fatptr":
            kinds = [v for pre, v in FAT_KINDS if inside == pre or
                     (pre.endswith((".", " ty.")) and inside.startswith(pre)
                      and inside[len(pre):].isdigit())]
            if len(kinds) != 1:
                raise Refusal(f"unparsed fat pointer kind {inside!r}")
            return ("FatPtr", kinds[0], []), close + 1
        return (TY_ANGLE[word], inside, []), close + 1
    if word in TY_ATOMS:
        return (TY_ATOMS[word], None, []), j
    if word in TY_IDS:
        m2 = re.compile(r"\.(\d+)").match(s, j)
        if m2:
            return (TY_IDS[word], int(m2.group(1)), []), m2.end()
    raise Refusal(f"unparsed trust-ir type at {s[i:i + 60]!r}")


def _const_list(s, i, close, names=None):
    """Elements `a, b, ...` up to the literal `close` (which ends the list)."""
    kids, j = [], i
    if s.startswith(close, j):
        return kids, j + len(close)
    while True:
        k, j = parse_const_text(s, j, names)
        kids.append(k)
        if s.startswith(", ", j):
            j += 2
            continue
        if s.startswith(close, j):
            return kids, j + len(close)
        raise Refusal(f"unparsed constant list in {s[i:i + 80]!r}")


def _symaddr_by_name(s, j, names):
    """(symbol, end) when `symaddr<` at s[j:] names a function of `names` with addend 0.

    The printer spells `symaddr<{symbol}>` with the symbol RAW, and a Rust instance name can
    carry an unbalanced `>` (`fn(A) -> B`), so bracket matching cannot delimit it. A name the
    module's own function table carries, followed by `>`, can; the longest such name wins.
    """
    best = None
    for n in names or ():
        if s.startswith(n, j) and s.startswith(">", j + len(n)) and (best is None or len(n) > len(best)):
            best = n
    return (best, j + len(best) + 1) if best is not None else (None, None)


def parse_const_text(s, i=0, names=None):
    """(node, end) for the trust-ir constant printed at s[i:]. node = (variant, detail, kids).

    `names` (a set of the module's function names) lets a `symaddr<NAME>` be read as the address
    of exactly that function (detail = NAME); without it, or when no name fits, the symbol is
    delimited by bracket matching and carries no detail."""
    if s.startswith("{  }", i):
        return ("Aggregate", None, []), i + 4
    if s.startswith("{ ", i):
        kids, j = _const_list(s, i + 2, " }", names)
        return ("Aggregate", None, kids), j
    for pre, var in (("array[ ", "Array"), ("vec[ ", "Vector"), ("seq[ ", "Sequence")):
        if s.startswith(pre, i):
            kids, j = _const_list(s, i + len(pre), " ]", names)
            return (var, None, kids), j
    if s.startswith("symaddr<", i) and names:
        sym, j = _symaddr_by_name(s, i + len("symaddr<"), names)
        if sym is not None:
            return ("SymbolAddr", sym, []), j
    for pre, var in (("set{", "Set"), ("record{", "Record")):
        if s.startswith(pre, i):
            return (var, None, []), _close_of(s, i + len(pre) - 1, "{", "}") + 1
    for pre, var in (("fndef<", "FnDef"), ("symaddr<", "SymbolAddr"), ("bytes<", "Bytes"),
                     ("utf8bytes<", "Bytes"), ("closure<", "Closure")):
        if s.startswith(pre, i):
            j = _close_of(s, i + len(pre) - 1, "<", ">") + 1
            if var == "Closure" and s.startswith("{", j):
                j = _close_of(s, j, "{", "}") + 1
            return (var, None, []), j
    for lit, var in (("phantomdata", "PhantomData"), ("uninit", "Uninit"), ("true", "Bool"),
                     ("false", "Bool"), ("NaN", "Float"), ("-inf", "Float"), ("inf", "Float")):
        if s.startswith(lit, i) and not (s[i + len(lit):i + len(lit) + 1].isalnum()):
            return (var, None, []), i + len(lit)
    m = _NUM.match(s, i)
    if m:
        t = m.group(0)
        if any(c in t for c in ".eE"):
            return ("Float", None, []), m.end()
        v = int(t)
        return ("U128" if v > I128_MAX else "Int", v, []), m.end()
    raise Refusal(f"unparsed trust-ir constant at {s[i:i + 60]!r}")


def _ops_module(code):
    """The body of the projector's inline `mod ops { .. }` (comment-blanked `code`): the operator
    alphabets, which lived in a sibling `ops.rs` until the projector became one source file.
    Exactly one such module, or a refusal -- never a search of the whole file for `fn binop(`."""
    heads = [m.start() for m in re.finditer(r"(?m)^mod ops\s*\{", code)]
    if len(heads) != 1:
        raise Refusal(f"projector main.rs: {len(heads)} `mod ops {{` blocks (need exactly one)")
    return _braced_body(code, heads[0])


# The refusing catch-all of a projector `match`: a bare `other =>` binding, or -- since the
# projector names every variant it refuses rather than wildcarding them -- `other @ (A | B ..) =>`.
# The alternation is matched lazily up to the FIRST `) =>`, which is the arm's own `=>`: no
# variant pattern inside it contains `=>`.
_CATCH_ALL = re.compile(r"\bother\s*(?:@\s*\(.*?\))?\s*=>", re.S)


def _arms_of(code, fn_sig, enum):
    """[(variant, pattern payload, rhs)] of a `match` in `fn_sig`, plus the catch-all rhs."""
    at = code.find(fn_sig)
    if at < 0:
        raise Refusal(f"projector main.rs: `{fn_sig}` not found")
    body = _braced_body(code, at)
    stop = _CATCH_ALL.search(body)
    arms = [a for a in re.finditer(rf"\b{enum}::([A-Za-z0-9]+)(?:\(([^()]*)\))?\s*=>", body)
            if stop is None or a.start() < stop.start()]
    if not arms or not stop or "Err(" not in body[stop.end():]:
        raise Refusal(f"projector main.rs `{fn_sig}`: arms or its refusing catch-all not found")
    out = []
    for n, am in enumerate(arms):
        end = arms[n + 1].start() if n + 1 < len(arms) else stop.start()
        rhs = body[am.end():end]
        # trust-ir D1b's extension variant (`Ty::Ext(e)`, `Constant::Ext(e)`) is UNINHABITED in
        # this build: its one admissible arm is `<binding>.unreachable()`, which images nothing
        # and refuses nothing, so it is not an arm of the image table. Any other `Ext` arm --
        # one that builds a string, returns, or calls anything else -- is read like every arm.
        if am.group(1) == "Ext" and re.fullmatch(
                rf"\s*{re.escape(am.group(2) or '')}\.unreachable\(\)\s*,?\s*", rhs or "x"):
            continue
        out.append((am.group(1), am.group(2) or "", rhs))
    return out


def projector_operand_images(proj):
    """What the projector's `fn ty` / `fn cst` accept, DERIVED from their arms."""
    ty_arms = _arms_of(proj, "fn ty(&mut self, t: &Ty) -> R<String>", "Ty")
    ty_variants, recursive, width, fat = set(), set(), set(), None
    for v, pay, rhs in ty_arms:
        if v not in set(TY_ATOMS.values()) | set(TY_IDS.values()) | set(TY_ANGLE.values()) | {
                "Unit", "Never", "Tuple", "Array", "Vector", "Error", "Ref", "RefMut",
                "PtrConst", "PtrMut"}:
            raise Refusal(f"projector `fn ty` images Ty::{v}, which the printer table cannot spell")
        ty_variants.add(v)
        if "self.ty(" in rhs:
            recursive.add(v)
        if "self.usize_bits" in rhs:
            width.add(v)
        if v == "FatPtr":
            km = re.search(r"FatPtrKind::([A-Za-z]+)", pay)
            fat = (fat or set()) | ({km.group(1)} if km else {k for _, k in FAT_KINDS})
    cst_arms = _arms_of(proj, "fn cst(&mut self, c: &Constant) -> R<String>", "Constant")
    const_variants, const_rec, neg_refused = set(), set(), False
    for v, _pay, rhs in cst_arms:
        const_variants.add(v)
        if "self.cst(" in rhs:
            const_rec.add(v)
        if v == "Int" and re.search(r"if\s+\*v\s*<\s*0\s*\{\s*return\s+Err\(", rhs):
            neg_refused = True
    norm = _norm(proj)
    missing = [a for a in PROJECTOR_GLOBAL_ANCHORS if _norm(a) not in norm]
    if missing:
        raise Refusal("projector global rules moved; the global model must be re-derived: "
                      + "; ".join(missing))
    return {"ty_variants": sorted(ty_variants), "ty_recursive": sorted(recursive),
            "ty_needs_width": sorted(width), "fat_kinds": sorted(fat or ()),
            "const_variants": sorted(const_variants), "const_recursive": sorted(const_rec),
            "int_refuses_negative": neg_refused}


def ty_imaged(node, img):
    v, detail, kids = node
    if v not in img["ty_variants"]:
        return False
    if v == "FatPtr" and detail not in img["fat_kinds"]:
        return False
    return v not in img["ty_recursive"] or all(ty_imaged(k, img) for k in kids)


def cst_imaged(node, img):
    v, detail, kids = node
    if v not in img["const_variants"]:
        return False
    if v == "Int" and img["int_refuses_negative"] and detail < 0:
        return False
    return v not in img["const_recursive"] or all(cst_imaged(k, img) for k in kids)


def _node_name(node):
    v, detail, _ = node
    return f"{v}({detail})" if v == "FatPtr" else ("negative Int" if v == "Int" else v)


_ORD_WORD = r"(?:relaxed|release|acquire|acq_rel|seq_cst|unordered|monotonic)"
# Crystal step 19: a SUPPLIED intrinsic body's producer stamp, as the trust-ir printer spells
# `Producer::Other("trust-intrinsic-arm")`, and the heads whose body the lane supplies.
SUPPLIED_PRODUCER_TEXT = '"trust-intrinsic-arm"'
SUPPLIED_ARM_HEADS = frozenset({"compare_bytes"})
# Crystal D13 (the trust sidecar's `fnptr-thunks` lane): a SUPPLIED ABI thunk's producer stamp and
# the suffix its name adds to its shim's (trust-ir-bridge `lower/abi_thunks.rs`).
THUNK_PRODUCER_TEXT = '"trust-abi-thunk"'
THUNK_SUFFIX = "#trust-abi-thunk"
# Crystal memo §15/§18: the trust bridge's undefined-behaviour halt obligation, SITED (its
# `site f<fn>/bb<k>#<index>` names the halting assert). The projector's `fn ub_halt_image` images
# that assert as `unreachable`. The wording is the bridge's exactly (`CallHalt::UndefinedBehavior`).
UB_HALT_WORDING = "is undefined behavior; this program point must be proven unreachable"
UB_HALT_OBL_RE = re.compile(
    r'^obligation \d+ \S+ \S+ "reaching `[^`"\\]*` is undefined behavior; this program point must be '
    r'proven unreachable" .* site f(\d+)/bb(\d+)#(\d+)$')


def operand_nodes(kind, rest):
    """{field: type node} and the constant node the projector images, read off the text."""
    tys = {}
    cst = None

    def ty_at(field, i):
        node, j = parse_ty_text(rest, i)
        tys[field] = node
        return j

    def expect(pat, j):
        m = re.compile(pat).match(rest, j)
        if not m:
            raise Refusal(f"unparsed {kind} operands: {rest[:120]!r}")
        return m.end()

    if kind in ("BinOp", "Overflow", "UnOp", "Copy", "ExtractField", "InsertField",
                "ExtractElement", "Select", "Undef", "Load", "Store", "Alloca"):
        j = ty_at("ty", 0)
        expect({"BinOp": r" %\d+, %\d+$", "Overflow": r" %\d+, %\d+$", "UnOp": r" %\d+$",
                "Copy": r" %\d+$", "ExtractField": r" %\d+, \d+$",
                "InsertField": r" %\d+, \d+, %\d+$", "ExtractElement": r" %\d+, %\d+$",
                "Select": r" %\d+, %\d+, %\d+$", "Undef": r"$",
                "Load": r", ptr %\d+(?:, align \d+)?$",
                "Store": r" %\d+, ptr %\d+(?:, align \d+)?$",
                "Alloca": r"(?:, %\d+)?(?:, align \d+)?$"}[kind], j)
    elif kind in ("ICmp", "FCmp"):
        expect(r" %\d+, %\d+$", ty_at("ty", expect(r"\S+ ", 0)))
    elif kind == "Cast":
        expect(r"$", ty_at("dst_ty", expect(r" %\d+ to ", ty_at("src_ty", 0))))
    elif kind == "GEP":
        expect(r", ptr %\d+(?:, %\d+)*$", ty_at("pointee_ty", expect(r"(?:inbounds )?", 0)))
    elif kind == "PtrData":
        expect(r" %\d+$", ty_at("ptr_ty", 0))
    elif kind == "PtrMetadata":
        expect(r"$", ty_at("metadata_ty", expect(r" %\d+ to ", ty_at("ptr_ty", 0))))
    elif kind == "PtrFromParts":
        expect(r" %\d+$", ty_at("metadata_ty", expect(r" ptr %\d+, ", ty_at("ptr_ty", 0))))
    elif kind == "Const":
        j = expect(r" ", ty_at("ty", 0))
        cst, j = parse_const_text(rest, j)
        expect(r"$", j)
        _check_uninit_placement(tys["ty"], cst, rest)
    # Crystal D10: the native atomics' printed forms (trust-ir display.rs `write_inst`).
    elif kind == "AtomicLoad":
        expect(r", ptr %\d+$", ty_at("ty", expect(_ORD_WORD + r" ", 0)))
    elif kind == "AtomicStore":
        expect(r" %\d+, ptr %\d+$", ty_at("ty", expect(_ORD_WORD + r" ", 0)))
    elif kind == "AtomicRMW":
        expect(r" ptr %\d+, %\d+$", ty_at("ty", expect(r"[a-z]+ " + _ORD_WORD + r" ", 0)))
    elif kind == "CmpXchg":
        expect(r" ptr %\d+, %\d+, %\d+ " + _ORD_WORD + r" " + _ORD_WORD + r"$",
               ty_at("ty", expect(r"(?:weak )?", 0)))
    if tuple(sorted(tys)) != tuple(sorted(TYPED_FIELDS.get(kind, ()))):
        raise Refusal(f"internal: {kind} operand positions {sorted(tys)} are not TYPED_FIELDS")
    return tys, cst


def _mentions_uninit(node):
    return node[0] == "Uninit" or any(_mentions_uninit(k) for k in node[2])


def _check_uninit_placement(ty_node, cst, text):
    """Crystal E3b: `uninit` (trust-ir `Constant::Uninit`, an UNWRITTEN lane) stands ONLY as a
    direct lane of a struct/tuple aggregate constant -- trust-ir-build's placement rule
    (`validate_uninit_lanes`). Anywhere else the artifact is malformed: a REFUSAL."""
    if not _mentions_uninit(cst):
        return
    if ty_node[0] in ("Struct", "Tuple") and cst[0] == "Aggregate" and all(
            k[0] == "Uninit" or not _mentions_uninit(k) for k in cst[2]):
        return
    raise Refusal(f"`uninit` outside a direct struct/tuple lane: const {text[:120]!r}")


def parse_global(line, names=None):
    """A `global ...` line (parser.rs parse_global): flags, name, type node, initializer."""
    m = re.match(r"^global ((?:[a-z_]+ |tls\([^)]*\) |align\(\d+\) )*)@", line)
    if not m:
        raise Refusal(f"unparsed global declaration {line[:100]!r}")
    try:
        name, end, spelling = tir_symbols.read_global_symbol(line, m.end())
    except tir_symbols.SymbolRefusal as exc:
        raise Refusal(f"global declaration {line[:100]!r}: {exc}") from exc
    if not line.startswith(" ", end) or end + 1 >= len(line):
        raise Refusal(f"unparsed global declaration {line[:100]!r}")
    flags = m.group(1).split()
    body = line[end + 1:]
    ty, j = parse_ty_text(body, 0)
    rest = body[j:]
    init = None
    if rest.startswith(" = "):
        init, k = parse_const_text(rest, 3, names)
        if k != len(rest):
            raise Refusal(f"unparsed global initializer {line[:100]!r}")
        if _mentions_uninit(init):
            raise Refusal(f"`uninit` in a global initializer {line[:100]!r}")
    elif rest:
        raise Refusal(f"unparsed global declaration {line[:100]!r}")
    return {"name": name, "spelling": spelling, "mutable": "mut" in flags,
            "tls": any(f.startswith("tls(") for f in flags),
            "align": any(f.startswith("align(") for f in flags), "ty": ty, "init": init}


def _global_elem_imaged(node, img, fn_names):
    """main.rs `global_elem`: a function address by exact name, an aggregate, or a `cst` image."""
    v, detail, kids = node
    if v == "SymbolAddr":
        return detail is not None and detail in fn_names
    if v == "Aggregate":
        return all(_global_elem_imaged(k, img, fn_names) for k in kids)
    return cst_imaged(node, img)


def global_imaged(g, types, img, fn_names=frozenset()):
    """None if the projector images this global, else why not (main.rs global loop)."""
    if g["mutable"] or g["tls"] or g["align"]:
        return "mut/tls/align global"
    if g["init"] is None:
        return "declaration-only global (no initializer)"
    if g["ty"][0] in ("Struct", "Tuple"):
        # Crystal plan step 18 (`const-images`): `global_ty_resolved` spells it as its `fn ty`
        # image and `global_init` takes only an aggregate through `global_elem`.
        if not ty_imaged(g["ty"], img):
            return f"global type {g['ty'][0]} has no image"
        if g["init"][0] != "Aggregate" or not all(
                _global_elem_imaged(e, img, fn_names) for e in g["init"][2]):
            return "global initializer is not an imaged aggregate {...}"
        return None
    if g["ty"][0] != "Array":
        return f"non-array global type {g['ty'][0]}"
    elem = types.get(g["ty"][1])
    if elem is None or "ty." in elem:
        return "global element type does not resolve"
    if g["init"][0] != "Array" or not all(cst_imaged(e, img) for e in g["init"][2]):
        return "global initializer is not an imaged array[...]"
    return None


def negative_int_imaged(inst, sem):
    """Crystal memo §18: a TOP-LEVEL negative `Int` constant at an integer type the projector's
    `fn negative_int_const_image` takes (read off its width match) is imaged as its bit pattern.
    Inside an aggregate or a global it is not."""
    img = sem.get("negative_int_image") or {}
    cst = inst.get("opnd_const")
    ty = inst.get("opnd_tys", {}).get("ty")
    return bool(img) and inst["mnem"] == "const" and cst is not None and ty is not None \
        and cst[0] == "Int" and isinstance(cst[1], int) and cst[1] < 0 and not cst[2] \
        and ty[0] in img.get("types", ())


def ptr_bitcast_imaged(inst, sem):
    """Crystal D12: a `bitcast ptr %x to ptr` is imaged as `copy (ptr) %x` (projector's `fn
    ptr_bitcast_identity_image`); every other bitcast keeps its cast image."""
    return bool(sem.get("ptr_bitcast_identity")) and inst.get("mnem") == "bitcast" \
        and inst.get("src_ty") == "ptr" and inst.get("dst_ty") == "ptr"


def unimaged_operand(inst, sem):
    """('type'|'const'|'global', detail) when the projector refuses an operand, else None."""
    img = sem["operand_image"]
    for _, node in sorted(inst.get("opnd_tys", {}).items()):
        if not ty_imaged(node, img):
            return ("type", _node_name(node))
    if inst.get("opnd_const") is not None and not cst_imaged(inst["opnd_const"], img) \
            and not negative_int_imaged(inst, sem):
        return ("const", _node_name(inst["opnd_const"]))
    if inst["mnem"] == "global_addr" and inst.get("global_why"):
        return ("global", inst["global_why"])
    if inst.get("d14_uncertified"):
        return ("vtable", "D14 vtable use outside the certified image")
    mc = sem.get("metadata_ty_check") or {}
    if inst["mnem"] in mc.get("ops", ()):
        pt, mt = inst.get("opnd_tys", {}).get("ptr_ty"), inst.get("opnd_tys", {}).get("metadata_ty")
        if pt is not None and mt is not None:
            want = mc["canonical"].get(pt[1]) if pt[0] == "FatPtr" else \
                (mc["thin"] if pt[0] in THIN_PTR_TYS else None)
            if want is None or mt[0] != want:
                return ("metadata", f"{inst['mnem']} metadata type {mt[0]} is not {pt[0]}'s canonical")
    fc = sem.get("fat_const_refusal") or {}
    if inst["mnem"] == "const":
        t = inst.get("opnd_tys", {}).get("ty")
        if t is not None and t[0] == "FatPtr" and t[1] in fc.get("kinds", ()):
            return ("const", f"FatPtr({t[1]}) constant")
    return None


# IRInst constructors the sidecar projector (scripts/crystal_a2_project) never produces, and
# where each comes from instead. Checked for EQUALITY against the unimaged set above.
# Crystal D1: projector arms that image SEVERAL trust_ir::Inst variants onto ONE IRInst
# constructor, each with why the semantics agree. Any other multi-variant imaging arm is refused.
SHARED_IMAGE_ARMS = {
    # trust-ir's reference interpreter executes both in ONE arm (interpret.rs, `Inst::Borrow { ptr }
    # | Inst::BorrowMut { ptr } =>`: the operand's pointer after `expect_pointer`, a fat pointer
    # verbatim), and EvalIR's `borrow` is that arm (`ir_borrow_eval`, ANCHORS undef.borrow.ptr).
    frozenset({"Borrow", "BorrowMut"}): "one arm in trust-ir's reference interpreter",
}

IRINST_NOT_FROM_PROJECTOR = {
    # crates/clean-verify/tests/eval_ir/census.rs: "Compiler-owned atomic bridge; sequential
    # byte execution only" (eval_ir_syntax.rs: a narrow ByteV1 operation the legacy cell
    # machine refuses). The projector refuses trust_ir::Inst::AtomicRMW by name.
    "atomic_fetch_add_relaxed_u64_seq",
    # census.rs: "Distinct target-indexed Usize lane. Source attachment is separate work."
    # (eval_ir_syntax.rs: appended with a target-bit-width index; only width 64 executes in
    # ByteV1, and the legacy cell machine refuses it). No projector arm produces it either.
    "atomic_fetch_add_relaxed_usize_seq",
}


def refused_by_projector(inst, sem):
    return unimaged(inst, sem) or unimaged_operand(inst, sem)


# ---------------------------------------------------------------------------
# The artifact: a strict parse of the sidecar text, joined to the manifest.
# ---------------------------------------------------------------------------
# What may stand before `fn @` in a header: the `rustcc` calling-convention word. The symbol after
# it is read by the shared reader (`crystal_trust_ir_symbols.parse_fn_header`).
FN_PREFIX = re.compile(r"(?:rustcc )?")
BLOCK_RE = re.compile(r"^(bb\d+)(?:\((.*)\))?:$")
RESULTS_RE = re.compile(r"^(%\d+(?:, %\d+)*) = (.*)$")
ID_RE = re.compile(r"%(\d+)")
TOPLEVEL_OK = re.compile(
    r"^(?:;|module |file |struct |enum |type |closure_ty |functy\.\d+ = |global |obligation )")
TARGET_RE = re.compile(r"bb(\d+)(\([^)]*\))?")
# A bodiless DECLARATION (a function past the members, with no blocks) is admitted only for a
# FOREIGN premise, the shape the trust bridge's `premise-decls` lane emits: a def path whose last
# segment follows an `{extern#N}` segment (DefPathData::ForeignMod), exactly as the link-3
# reconcile rule /4 requires.
FOREIGN_ITEM_RE = re.compile(r"\{extern#\d+\}::[^:]+$")
INT_TY = re.compile(r"^([iu])(8|16|32|64|128)$")


def _ids(s):
    return [int(x) for x in ID_RE.findall(s)]


def _int_width(ty):
    ty = ty.strip()
    if ty in ("usize", "isize"):
        return USIZE_BITS
    m = INT_TY.match(ty)
    return int(m.group(2)) if m else None


def _targets(s):
    """[(block label, [arg ids])] in textual order."""
    out = []
    for m in TARGET_RE.finditer(s):
        out.append(("bb" + m.group(1), _ids(m.group(2) or "")))
    return out


def parse_inst(line):
    """One instruction line (comment already stripped) -> dict, or Refusal."""
    rm = RESULTS_RE.match(line)
    results = _ids(rm.group(1)) if rm else []
    body = rm.group(2) if rm else line
    volatile = False
    if body.startswith("volatile "):
        volatile = True
        body = body[len("volatile "):]
    word, _, rest = body.partition(" ")
    mnem, kind, sub = classify_mnemonic(word, rest)
    inst = {"res": results, "mnem": mnem, "kind": kind, "sub": sub, "uses": _ids(rest),
            "roles": {}, "text": line}
    r = inst["roles"]

    def need(pattern):
        m = re.match(pattern, rest)
        if not m:
            raise Refusal(f"unparsed {mnem} shape: {line!r}")
        return m

    if kind == "BinOp" or kind == "Overflow" or kind in ("ICmp", "FCmp"):
        m = need(r"^(?:\S+ )?(.+) %(\d+), %(\d+)$") if kind in ("ICmp", "FCmp") else \
            need(r"^(.+) %(\d+), %(\d+)$")
        inst["ty"] = m.group(1)
        r["lhs"], r["rhs"] = int(m.group(2)), int(m.group(3))
    elif kind == "UnOp":
        m = need(r"^(.+) %(\d+)$")
        inst["ty"] = m.group(1)
        r["operand"] = int(m.group(2))
    elif kind == "Cast":
        m = need(r"^(.+) %(\d+) to (.+)$")
        inst["src_ty"], inst["dst_ty"] = m.group(1), m.group(3)
        r["operand"] = int(m.group(2))
    elif mnem == "load":
        m = need(r"^(.+), ptr %(\d+)(?:, align \d+)?$")
        r["ptr"] = int(m.group(2))
    elif mnem == "store":
        m = need(r"^(.+) %(\d+), ptr %(\d+)(?:, align \d+)?$")
        r["value"], r["ptr"] = int(m.group(2)), int(m.group(3))
    elif mnem == "gep":
        m = need(r"^(?:inbounds )?(.+), ptr %(\d+)((?:, %\d+)*)$")
        r["base"] = int(m.group(2))
        # Not a ROLE (a gep has any number of them): read by the gep-index rule only.
        inst["gep_indices"] = _ids(m.group(3))
    elif mnem in ("borrow", "borrow_mut"):
        r["ptr"] = int(need(r"^%(\d+)$").group(1))
    elif mnem == "copy":
        m = need(r"^(.+) %(\d+)$")
        inst["ty"] = m.group(1)
        r["operand"] = int(m.group(2))
    elif mnem == "extractfield":
        r["aggregate"] = int(need(r"^(.+) %(\d+), \d+$").group(2))
    elif mnem == "insertfield":
        m = need(r"^(.+) %(\d+), \d+, %(\d+)$")
        inst["ty"] = m.group(1)
        r["aggregate"], r["value"] = int(m.group(2)), int(m.group(3))
    elif mnem == "select":
        m = need(r"^(.+) %(\d+), %(\d+), %(\d+)$")
        r["cond"], r["then"], r["else"] = int(m.group(2)), int(m.group(3)), int(m.group(4))
    elif mnem in ("assert", "assume"):
        r["cond"] = int(need(r"^%(\d+)$").group(1))
    elif mnem == "ptr_data":
        r["ptr"] = int(need(r"^(.+) %(\d+)$").group(2))
    elif mnem == "ptr_metadata":
        r["ptr"] = int(need(r"^(.+) %(\d+) to (.+)$").group(2))
    elif mnem == "ptr_from_parts":
        m = need(r"^(.+) ptr %(\d+), (.+) %(\d+)$")
        r["data"], r["meta"] = int(m.group(2)), int(m.group(4))
    elif mnem == "const":
        # The TYPE is read with the one type grammar (`parse_ty_text`), never a token regex: a
        # tuple type `(i32, ptr)` holds a space, and `^(\S+|\(.*?\))` read it as `(i32,` (C-M0,
        # the D3 arm's two-argument ABI thunk #2990, `const (i32, ptr) { 0, 0 }`).
        try:
            _node, k = parse_ty_text(rest, 0)
        except Refusal:
            raise Refusal(f"unparsed {mnem} shape: {line!r}") from None
        if not rest.startswith(" ", k) or k + 1 >= len(rest):
            raise Refusal(f"unparsed {mnem} shape: {line!r}")
        inst["const_ty"], inst["const_value"] = rest[:k], rest[k + 1:]
    elif mnem == "undef":
        inst["ty"] = need(r"^(.+)$").group(1)
    elif mnem == "global_addr":
        inst["global"] = int(need(r"^@global\.(\d+)$").group(1))
    elif mnem == "call":
        m = need(r"^@func\.(\d+)\(((?:%\d+(?:, %\d+)*)?)\)$")
        inst["callee"] = int(m.group(1))
        r["args"] = _ids(m.group(2))
    elif mnem == "call_indirect":
        m = need(r"^%(\d+)\(functy\.(\d+)\)\(((?:%\d+(?:, %\d+)*)?)\)(?: cc=\S+)?$")
        r["callee"] = int(m.group(1))
        inst["sig"] = int(m.group(2))
        inst["args"] = _ids(m.group(3))
    elif mnem == "dialect_op":
        # Crystal D11: the ONE dialect op with an image, spelled exactly (display.rs), with a
        # symbol carrying no quote or backslash; any other spelling stays unimaged.
        if rest.startswith(TLS_OP_TEXT) and rest.endswith('"]'):
            sym = rest[len(TLS_OP_TEXT):-2]
            if sym and '"' not in sym and "\\" not in sym:
                inst["tls_symbol"] = sym
    elif mnem == "br":
        need(r"^bb\d+(?:\((?:%\d+(?:, %\d+)*)?\))?$")
        inst["succ"] = _targets(rest)
    elif mnem == "condbr":
        m = need(r"^%(\d+), (bb\d+(?:\([^)]*\))?), (bb\d+(?:\([^)]*\))?)$")
        r["cond"] = int(m.group(1))
        inst["succ"] = _targets(m.group(2)) + _targets(m.group(3))
    elif mnem == "switch":
        m = need(r"^%(\d+) \[((?: -?\d+: bb\d+(?:\([^)]*\))?)*) default: (bb\d+(?:\([^)]*\))?) \]$")
        r["selector"] = int(m.group(1))
        inst["succ"] = _targets(m.group(2)) + _targets(m.group(3))
    elif mnem == "ret":
        need(r"^(?:%\d+(?:, %\d+)*)?$")
    elif mnem == "unreachable":
        need(r"^$")
    # Crystal D10: the native atomics' operands (display.rs `write_inst`).
    elif mnem == "atomic_load":
        r["ptr"] = int(need(r"^\S+ .+, ptr %(\d+)$").group(1))
    elif mnem == "atomic_store":
        m = need(r"^\S+ .+ %(\d+), ptr %(\d+)$")
        r["value"], r["ptr"] = int(m.group(1)), int(m.group(2))
    elif mnem == "atomicrmw":
        m = need(r"^([a-z]+) \S+ .+ ptr %(\d+), %(\d+)$")
        inst["rmw_op"] = m.group(1)
        r["ptr"], r["value"] = int(m.group(2)), int(m.group(3))
    elif mnem == "cmpxchg":
        m = need(r"^(weak )?.+ ptr %(\d+), %(\d+), %(\d+) \S+ \S+$")
        inst["weak"] = bool(m.group(1))
        r["ptr"], r["expected"], r["desired"] = int(m.group(2)), int(m.group(3)), int(m.group(4))
    elif mnem == "fence":
        need(r"^\S+$")
    if volatile and mnem not in ("load", "store"):
        raise Refusal(f"`volatile` on {mnem}: {line!r}")
    if kind in TYPED_FIELDS:
        inst["opnd_tys"], inst["opnd_const"] = operand_nodes(kind, rest)
    return inst


def _strip_comment(s):
    q = s.rfind('"')
    k = s.find("  ;", q + 1 if q >= 0 else 0)
    return (s[:k] if k >= 0 else s).rstrip()


def check_v3_fields(man):
    """Refuse a manifest that claims schema v3 without its v3 fields, well formed.

    `type(x) is int`, not isinstance: a JSON `true` is a Python bool, which IS an int. A
    member's calls are one per MIR block in block order, so their `bb`s strictly increase
    and each is below the member's `mir_blocks`.
    """
    if type(man.get("fuel")) is not int or man["fuel"] < 1:
        raise Refusal("v3 manifest has no well-typed `fuel` (the member cap in effect)")
    if type(man.get("fuel_exhausted")) is not bool:
        raise Refusal("v3 manifest has no well-typed `fuel_exhausted`")
    if man["fuel_exhausted"] and man.get("closed") is True:
        raise Refusal("v3 manifest says `closed` with its member fuel exhausted: contradictory")
    for k, mem in enumerate(man["members"]):
        digest = mem.get("mir_digest")
        if not (isinstance(digest, str) and MIR_DIGEST_RE.match(digest)
                and digest != ZERO_MIR_DIGEST):
            raise Refusal(f"v3 manifest member #{k} has no well-formed `mir_digest` "
                          f"(sha256:<64 hex>, non-zero): {digest!r}")
        n_blocks = mem.get("mir_blocks")
        if type(n_blocks) is not int:
            raise Refusal(f"v3 manifest member #{k} has no `mir_blocks` to bound its call bbs")
        prev = -1
        for j, c in enumerate(mem["calls"]):
            bb = c.get("bb")
            if not (type(bb) is int and prev < bb < n_blocks):
                raise Refusal(f"v3 manifest member #{k} call {j} has no `bb` in "
                              f"({prev}, {n_blocks}): {bb!r}")
            prev = bb


def parse_artifact(artifact_dir):
    cdir = os.path.join(artifact_dir, "callees")
    mpath = os.path.join(cdir, f"{CRATE}.callees.manifest.json")
    tpath = os.path.join(cdir, f"{CRATE}.callees.trust-ir.txt")
    for p in (mpath, tpath):
        if not os.path.isfile(p):
            raise Refusal(f"missing artifact file {p}")
    mraw = open(mpath, "rb").read()
    traw = open(tpath, "rb").read()
    try:
        man = json.loads(mraw)
    except ValueError as exc:
        raise Refusal(f"manifest is not JSON: {exc}") from exc
    if not isinstance(man, dict):
        raise Refusal("manifest is not a JSON object")
    for key in ("schema", "members", "lowering", "artifacts", "crate", "escaping"):
        if key not in man:
            raise Refusal(f"manifest has no {key!r} key (refused, never read as empty)")
    if man["schema"] not in KNOWN_MANIFEST_SCHEMAS:
        raise Refusal(f"unknown manifest schema {man['schema']!r}")
    if man["crate"] != CRATE:
        raise Refusal(f"manifest crate {man['crate']!r} is not {CRATE!r}")
    if man["lowering"] != "ok":
        raise Refusal(f"manifest lowering={man['lowering']!r}: a partially lowered bundle is "
                      f"not comparable to the baseline")
    arts = man["artifacts"]
    if not isinstance(arts, dict) or not isinstance(arts.get("text_bytes"), int) \
            or arts.get("text") != os.path.basename(tpath):
        raise Refusal("manifest artifacts.text / artifacts.text_bytes missing or not this file")
    if len(traw) != arts["text_bytes"]:
        raise Refusal(f"sidecar text is {len(traw)} bytes, manifest says {arts['text_bytes']}: "
                      f"truncated or not the manifest's text")
    if not isinstance(man["escaping"], list):
        raise Refusal("manifest escaping is not a list")
    members = man["members"]
    if not isinstance(members, list) or not members:
        raise Refusal("manifest members is empty or not a list")
    for k, mem in enumerate(members):
        if not isinstance(mem, dict) or mem.get("sidecar_func_id") != k \
                or not isinstance(mem.get("name"), str) or not isinstance(mem.get("calls"), list):
            raise Refusal(f"manifest member #{k} is malformed (id/name/calls)")
        for c in mem["calls"]:
            if not isinstance(c, dict) or not isinstance(c.get("class"), str):
                raise Refusal(f"manifest member #{k} has a call record with no class")
    if man["schema"] == MANIFEST_SCHEMA_V3:
        check_v3_fields(man)

    try:
        text = traw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise Refusal(f"sidecar text is not UTF-8: {exc}") from exc
    if not text.endswith("\n"):
        raise Refusal("sidecar text does not end with a newline: truncated")
    lines = text[:-1].split("\n")
    if lines[0] != TEXT_HEADER:
        raise Refusal(f"sidecar text does not start with {TEXT_HEADER!r}")
    funcs = []
    globals_n = 0
    globals_list = []
    types = {}
    functys = {}
    ub_sites = []
    cur = None
    spellings = tir_symbols.Spellings()
    for ln_no, ln in enumerate(lines[1:], start=2):
        if cur is None:
            if ln == "":
                continue
            # Crystal memo §18: an undefined-behaviour halt obligation must be SITED; its site is
            # the node the projector images as `unreachable`.
            if ln.startswith("obligation ") and UB_HALT_WORDING in ln and '"reaching `' in ln:
                um = UB_HALT_OBL_RE.match(ln)
                if not um:
                    raise Refusal(f"sidecar text line {ln_no}: an undefined-behaviour halt "
                                  f"obligation with no site (its halt cannot be located)")
                ub_sites.append((int(um.group(1)), f"bb{um.group(2)}", int(um.group(3))))
            try:
                fh = tir_symbols.parse_fn_header(ln, FN_PREFIX)
                if fh is not None:
                    spellings.note(fh[2], f"line {ln_no}")
            except tir_symbols.SymbolRefusal as exc:
                raise Refusal(f"sidecar text line {ln_no}: {exc}") from exc
            if fh is not None:
                cur = {"name": fh[0], "blocks": [], "line": ln_no, "functy": fh[1]}
                funcs.append(cur)
                continue
            fym = re.match(r"^functy\.(\d+) = (.+)$", ln)
            if fym:
                functys[int(fym.group(1))] = fym.group(2)
            if ln.startswith("global "):
                # Parsed below, once the function names are known (`symaddr<NAME>`).
                globals_n += 1
                globals_list.append(ln)
            tm = re.match(r"^type ty\.(\d+) = (.+)$", ln)
            if tm:
                types[int(tm.group(1))] = tm.group(2)
            elif ln.startswith("type "):
                raise Refusal(f"sidecar text line {ln_no}: unparsed type-table row {ln[:80]!r}")
            if not TOPLEVEL_OK.match(ln):
                raise Refusal(f"sidecar text line {ln_no}: unknown top-level form {ln[:80]!r}")
            continue
        if ln == "}":
            if not cur["blocks"]:
                # A bodiless DECLARATION. Whether one may stand here (only after the members,
                # only for a foreign premise) is decided below, once the member count is known.
                cur["decl"] = True
                cur = None
                continue
            last = cur["blocks"][-1]
            if not last["insts"] or last["insts"][-1]["mnem"] not in TERMINATORS:
                raise Refusal(f"function {cur['name'][:80]}: last block has no terminator")
            cur = None
            continue
        bm = BLOCK_RE.match(ln)
        if bm:
            if cur["blocks"]:
                prev = cur["blocks"][-1]
                if not prev["insts"] or prev["insts"][-1]["mnem"] not in TERMINATORS:
                    raise Refusal(f"function {cur['name'][:80]}: block {prev['label']} "
                                  f"has no terminator")
            params = [int(x) for x in re.findall(r"%(\d+):", bm.group(2) or "")]
            cur["blocks"].append({"label": bm.group(1), "params": params, "insts": []})
            continue
        if ln.startswith("    "):
            s = ln.strip()
            if s.startswith("; #producer:"):
                # Crystal step 19: the stamp that separates a SUPPLIED intrinsic body from a member.
                cur["producer"] = s[len("; #producer:"):].strip()
                continue
            if s.startswith(";"):
                continue
            if not cur["blocks"]:
                raise Refusal(f"sidecar text line {ln_no}: instruction before the first block")
            blk = cur["blocks"][-1]
            if blk["insts"] and blk["insts"][-1]["mnem"] in TERMINATORS:
                raise Refusal(f"sidecar text line {ln_no}: instruction after a terminator")
            blk["insts"].append(parse_inst(_strip_comment(s)))
            continue
        raise Refusal(f"sidecar text line {ln_no}: unparsed line inside a function {ln[:80]!r}")
    if cur is not None:
        raise Refusal(f"function {cur['name'][:80]} is never closed: truncated text")
    fn_names = frozenset(f["name"] for f in funcs)
    globals_list = [parse_global(ln, fn_names) for ln in globals_list]
    try:
        for g in globals_list:
            spellings.note(g["spelling"], f"global {g['name'][:80]!r}")
    except tir_symbols.SymbolRefusal as exc:
        raise Refusal(f"sidecar text: {exc}") from exc
    # #functions = #members + #declarations: one `fn` per member, in sidecar_func_id order,
    # then the bodiless declarations of FOREIGN premises (the `premise-decls` lane). A body past
    # the members, a bodiless member, a declaration of a non-foreign item or one declared twice
    # is a refusal.
    n_members = len(members)
    if len(funcs) < n_members:
        raise Refusal(f"text has {len(funcs)} functions, manifest {n_members} members")
    # Crystal step 19 (`intrinsic-arms` lane): SUPPLIED intrinsic bodies sit between the members
    # and the declarations, each stamped `; #producer: "trust-intrinsic-arm"`, named a core
    # intrinsic whose body the lane supplies, admitted only from a manifest naming the lane (the
    # same rule as the link-3 reconcile's /8). A supplied body IS a body: the closure walks it.
    n_supplied = 0
    while n_members + n_supplied < len(funcs) \
            and not funcs[n_members + n_supplied].get("decl") \
            and funcs[n_members + n_supplied].get("producer") == SUPPLIED_PRODUCER_TEXT:
        n_supplied += 1
    producer = man.get("producer") if isinstance(man.get("producer"), dict) else {}
    if n_supplied and not isinstance(producer.get("intrinsic_arms"), str):
        raise Refusal(f"text carries {n_supplied} supplied intrinsic bod(y/ies) but the manifest's "
                      f"producer does not name the `intrinsic_arms` lane")
    value_lanes = producer.get("value_lanes")
    if value_lanes is not None and not isinstance(value_lanes, str):
        raise Refusal("manifest producer `value_lanes` is not a string")
    value_lanes = value_lanes or ""
    # Crystal D13 (`fnptr-thunks` lane): SUPPLIED ABI thunks follow the supplied intrinsic bodies,
    # each stamped `; #producer: "trust-abi-thunk"`, admitted only from a manifest naming the lane,
    # and each checked to be EXACTLY the rust-call spread of one member shim (`check_thunk`).
    n_thunks = 0
    base = n_members + n_supplied
    while base + n_thunks < len(funcs) and not funcs[base + n_thunks].get("decl") \
            and funcs[base + n_thunks].get("producer") == THUNK_PRODUCER_TEXT:
        n_thunks += 1
    if n_thunks and "fnptr-thunks:" not in value_lanes:
        raise Refusal(f"text carries {n_thunks} supplied ABI thunk(s) but the manifest's producer "
                      f"does not name the `fnptr-thunks` lane")
    thunk_of = {}
    for k in range(base, base + n_thunks):
        shim = check_thunk(funcs, k, n_members, functys)
        if shim in thunk_of:
            raise Refusal(f"shim #{shim} has two ABI thunks")
        thunk_of[shim] = k
        funcs[k]["thunk_of"] = shim
    supplied_names = set()
    for k in range(n_members, n_members + n_supplied):
        name = funcs[k]["name"]
        stem = name.split("::<", 1)[0]
        if not (stem.startswith("core::intrinsics::") and stem.count("::") == 2
                and stem.rsplit("::", 1)[1] in SUPPLIED_ARM_HEADS) or name in supplied_names:
            raise Refusal(f"supplied body #{k} {name[:80]!r} is not a core intrinsic the lane "
                          f"supplies, or appears twice")
        supplied_names.add(name)
    decl_names = set()
    for k, f in enumerate(funcs):
        if k < n_members and f.get("decl"):
            raise Refusal(f"function #{k} {f['name'][:60]!r} is a MEMBER and has no blocks")
        if n_members <= k < n_members + n_supplied + n_thunks:
            continue
        if k >= n_members:
            if not f.get("decl"):
                raise Refusal(f"text has {len(funcs)} functions, manifest {n_members} members, and "
                              f"function #{k} past the members has a body")
            if not FOREIGN_ITEM_RE.search(f["name"]):
                raise Refusal(f"declaration #{k} {f['name'][:80]!r} is not an {{extern#N}} foreign "
                              f"item; a bodiless declaration is admitted only as a FOREIGN premise")
            if f["name"] in decl_names:
                raise Refusal(f"declaration #{k} {f['name'][:80]!r} is declared twice")
            decl_names.add(f["name"])
    for k, (f, mem) in enumerate(zip(funcs, members)):
        if f["name"] != mem["name"]:
            raise Refusal(f"function #{k} is {f['name'][:60]!r} in the text but "
                          f"{mem['name'][:60]!r} in the manifest")
        labels = {b["label"] for b in f["blocks"]}
        if len(labels) != len(f["blocks"]):
            raise Refusal(f"function #{k}: duplicate block labels")
        for b in f["blocks"]:
            for i in b["insts"]:
                for t, _ in i.get("succ", ()):
                    if t not in labels:
                        raise Refusal(f"function #{k}: branch to missing block {t}")
                if i["mnem"] == "call" and not 0 <= i["callee"] < len(funcs):
                    raise Refusal(f"function #{k}: call @func.{i['callee']} out of range")
                if i["mnem"] == "global_addr" and not 0 <= i["global"] < globals_n:
                    raise Refusal(f"function #{k}: global_addr @global.{i['global']} names no "
                                  f"declared global")
    # Cross-check: IR call edges == manifest `member` edges, per function. A call to a
    # DECLARATION is not a member edge; it must name a callee the manifest lists for this
    # member (its foreign-terminal, or escaping, row), and every declaration must be called.
    by_name = {}
    for k, mem in enumerate(members):
        by_name.setdefault(mem["name"], k)
    called_decls = set()
    for k, (f, mem) in enumerate(zip(funcs, members)):
        all_edges = {i["callee"] for b in f["blocks"] for i in b["insts"] if i["mnem"] == "call"}
        ir_edges = {c for c in all_edges if c < n_members}
        listed = {c.get("resolved") for c in mem["calls"] if c["class"] != "member"}
        for c in sorted(all_edges - ir_edges):
            if funcs[c]["name"] not in listed:
                raise Refusal(f"member #{k} {f['name'][:60]}: calls declaration or supplied body "
                              f"{funcs[c]['name'][:60]!r}, which no non-member call row of it names")
            called_decls.add(c)
        man_edges = set()
        for c in mem["calls"]:
            if c["class"] == "member":
                if c.get("resolved") not in by_name:
                    raise Refusal(f"member #{k}: a `member` call resolves to no member")
                man_edges.add(by_name[c["resolved"]])
        if ir_edges != man_edges:
            raise Refusal(f"member #{k} {f['name'][:60]}: IR call edges and manifest member "
                          f"calls disagree")
    uncalled = [funcs[c]["name"][:80] for c in range(n_members, len(funcs))
                if c not in called_decls and "thunk_of" not in funcs[c]]
    if uncalled:
        raise Refusal(f"declaration(s) or supplied bod(y/ies) no member calls: {uncalled[:3]}")
    tls_certified = read_tls_cells(man, value_lanes)
    mark_ub_halts(funcs, ub_sites)
    by_value_sites = annotate_by_value(funcs, members, man["escaping"], value_lanes, functys,
                                       thunk_of, text)
    return {
        "funcs": funcs,
        "declarations": len(funcs) - n_members - n_supplied - n_thunks,
        "supplied_bodies": n_supplied,
        "abi_thunks": n_thunks,
        "ub_halt_sites": len(ub_sites),
        "globals": globals_n,
        "globals_list": globals_list,
        "fn_names": fn_names,
        "types": types,
        "manifest_sha256": hashlib.sha256(mraw).hexdigest(),
        "text_sha256": hashlib.sha256(traw).hexdigest(),
        "text_bytes": len(traw),
        "members": len(members),
        "escaping_rows": len(man["escaping"]),
        "tls_certified": tls_certified,
        "by_value_sites": by_value_sites,
        "functys": functys,
    }


def _insertfield_parts(text):
    m = re.match(r"^%(\d+) = insertfield (.+) %(\d+), (\d+), %(\d+)$", text)
    return (int(m.group(1)), m.group(2), int(m.group(3)), int(m.group(4)), int(m.group(5))) if m else None


def check_thunk(funcs, k, n_members, functys):
    """Crystal D13: function #k must be EXACTLY the supplied ABI thunk of one member shim -- named
    `<shim>#trust-abi-thunk`, one block `bb0(%p0..%pn-1)` of
    `const () phantomdata; const (T..) {..}; insertfield (T..) .., i, %pi (i = 0..n-1, a chain);
    call @func.<shim>(%env, %last); ret`, at the shim's signature with the environment and the
    tuple spread: shim `((), (T..)) -> R`, thunk `(T..) -> R`. Returns the shim's id."""
    f = funcs[k]
    name = f["name"]
    if not name.endswith(THUNK_SUFFIX):
        raise Refusal(f"ABI thunk #{k} {name[:80]!r} is not named `<shim>{THUNK_SUFFIX}`")
    shims = [j for j in range(n_members) if funcs[j]["name"] == name[:-len(THUNK_SUFFIX)]]
    if len(shims) != 1:
        raise Refusal(f"ABI thunk #{k} {name[:80]!r} names no member shim, or several")
    j = shims[0]
    bad = Refusal(f"ABI thunk #{k} {name[:80]!r} is not the exact rust-call spread of its shim")
    if len(f["blocks"]) != 1 or f["blocks"][0]["label"] != "bb0":
        raise bad
    b = f["blocks"][0]
    params, ins = b["params"], b["insts"]
    n = len(params)
    if n < 1 or len(ins) != n + 4:
        raise bad
    env, seed = ins[0], ins[1]
    if env["mnem"] != "const" or env.get("const_ty") != "()" \
            or env.get("const_value") != "phantomdata" or len(env["res"]) != 1:
        raise bad
    tup = seed.get("const_ty") or ""
    if seed["mnem"] != "const" or len(seed["res"]) != 1 or not tup.startswith("(") \
            or _functy_arity(tup + " -> ()") != n:
        raise bad
    cur = seed["res"][0]
    for i in range(n):
        parts = _insertfield_parts(ins[2 + i]["text"])
        if parts is None or parts[1] != tup or parts[2] != cur or parts[3] != i \
                or parts[4] != params[i]:
            raise bad
        cur = parts[0]
    call, ret = ins[2 + n], ins[3 + n]
    if call["mnem"] != "call" or call["callee"] != j or call["roles"]["args"] != [env["res"][0], cur]:
        raise bad
    if ret["mnem"] != "ret" or ret["text"] != ("ret" if not call["res"] else f"ret %{call['res'][0]}"):
        raise bad
    sdef = functys.get(funcs[j]["functy"]) or ""
    tdef = functys.get(f["functy"]) or ""
    if not sdef.startswith("((), ") or not sdef[len("((), "):].startswith(tup) \
            or tdef != tup + sdef[len("((), ") + len(tup) + 1:]:
        raise bad
    return j


def mark_ub_halts(funcs, ub_sites):
    """Crystal memo §18: mark each sited undefined-behaviour halt. The projector images a site
    that is an `assert` of a `const bool false` bound before it in its block as `unreachable`
    (`ub_halt`), and refuses the body at any other site (`ub_halt_bad`)."""
    for fid, label, idx in ub_sites:
        if not 0 <= fid < len(funcs):
            raise Refusal(f"an undefined-behaviour halt obligation names function {fid}, out of range")
        blk = next((b for b in funcs[fid]["blocks"] if b["label"] == label), None)
        if blk is None or not 0 <= idx < len(blk["insts"]):
            raise Refusal(f"an undefined-behaviour halt obligation names {label}#{idx} of function "
                          f"{fid}, which does not exist")
        i = blk["insts"][idx]
        falses = {v for x in blk["insts"][:idx] if x["mnem"] == "const"
                  and x.get("const_ty") == "bool" and x.get("const_value") == "false" for v in x["res"]}
        if i["mnem"] == "assert" and i["roles"]["cond"] in falses:
            i["ub_halt"] = True
        else:
            i["ub_halt_bad"] = True


def read_tls_cells(man, value_lanes):
    """Crystal D11: the symbols the manifest's `tls_cells` rows CERTIFY (lane `tls-cells`). Rows
    present without the lane named, or malformed, are a refusal; absent, nothing is certified."""
    rows = man.get("tls_cells")
    if rows is None:
        return frozenset()
    if "tls-cells:" not in value_lanes:
        raise Refusal("manifest carries `tls_cells` rows but its producer does not name the "
                      "`tls-cells` lane")
    if not isinstance(rows, list):
        raise Refusal("manifest `tls_cells` is not a list")
    out = set()
    for k, row in enumerate(rows):
        if not isinstance(row, dict) or not isinstance(row.get("symbol"), str) \
                or type(row.get("certified")) is not bool \
                or any(type(row.get(f)) is not bool for f in
                       ("unique_symbol", "pointer_free", "definitely_not_sync")):
            raise Refusal(f"manifest tls_cells row {k} is malformed")
        want = row["unique_symbol"] and row["pointer_free"] and row["definitely_not_sync"]
        if row["certified"] != want:
            raise Refusal(f"manifest tls_cells row {k}: `certified` is not the conjunction of its "
                          f"three facts")
        if row["certified"]:
            out.add(row["symbol"])
    return frozenset(out)


INDIRECT_ALL_MEMBERS = "(every enumerated target is a member)"
INDIRECT_SCAN_COMPLETE = ("(crate-wide address-taken scan: no body of this crate could take an "
                          "address at this type unseen;")


def _tile_targets(content, n, names):
    """The member names whose sorted `", "`-join is exactly `content` (n of them), or None when no
    UNIQUE tiling exists -- ambiguity is a refusal to credit, never a guess."""
    cands = sorted(nm for nm in names if nm in content)
    sols = []

    def go(i, acc):
        if len(sols) > 1:
            return
        if i == len(content):
            if len(acc) == n:
                sols.append(list(acc))
            return
        for nm in cands:
            if content.startswith(nm, i):
                j = i + len(nm)
                if j == len(content):
                    go(j, acc + [nm])
                elif content.startswith(", ", j):
                    go(j + 2, acc + [nm])
    go(0, [])
    if len(sols) != 1 or sols[0] != sorted(sols[0]):
        return None
    return sols[0]


def _functy_arity(defn):
    """Parameter count of a `functy.N = (P, ..) -> (R..)` definition, or None when unparsed."""
    if not defn.startswith("("):
        return None
    depth = 0
    for j, ch in enumerate(defn):
        if ch in "([{<":
            depth += 1
        elif ch in ")]}>":
            depth -= 1
            if depth == 0:
                inner = defn[1:j]
                if not inner.strip():
                    return 0
                d, n = 0, 1
                for c in inner:
                    if c in "([{<":
                        d += 1
                    elif c in ")]}>":
                        d -= 1
                    elif c == "," and d == 0:
                        n += 1
                return n
    return None


def annotate_by_value(funcs, members, escaping, value_lanes, functys, thunk_of=None, text=""):
    """Crystal D1: mark each `call_indirect` DISPATCHED BY VALUE with its target function ids.

    Credited only when ALL hold, the link-3 reconcile's rule /6 plus the signature: the block
    carries no `assert` of a `const bool false` (the bridge's marker); the manifest's producer
    names `indirect-by-value`; every indirect escaping row of the member states an all-member,
    scan-complete enumeration, and all of them the SAME targets, read by an unambiguous tiling of
    member names; every target's declared functy DEFINITION equals the call's; and the call
    passes exactly that functy's arity. A site that fails any check keeps the `call_unknown`
    policy. Returns the credited sites, (function id, block label, [target ids])."""
    out = []
    if "indirect-by-value:" not in value_lanes:
        return out
    name_to_id = {m["name"]: k for k, m in enumerate(members)}
    names = list(name_to_id)
    for k, f in enumerate(funcs[:len(members)]):
        sites = [(b, i) for b in f["blocks"] for i in b["insts"] if i["mnem"] == "call_indirect"]
        if not sites:
            continue
        false_ids = set()
        for b in f["blocks"]:
            for i in b["insts"]:
                if i["mnem"] == "const" and i["const_ty"] == "bool" and i["const_value"] == "false":
                    false_ids.update(i["res"])
                elif i["mnem"] == "copy" and i["roles"]["operand"] in false_ids:
                    false_ids.update(i["res"])
        prefix = f["name"] + ": indirect call (non-const func operand of type "
        rows = [r for r in escaping if isinstance(r, str) and r.startswith(prefix)]
        tsets = []
        for r in rows:
            m = re.search(r"; enumerated targets (\d+) \[(.*)\] " + re.escape(INDIRECT_ALL_MEMBERS), r)
            if not m or INDIRECT_SCAN_COMPLETE not in r:
                tsets = None
                break
            tiled = _tile_targets(m.group(2), int(m.group(1)), names)
            if tiled is None:
                tsets = None
                break
            tsets.append(tuple(tiled))
        if not tsets or len(set(tsets)) != 1:
            continue
        targets = [name_to_id[t] for t in tsets[0]]
        # Crystal D13 (`fnptr-thunks`): every value that names a thunked shim at a functy names
        # its THUNK, so the site dispatches to the thunks -- credited only when the lane is named,
        # every target has one, and no constant anywhere names the SHIM itself as a value.
        cands = [targets]
        if thunk_of and "fnptr-thunks:" in value_lanes and all(t in thunk_of for t in targets) \
                and not any(f"fndef<func.{t}>" in text for t in targets):
            cands.append([thunk_of[t] for t in targets])
        for b, i in sites:
            if any(x["mnem"] == "assert" and x["roles"]["cond"] in false_ids for x in b["insts"]):
                continue
            call_def = functys.get(i["sig"])
            if call_def is None or _functy_arity(call_def) != len(i["args"]):
                continue
            chosen = next((c for c in cands
                           if all(functys.get(funcs[t]["functy"]) == call_def for t in c)), None)
            if chosen is None:
                continue
            i["by_value_targets"] = chosen
            out.append((k, b["label"], chosen))
    return out


# ---------------------------------------------------------------------------
# Analyses.
# ---------------------------------------------------------------------------
def find_targets(funcs):
    out = {}
    for t in TARGETS:
        hits = [k for k, f in enumerate(funcs)
                if f["name"].split("::<__trust")[0].startswith(TARGET_PREFIX)
                and f["name"].split("::<__trust")[0].endswith(f">::{t}")]
        if len(hits) != 1:
            raise Refusal(f"target {t}: {len(hits)} matching functions (need exactly one)")
        out[t] = hits[0]
    return out


def closure(funcs, root):
    """The BODIES reachable through `call` edges. A bodiless declaration is not a body, so it
    is never counted as a closure member; a call to one still blocks its block, because a
    declaration never enters the returning set (see `_can_return`)."""
    seen = {root}
    stack = [root]
    while stack:
        k = stack.pop()
        for b in funcs[k]["blocks"]:
            for i in b["insts"]:
                c = i["mnem"] == "call" and i["callee"]
                nxt = [c] if c is not False else list(i.get("by_value_targets") or ())
                for c in nxt:
                    if c not in seen and not funcs[c].get("decl"):
                        seen.add(c)
                        stack.append(c)
    return seen


def seq_imaged(inst, sem):
    """Crystal D10: True when the projector images this NATIVE atomic under premise SEQ."""
    img = sem.get("seq_atomic_image", {}).get(inst["kind"])
    if img is None:
        return False
    if inst["kind"] == "AtomicRMW":
        return inst.get("rmw_op") in img.get("rmw_ops", {})
    if inst["kind"] == "CmpXchg":
        return not inst.get("weak")
    return True


def unimaged(inst, sem):
    """('kind', variant) / ('op', variant.op) when the instruction has no image."""
    if seq_imaged(inst, sem):
        return None
    # Crystal D11: a certified thread-local address is imaged (`annotate_tls` marks it).
    if inst["mnem"] == "dialect_op" and sem.get("tls_input_image") and inst.get("tls_imaged"):
        return None
    # Crystal memo §18: an undefined-behaviour halt obligation sited off a halting assert has no
    # image (the projector's `fn ub_halt_image` refuses the body).
    if inst.get("ub_halt_bad") and sem.get("ub_halt_image"):
        return ("kind", "ub halt sited off a halting assert")
    if inst["kind"] not in sem["kind_image"]:
        return ("kind", inst["mnem"])
    if inst["kind"] in OPERATOR_FAMILIES:
        if inst["sub"] not in sem["operator_image"][inst["kind"]]:
            return ("op", f"{inst['kind']}.{inst['sub']}")
    return None


def undef_sets(func, propagate):
    """(U0: ids an `undef` binds, D: U0 closed under EvalIR's undef-propagating evaluators)."""
    u0 = set()
    for b in func["blocks"]:
        for i in b["insts"]:
            if i["mnem"] == "undef":
                u0.update(i["res"])
    d = set(u0)
    if not propagate:
        return u0, d
    incoming = {}
    for b in func["blocks"]:
        for i in b["insts"]:
            for t, args in i.get("succ", ()):
                incoming.setdefault(t, []).append(args)
    changed = True
    while changed:
        changed = False
        for bi, b in enumerate(func["blocks"]):
            if bi > 0 and b["params"] and b["label"] in incoming:
                for pos, p in enumerate(b["params"]):
                    if p not in d and all(len(a) > pos and a[pos] in d
                                          for a in incoming[b["label"]]):
                        d.add(p)
                        changed = True
            for i in b["insts"]:
                if not i["res"] or i["res"][0] in d:
                    continue
                r = i["roles"]
                m = i["mnem"]
                hit = (
                    (m == "extractfield" and r["aggregate"] in d)
                    or (m in ("ptr_data", "ptr_metadata") and r["ptr"] in d)
                    or (m == "ptr_from_parts" and r["data"] in d)
                    or (m in ("ptrtoptr", "reify_fn_pointer") and r["operand"] in d)
                    or (m == "select" and r["cond"] not in d and r["then"] in d and r["else"] in d)
                )
                if hit:
                    d.add(i["res"][0])
                    changed = True
    return u0, d


REVIEW_INSERTFIELD = re.compile(r"(?:%\d+ = )?insertfield \S+ (%\d+),")


def static_block_reasons(func, sem, cfg):
    """Per block: list of (family, detail) definite-fault reasons, calls excluded."""
    if cfg.get("unimaged_body") and any(refused_by_projector(i, sem) for b in func["blocks"]
                                       for i in b["insts"]):
        return [[("unimaged_body", "the projector refuses this body")] for _ in func["blocks"]]
    u0, d = undef_sets(func, cfg["propagate"])
    false_ids = set()
    for b in func["blocks"]:
        for i in b["insts"]:
            if i["mnem"] == "const" and i["const_ty"] == "bool" and i["const_value"] == "false":
                false_ids.update(i["res"])
            elif i["mnem"] == "copy" and i["roles"]["operand"] in false_ids:
                false_ids.update(i["res"])
    # Crystal D1: the instruction defining each SSA id (block params have none).
    defs = {}
    if cfg.get("callee_not_fnptr"):
        for b in func["blocks"]:
            for i in b["insts"]:
                for v in i["res"]:
                    defs[v] = i
    out = []
    for b in func["blocks"]:
        reasons = []
        for i in b["insts"]:
            m = i["mnem"]
            r = i["roles"]
            if cfg.get("callee_not_fnptr") and m == "call_indirect":
                cdef = defs.get(r["callee"])
                if cdef is not None and ((cdef["mnem"] == "copy" and not cdef["ty"].startswith("functy."))
                                         or ptr_bitcast_imaged(cdef, sem)):
                    reasons.append(("callee_not_fnptr", f"{cdef['text']} -> {i['text']}"))
            if cfg["undef_insertfield"] == "review" and m == "insertfield":
                mm = REVIEW_INSERTFIELD.match(i["text"])
                if mm and int(mm.group(1)[1:]) in u0:
                    reasons.append(("undef_insertfield", i["text"]))
            if cfg["undef_insertfield"] == "structured" and m == "insertfield" \
                    and r["aggregate"] in d:
                reasons.append(("undef_insertfield", i["text"]))
            if cfg["unimaged_kind"] or cfg["unimaged_op"]:
                u = unimaged(i, sem)
                if u and ((u[0] == "kind" and cfg["unimaged_kind"])
                          or (u[0] == "op" and cfg["unimaged_op"])):
                    reasons.append(("unimaged_" + u[0], u[1]))
            if cfg.get("unimaged_operand"):
                uo = unimaged_operand(i, sem)
                if uo:
                    reasons.append(("unimaged_operand", f"{uo[0]} {uo[1]}"))
            if cfg["unreachable"] and m == "unreachable":
                reasons.append(("unreachable", "unreachable"))
            if m == "assert" and r["cond"] in false_ids and i.get("ub_halt") \
                    and sem.get("ub_halt_image"):
                # Crystal memo §18: the projector images this assert as `unreachable` (ub, never
                # the sanctioned panic), so it is that family.
                if cfg["unreachable"]:
                    reasons.append(("unreachable", "ub halt: " + i["text"]))
            elif cfg["assert_false"] and m == "assert" and r["cond"] in false_ids:
                reasons.append(("assert_false", i["text"]))
            if cfg["undef_other"] and m == "gep" and any(x in d for x in i["gep_indices"]):
                reasons.append(("undef_other", i["text"]))
            for role, v in r.items():
                if not isinstance(v, int) or v not in d:
                    continue
                # Crystal D12: the image is a `copy (ptr)`, whose operand is an undef-checked role.
                if cfg["undef_other"] and role == "operand" and ptr_bitcast_imaged(i, sem):
                    reasons.append(("undef_other", i["text"]))
                if cfg["undef_branch"] and (m, role) in UNDEF_BRANCH_ROLES:
                    reasons.append(("undef_branch", i["text"]))
                if cfg["undef_other"] and (m, role) in UNDEF_OTHER_ROLES:
                    reasons.append(("undef_other", i["text"]))
            if cfg["cast_unmodelled"]:
                if i["kind"] == "Cast" and i["sub"] != "Bitcast":
                    ctor = sem["operator_image"]["Cast"].get(i["sub"])
                    if ctor in sem["unmodelled_cast_ops"]:
                        reasons.append(("cast_unmodelled", i["text"]))
                elif i["kind"] == "Cast":
                    sw, dw = _int_width(i["src_ty"]), _int_width(i["dst_ty"])
                    if ptr_bitcast_imaged(i, sem):
                        pass  # Crystal D12: imaged as `copy (ptr)`, the identity
                    elif sw is None or dw is None or sw != dw:
                        reasons.append(("cast_unmodelled", i["text"]))
                elif i["kind"] == "BinOp":
                    ctor = sem["operator_image"]["BinOp"].get(i["sub"])
                    if ctor in sem["unmodelled_binops"]:
                        reasons.append(("cast_unmodelled", i["text"]))
            if cfg["call_unknown"] and m == "call_indirect" and not i.get("by_value_targets"):
                reasons.append(("call_unknown", i["text"]))
        out.append(reasons)
    return out


def mod_reason(mod, sem, k, cfg=None):
    """The first definite-fault family of function k's entry block (self-test helper)."""
    rs = static_block_reasons(mod["funcs"][k], sem, cfg or PRIMARY)[0]
    return rs[0][0] if rs else None


def block_graph(func):
    """(successors, direct callees, rets, by-value dispatch sets) per block. A by-value
    `call_indirect` (crystal D1) returns when SOME target of its exact, complete set returns."""
    idx = {b["label"]: n for n, b in enumerate(func["blocks"])}
    succ, calls, rets, alts = [], [], [], []
    for b in func["blocks"]:
        term = b["insts"][-1]
        succ.append([idx[t] for t, _ in term.get("succ", ())])
        calls.append(sorted({i["callee"] for i in b["insts"] if i["mnem"] == "call"}))
        rets.append(term["mnem"] == "ret")
        alts.append([tuple(i["by_value_targets"]) for i in b["insts"]
                     if i["mnem"] == "call_indirect" and i.get("by_value_targets")])
    return succ, calls, rets, alts


def _can_return(g, blocked, returns):
    succ, calls, rets, alts = g
    if not succ:
        # A bodiless DECLARATION: the projector omits it, so a call to it is `stuck no_func`
        # (ANCHORS "call_nonreturning"). POLICY, stated: returns-under-contract for a declared
        # premise is E-phase, so today a declaration NEVER returns -- the same verdict the old
        # `assert false; undef` lowering gave the site, reached through no_func instead of ub.
        return False
    seen = {0}
    todo = [0]
    while todo:
        n = todo.pop()
        if blocked[n] or any(c not in returns for c in calls[n]) \
                or any(not any(t in returns for t in alt) for alt in alts[n]):
            continue
        if rets[n]:
            return True
        for s in succ[n]:
            if s not in seen:
                seen.add(s)
                todo.append(s)
    return False


def annotate_globals(mod, sem):
    """Mark each `global_addr` with why the projector cannot image its global (or None)."""
    why = [global_imaged(g, mod["types"], sem["operand_image"], mod.get("fn_names", frozenset()))
           for g in mod["globals_list"]]
    for f in mod["funcs"]:
        for b in f["blocks"]:
            for i in b["insts"]:
                if i["mnem"] == "global_addr":
                    i["global_why"] = why[i["global"]]


def annotate_tls(mod, sem):
    """Crystal D11: mark each `trust_rust.thread_local_addr` op whose symbol the manifest's
    `tls_cells` rows certify -- the projector's `fn tls_input_image` images exactly those."""
    cert = mod.get("tls_certified", frozenset())
    for f in mod["funcs"]:
        for b in f["blocks"]:
            for i in b["insts"]:
                if i["mnem"] == "dialect_op":
                    i["tls_imaged"] = bool(sem.get("tls_input_image")) and i.get("tls_symbol") in cert


def annotate_d14(mod, sem):
    """Crystal D14/E5: mark the first use of a VTABLE word the projector's `fn d14_vtable_certify`
    does not certify. A vtable word is a `ptr_metadata` of a kind `sem["d14_vtable_certify"]`
    seeds, followed through `copy`, a thin-to-thin `bitcast`/`ptrtoptr` and a `gep` of constant
    indices (a byte pointee adds them; any other pointee only with every index zero); a use is
    certified when it is a `load usize` at byte offset 8 or 16, the unchanged word as a vtable
    kind's `ptr_from_parts` metadata, or a follow. Everything else refuses the body."""
    d14 = sem.get("d14_vtable_certify") or {}
    kinds = set(d14.get("seed_kinds", ()))
    if not kinds:
        return
    byte = set(d14["byte_pointees"])
    thin = set(d14["thin_ptr_tys"])
    slots = set(d14["load_slots"])
    for f in mod["funcs"]:
        insts = [i for b in f["blocks"] for i in b["insts"]]
        consts = {}
        for i in insts:
            if i["mnem"] == "const" and i["res"] and re.fullmatch(r"-?\d+", i.get("const_value", "")):
                consts[i["res"][0]] = int(i["const_value"])
        derived, bad = {}, None

        def node(i, field):
            return i.get("opnd_tys", {}).get(field) or (None, None, [])

        def follows(i):
            if i["mnem"] == "copy":
                return i["roles"]["operand"]
            if i["mnem"] in ("bitcast", "ptrtoptr") and node(i, "src_ty")[0] in thin \
                    and node(i, "dst_ty")[0] in thin:
                return i["roles"]["operand"]
            return None

        while bad is None:
            before = len(derived)
            for i in insts:
                if not i["res"] or i["res"][0] in derived:
                    continue
                r0 = i["res"][0]
                if i["mnem"] == "ptr_metadata":
                    pt = node(i, "ptr_ty")
                    if pt[0] == "FatPtr" and pt[1] in kinds:
                        derived[r0] = (r0, 0)
                elif i["mnem"] == "gep" and i["roles"]["base"] in derived:
                    seed, off = derived[i["roles"]["base"]]
                    for ix in i["gep_indices"]:
                        c = consts.get(ix)
                        if c is None or c < 0 or (node(i, "pointee_ty")[0] not in byte and c != 0):
                            bad = i
                            break
                        off += c if node(i, "pointee_ty")[0] in byte else 0
                    if bad is not None:
                        break
                    derived[r0] = (seed, off)
                elif follows(i) in derived:
                    derived[r0] = derived[follows(i)]
            if len(derived) == before:
                break
        if bad is None:
            for i in insts:
                for v in i["uses"]:
                    if v not in derived:
                        continue
                    _seed, off = derived[v]
                    m = i["mnem"]
                    if m == "load" and i["roles"]["ptr"] == v:
                        ok = node(i, "ty")[0] == d14["load_ty"] and off in slots
                    elif m == "gep":
                        ok = i["roles"]["base"] == v and v not in i["gep_indices"]
                    elif follows(i) == v:
                        ok = True
                    elif m == "ptr_from_parts":
                        pt = node(i, "ptr_ty")
                        ok = pt[0] == "FatPtr" and pt[1] in kinds and i["roles"]["meta"] == v \
                            and i["roles"]["data"] != v and off == 0
                    else:
                        ok = False
                    if not ok:
                        bad = i
                        break
                if bad is not None:
                    break
        for i in insts:
            i["d14_uncertified"] = i is bad


def fixpoint(mod, sem, cfg):
    annotate_globals(mod, sem)
    annotate_tls(mod, sem)
    annotate_d14(mod, sem)
    funcs = mod["funcs"]
    graphs = [block_graph(f) for f in funcs]
    blocked = [[bool(r) for r in static_block_reasons(f, sem, cfg)] for f in funcs]
    callers = [set() for _ in funcs]
    for k, g in enumerate(graphs):
        for cs in g[1]:
            for c in cs:
                callers[c].add(k)
        for alt_list in g[3]:
            for alt in alt_list:
                for t in alt:
                    callers[t].add(k)
    if cfg["fixpoint"] == "lfp":
        returns = set()
        work = deque(range(len(funcs)))
        queued = set(work)
        while work:
            k = work.popleft()
            queued.discard(k)
            if k in returns:
                continue
            if _can_return(graphs[k], blocked[k], returns):
                returns.add(k)
                for c in callers[k]:
                    if c not in returns and c not in queued:
                        work.append(c)
                        queued.add(c)
        return returns
    returns = set(range(len(funcs)))
    changed = True
    while changed:
        changed = False
        for k in range(len(funcs)):
            if k in returns and not _can_return(graphs[k], blocked[k], returns):
                returns.discard(k)
                changed = True
    return returns


FAMILIES = ("undef_insertfield", "unreachable", "assert_false", "undef_branch", "undef_other",
            "unimaged_kind", "unimaged_op", "cast_unmodelled", "call_unknown", "unimaged_operand",
            "callee_not_fnptr")
PRIMARY = {"fixpoint": "lfp", "propagate": True, **{f: True for f in FAMILIES},
           "undef_insertfield": "structured"}
REVIEW = {"fixpoint": "gfp", "propagate": False, **{f: False for f in FAMILIES},
          "undef_insertfield": "review"}
LADDER = [
    ("0 l4-review rule: insertfield on an `undef` matched as `insertfield \\S+`, GREATEST "
     "fixpoint", dict(REVIEW)),
    ("1 structured parse: tuple-typed `insertfield (a, b) %u` now seen",
     {"undef_insertfield": "structured"}),
    ("2 LEAST fixpoint", {"fixpoint": "lfp"}),
    ("3 undef propagated through extractfield/ptr_*/ptrtoptr/select/block params",
     {"propagate": True}),
    ("4 + assert of a const false", {"assert_false": True}),
    ("5 + unreachable", {"unreachable": True}),
    ("6 + undef feeding condbr/switch/select/assert", {"undef_branch": True}),
    ("7 + call_indirect never returns (policy)", {"call_unknown": True}),
    ("8 + undef as load/store/gep base, gep index, borrow, call_indirect callee or copy operand",
     {"undef_other": True}),
    ("9 + instruction kind with no IRInst image", {"unimaged_kind": True}),
    ("10 + operator with no alphabet image", {"unimaged_op": True}),
    ("11 + casts/binops EvalIR never models", {"cast_unmodelled": True}),
    ("12 + operand (type/constant/global) the projector cannot image",
     {"unimaged_operand": True}),
    ("13 + a call_indirect callee copied at a non-function type: never an fnptr_ (= the gated "
     "model)", {"callee_not_fnptr": True}),
]
# Not gated: the projector refuses a WHOLE body over one unimaged instruction, so
# in a projected module such a body is absent and a call to it is stuck no_func.
INFORMATIONAL = ("14 (not gated) + the projector refuses the whole body, not one block",
                 {"unimaged_body": True})


def _short(name):
    return name.split("::<__trust")[0][:200]


def _frontier_blocks(mod, sem, cfg, returns, k):
    f = mod["funcs"][k]
    reasons = static_block_reasons(f, sem, cfg)
    succ, calls, rets, alts = block_graph(f)
    out = []
    seen = {0}
    todo = [0]
    while todo:
        n = todo.pop()
        why = [(fam, det[:140]) for fam, det in reasons[n]]
        why += [("call_nonreturning", c) for c in calls[n] if c not in returns]
        why += [("call_nonreturning", alt[0]) for alt in alts[n]
                if not any(t in returns for t in alt)]
        if why:
            out.append((n, why))
            continue
        for s in succ[n]:
            if s not in seen:
                seen.add(s)
                todo.append(s)
    return f, rets, sorted(out)


def frontier(mod, sem, cfg, returns, k):
    """Why body k cannot return: the blocked blocks reachable from its entry
    (every entry-to-ret path crosses one), and one chain of first blockers
    followed through non-returning callees down to a local fault."""
    f, rets, out = _frontier_blocks(mod, sem, cfg, returns, k)

    def render(why):
        return [f"call_nonreturning: {_short(mod['funcs'][d]['name'])}" if fam ==
                "call_nonreturning" else f"{fam}: {d}" for fam, d in why]
    chain = []
    cur, seen = k, set()
    while cur not in seen and len(chain) < 16:
        seen.add(cur)
        if mod["funcs"][cur].get("decl"):
            chain.append({"function": _short(mod["funcs"][cur]["name"]), "block": None,
                          "first_blocker": "bodiless declaration of a FOREIGN premise: stuck no_func "
                                           "(returns-under-contract is E-phase)"})
            break
        cf, _, cout = _frontier_blocks(mod, sem, cfg, returns, cur)
        if not cout:
            chain.append({"function": _short(cf["name"]), "block": None,
                          "first_blocker": "no ret block at all"})
            break
        n, why = cout[0]
        fam, det = why[0]
        chain.append({"function": _short(cf["name"]), "block": cf["blocks"][n]["label"],
                      "first_blocker": render([why[0]])[0]})
        if fam != "call_nonreturning":
            break
        cur = det
    return {"ret_blocks": [f["blocks"][n]["label"] for n in range(len(rets)) if rets[n]],
            "blocked_frontier": [{"block": f["blocks"][n]["label"], "reasons": render(why)[:6],
                                  "reasons_total": len(why)} for n, why in out],
            "first_blocker_chain": chain}


def havoc_census(funcs, members):
    """Undef defs in `members`, classified by how they are used."""
    total = agg = value = unused = 0
    review_value = 0
    review_split = Counter()
    by_type = Counter()
    branch_direct = 0
    branch_bodies = set()
    bodies_with_value = set()
    for k in sorted(members):
        f = funcs[k]
        undefs = {}
        for b in f["blocks"]:
            for i in b["insts"]:
                if i["mnem"] == "undef":
                    undefs[i["res"][0]] = i["ty"]
        if not undefs:
            continue
        uses = {u: [] for u in undefs}
        for b in f["blocks"]:
            for i in b["insts"]:
                if i["mnem"] == "undef":
                    continue
                for v in set(i["uses"]):
                    if v in uses:
                        uses[v].append(i)
        for u, ty in undefs.items():
            total += 1
            us = uses[u]
            if not us:
                unused += 1
            elif all(i["mnem"] == "insertfield" and i["roles"]["aggregate"] == u
                     and i["roles"]["value"] != u for i in us):
                agg += 1
            else:
                value += 1
                bodies_with_value.add(k)
                cls = ("unit" if ty == "()" else "tuple" if ty.startswith("(") else
                       ty.split(".")[0].split("<")[0])
                by_type[cls] += 1
            if any((i["mnem"] == "condbr" and i["roles"]["cond"] == u)
                   or (i["mnem"] == "switch" and i["roles"]["selector"] == u) for i in us):
                branch_direct += 1
                branch_bodies.add(k)
            # The review's literal rule: VALUE unless every use line matches
            # `insertfield \S+ %u,` (types with a space never match) and there is one.
            tok = re.compile(r"%" + str(u) + r"\b")
            rus = [i["text"] for i in us if tok.search(i["text"])]
            ok = bool(rus) and all(re.match(r"(%\d+ = )?insertfield \S+ %" + str(u) + ",", t)
                                   for t in rus)
            if not ok:
                review_value += 1
                review_split["value" if us and not all(
                    i["mnem"] == "insertfield" and i["roles"]["aggregate"] == u
                    and i["roles"]["value"] != u for i in us) else
                    "unused" if not us else "aggregate_idiom_the_regex_missed"] += 1
    return {"undef_defs": total, "aggregate_idiom": agg, "value_havoc": value,
            "unused": unused, "value_havoc_bodies": len(bodies_with_value),
            "value_havoc_by_type": dict(sorted(by_type.items())),
            "feeding_condbr_or_switch_directly": branch_direct,
            "bodies_branching_directly_on_undef": len(branch_bodies),
            "review_rule_value_count": review_value,
            "review_rule_value_count_is": dict(sorted(review_split.items()))}


def projectability(funcs, members, sem):
    kind_bodies, op_bodies, proj_bodies = set(), set(), set()
    per_mnem = Counter()
    per_op = Counter()
    per_operand = Counter()
    instances = Counter()
    for k in members:
        seen_m, seen_o, seen_x = set(), set(), set()
        for b in funcs[k]["blocks"]:
            for i in b["insts"]:
                uo = unimaged_operand(i, sem)
                if uo:
                    seen_x.add(f"{uo[0]} {uo[1]}")
                u = unimaged(i, sem)
                if not u:
                    continue
                instances[u[1]] += 1
                if u[0] == "kind":
                    seen_m.add(u[1])
                else:
                    seen_o.add(u[1])
        if seen_m:
            kind_bodies.add(k)
        if seen_m or seen_o:
            op_bodies.add(k)
        if seen_m or seen_o or seen_x:
            proj_bodies.add(k)
        per_mnem.update(seen_m)
        per_op.update(seen_o)
        per_operand.update(seen_x)
    return {"unprojectable_bodies": len(kind_bodies),
            "unprojectable_bodies_operator_level": len(op_bodies),
            "unprojectable_bodies_projector": len(proj_bodies),
            "bodies_per_unimaged_operand": dict(sorted(per_operand.items(), key=lambda x: -x[1])),
            "bodies_per_unimaged_mnemonic": dict(sorted(per_mnem.items(), key=lambda x: -x[1])),
            "bodies_per_unimaged_operator": dict(sorted(per_op.items(), key=lambda x: -x[1])),
            "instances": dict(sorted(instances.items(), key=lambda x: -x[1]))}


def measure(artifact_dir, texts):
    sem = derive_semantics(texts)
    mod = parse_artifact(artifact_dir)
    annotate_globals(mod, sem)
    annotate_tls(mod, sem)
    annotate_d14(mod, sem)
    funcs = mod["funcs"]
    tg = find_targets(funcs)
    closures = {t: closure(funcs, tg[t]) for t in TARGETS}
    primary = fixpoint(mod, sem, PRIMARY)
    metrics = {}
    per_closure = {}
    for t in TARGETS:
        mem = closures[t]
        proj = projectability(funcs, mem, sem)
        hav = havoc_census(funcs, mem)
        nonret = sorted(k for k in mem if k not in primary)
        metrics[f"{t}.unprojectable_bodies"] = proj["unprojectable_bodies"]
        metrics[f"{t}.unprojectable_bodies_operator_level"] = \
            proj["unprojectable_bodies_operator_level"]
        metrics[f"{t}.unprojectable_bodies_projector"] = proj["unprojectable_bodies_projector"]
        metrics[f"{t}.non_returning_bodies"] = len(nonret)
        metrics[f"{t}.value_havoc_undefs"] = hav["value_havoc"]
        per_closure[t] = {"root": funcs[tg[t]]["name"], "closure_bodies": len(mem),
                          "projectability": proj, "havoc": hav,
                          "non_returning_bodies": len(nonret),
                          "calls_to_declarations": sum(
                              1 for k in mem for b in funcs[k]["blocks"] for i in b["insts"]
                              if i["mnem"] == "call" and funcs[i["callee"]].get("decl"))}
    metrics["targets.non_returning"] = sum(1 for t in TARGETS if tg[t] not in primary)
    ladder = []
    cfg = {}
    for label, delta in LADDER + [INFORMATIONAL]:
        cfg.update(delta)
        ret = fixpoint(mod, sem, cfg)
        ladder.append({"step": label,
                       "non_returning": {t: sum(1 for k in closures[t] if k not in ret)
                                         for t in TARGETS},
                       "targets_returning": {t: tg[t] in ret for t in TARGETS}})
    last = ladder[len(LADDER) - 1]["non_returning"]
    if any(last[t] != metrics[f"{t}.non_returning_bodies"] for t in TARGETS):
        raise Refusal("internal: the ladder's last gated rung is not the gated model")
    loo = {}
    for fam in FAMILIES:
        c = dict(PRIMARY)
        c[fam] = False
        ret = fixpoint(mod, sem, c)
        loo[fam] = {"non_returning": {t: sum(1 for k in closures[t] if k not in ret)
                                      for t in TARGETS},
                    "targets_returning": {t: tg[t] in ret for t in TARGETS}}
    pending = pending_pin_images(mod, sem, closures, tg)
    report = {
        "schema": SCHEMA,
        "metrics": metrics,
        "identity": identity(mod, sem),
        "artifact": {"dir": os.path.abspath(artifact_dir), "members": mod["members"],
                     "by_value_dispatched_call_indirects": len(mod["by_value_sites"]),
                     "tls_certified_symbols": sorted(mod["tls_certified"]),
                     "tls_input_imaged_ops": sum(1 for f in funcs for b in f["blocks"]
                                                 for i in b["insts"] if i.get("tls_imaged")),
                     "declarations": mod["declarations"],
                     "text_bytes": mod["text_bytes"], "globals": mod["globals"],
                     "manifest_escaping_rows": mod["escaping_rows"]},
        "semantics": {k: v for k, v in sem.items() if k != "digest"},
        "targets": {t: {"name": funcs[tg[t]]["name"], "returns": tg[t] in primary,
                        "why_not": None if tg[t] in primary else
                        frontier(mod, sem, PRIMARY, primary, tg[t])} for t in TARGETS},
        "closures": per_closure,
        "reconciliation_ladder": ladder,
        "leave_one_family_out": loo,
        "pending_pin_images": pending,
        "model": {"gated": "LEAST fixpoint, all families (see the script docstring)",
                  "families": list(FAMILIES), "usize_bits": USIZE_BITS,
                  "lower_bound": "faults are counted only when DEFINITE; undef arithmetic, "
                                 "loads of unwritten cells and undef arguments into callees "
                                 "are not modelled, so non_returning is a lower bound",
                  "declarations": "a bodiless declaration (a FOREIGN premise the bridge's "
                                  "premise-decls lane lowers as a call) is not a closure body and "
                                  "NEVER returns: the projector omits it, so the call is stuck "
                                  "no_func (anchor call_nonreturning). Returns-under-contract is "
                                  "E-phase; until it lands this is the verdict the old `assert "
                                  "false; undef` lowering gave the same site"},
    }
    return report


def _carries_uninit(inst):
    c = inst.get("opnd_const")
    return c is not None and _mentions_uninit(c)


def pending_pin_images(mod, sem, closures, tg):
    """Informational, NOT gated: the gated model re-run with the pending-pin constant images
    (`pending_const_images`) granted -- what link 4 measures once reader A's trust-ir carries
    them. None when nothing is pending."""
    pending = sem.get("pending_const_images") or {}
    if not pending:
        return None
    sem2 = json.loads(json.dumps({k: v for k, v in sem.items() if k != "digest"}))
    sem2["operand_image"]["const_variants"] = sorted(
        set(sem2["operand_image"]["const_variants"]) | set(pending))
    ret = fixpoint(mod, sem2, PRIMARY)
    funcs = mod["funcs"]
    return {
        "gated": False,
        "images": pending,
        "why": "reader A (the binary projector, scripts/crystal_a2_project) is pinned to a "
               "trust-ir with no Constant::Uninit and cannot decode a v42 crystal-lineage blob; "
               "reader B (ir_mint/emitted.rs) images an unwritten lane as (undef) = "
               "IRConst.undef_, whose EvalIR semantics is anchored (ANCHORS uninit.lane)",
        "non_returning": {t: sum(1 for k in closures[t] if k not in ret) for t in TARGETS},
        "targets_returning": {t: tg[t] in ret for t in TARGETS},
        "unprojectable_bodies_projector": {
            t: projectability(funcs, closures[t], sem2)["unprojectable_bodies_projector"]
            for t in TARGETS},
        "bodies_carrying_uninit_lanes": {
            t: sum(1 for k in closures[t] if any(_carries_uninit(i) for b in funcs[k]["blocks"]
                                                 for i in b["insts"])) for t in TARGETS},
    }


def identity(mod, sem):
    return {"manifest_sha256": mod["manifest_sha256"], "text_sha256": mod["text_sha256"],
            "semantics_digest": sem["digest"], "script_sha256": _script_sha256()}


def _script_sha256():
    """The INSTRUMENT's Python digest: this script's bytes, then the bytes of the symbol reader it
    imports (`crystal_trust_ir_symbols.py`), so a change to either moves the identity and can be
    re-seated. Hashing this file alone would leave a reader change un-reseatable."""
    h = hashlib.sha256(open(os.path.abspath(__file__), "rb").read())
    h.update(open(os.path.abspath(tir_symbols.__file__), "rb").read())
    return h.hexdigest()


# ---------------------------------------------------------------------------
# The ratchet.
# ---------------------------------------------------------------------------
def _payload_digest(b):
    body = {k: b[k] for k in ("schema", "metrics", "identity", "history")}
    return hashlib.sha256(json.dumps(body, sort_keys=True).encode()).hexdigest()


def load_baseline(path):
    if not os.path.isfile(path):
        raise Refusal(f"no baseline at {path} (create one with --init --reason TEXT)")
    try:
        b = json.load(open(path))
    except ValueError as exc:
        raise Refusal(f"baseline is not JSON: {exc}") from exc
    for key in ("schema", "metrics", "identity", "history", "payload_sha256"):
        if key not in b:
            raise Refusal(f"baseline has no {key!r}")
    if b["schema"] != BASELINE_SCHEMA:
        raise Refusal(f"baseline schema {b['schema']!r} is not {BASELINE_SCHEMA!r}")
    if b["payload_sha256"] != _payload_digest(b):
        raise Refusal("baseline payload digest does not match its contents: edited by hand. "
                      "Baselines move only through --init / --rebase / --reseat")
    if not isinstance(b["metrics"], dict) or not all(
            isinstance(v, int) and not isinstance(v, bool) and v >= 0
            for v in b["metrics"].values()):
        raise Refusal("baseline metrics must be non-negative integers")
    ident = b["identity"]
    if not isinstance(ident, dict) or sorted(ident) != sorted(
            ("manifest_sha256", "text_sha256", "semantics_digest", "script_sha256")):
        raise Refusal("baseline identity is malformed")
    hist = b["history"]
    if not isinstance(hist, list) or not hist or not isinstance(hist[-1], dict) \
            or hist[-1].get("metrics") != b["metrics"] or hist[-1].get("identity") != ident:
        raise Refusal("baseline metrics/identity are not the ones its last history entry "
                      "recorded: moved by hand")
    return b


def write_baseline(path, metrics, ident, history):
    b = {"schema": BASELINE_SCHEMA,
         "what": "crystal link 4 executability ratchet; every metric is a BAD count, "
                 "derived by scripts/crystal_link4_executability.py from the callee sidecar",
         "metrics": dict(sorted(metrics.items())), "identity": ident, "history": history}
    b["payload_sha256"] = _payload_digest(b)
    tmp = path + ".tmp"
    with open(tmp, "w") as fh:
        json.dump(b, fh, indent=2, sort_keys=False)
        fh.write("\n")
    os.replace(tmp, path)
    return b


def compare(base, report, allow_set_change=False):
    """(exit code, lines) of the gate verdict."""
    got, want = report["metrics"], base["metrics"]
    if set(got) != set(want) and not allow_set_change:
        raise Refusal(f"baseline names metrics {sorted(set(want) ^ set(got))} the measurement "
                      f"does not (or the reverse): the metric set moved, --reseat it")
    lines = []
    common = sorted(set(got) & set(want))
    worse = [k for k in common if got[k] > want[k]]
    better = [k for k in common if got[k] < want[k]]
    same_identity = base["identity"] == report["identity"]
    for k in common:
        tag = "WORSE" if k in worse else "better" if k in better else "="
        lines.append(f"  {k:52s} baseline={want[k]:>6}  measured={got[k]:>6}  {tag}")
    for k in sorted(set(got) - set(want)):
        lines.append(f"  {k:52s} baseline=   new  measured={got[k]:>6}  NEW METRIC")
    for k in sorted(set(want) - set(got)):
        lines.append(f"  {k:52s} baseline={want[k]:>6}  measured=  gone  DROPPED METRIC")
    if same_identity and (worse or better):
        lines.append("VERDICT=fail  the baseline claims a state its OWN artifact does not "
                     "support (same artifact, semantics and script digests, different "
                     "numbers): refused as hand-edited or stale")
        return EXIT_FAIL, lines
    if worse:
        lines.append(f"VERDICT=fail  REGRESSION in {len(worse)} metric(s): {', '.join(worse)}")
        return EXIT_FAIL, lines
    if better:
        lines.append(f"VERDICT=pass  improved in {len(better)} metric(s); lock it in with "
                     f"--rebase --reason TEXT")
        return EXIT_PASS, lines
    lines.append("VERDICT=pass  at baseline")
    return EXIT_PASS, lines


def _history_entry(action, reason, report):
    return {"action": action, "reason": reason, "metrics": dict(sorted(report["metrics"].items())),
            "identity": report["identity"]}


def run(args):
    if args.pinned_inputs:
        from pathlib import Path  # noqa: PLC0415
        print("\n".join(tir_symbols.first_party_imports(Path(__file__))))
        return EXIT_PASS
    if args.self_test:
        return self_test()
    if not args.artifact_dir:
        raise Refusal("--artifact-dir is required")
    modes = sum(bool(x) for x in (args.rebase, args.init, args.reseat))
    if modes > 1:
        raise Refusal("--init, --rebase and --reseat are exclusive")
    if modes and not (args.reason or "").strip():
        raise Refusal("--init/--rebase/--reseat need a non-empty --reason")
    texts = read_semantics_texts(args.repo_root)
    report = measure(args.artifact_dir, texts)
    baseline_path = os.path.join(args.repo_root, args.baseline) \
        if not os.path.isabs(args.baseline) else args.baseline
    if args.report:
        rp = args.report if os.path.isabs(args.report) else os.path.join(args.repo_root, args.report)
        os.makedirs(os.path.dirname(rp) or ".", exist_ok=True)
        with open(rp, "w") as fh:
            json.dump(report, fh, indent=2)
            fh.write("\n")
    for t in TARGETS:
        print(f"TARGET {t:16s} returns={report['targets'][t]['returns']}")
    pend = report.get("pending_pin_images")
    if pend:
        print("PENDING_PIN (informational, NOT gated) images=" + ",".join(sorted(pend["images"]))
              + " non_returning=" + json.dumps(pend["non_returning"], sort_keys=True))
    if args.init:
        if os.path.exists(baseline_path):
            raise Refusal(f"{baseline_path} exists; --init creates, it never overwrites")
        write_baseline(baseline_path, report["metrics"], report["identity"],
                       [_history_entry("init", args.reason, report)])
        print(f"BASELINE=written {baseline_path}")
        return EXIT_PASS
    base = load_baseline(baseline_path)
    code, lines = compare(base, report, allow_set_change=bool(args.reseat))
    print("\n".join(lines))
    if args.rebase:
        got, want = report["metrics"], base["metrics"]
        worse = [k for k in got if got[k] > want[k]]
        better = [k for k in got if got[k] < want[k]]
        if code != EXIT_PASS or worse:
            print("REBASE=refused  a baseline is lowered only when no metric is worse")
            return EXIT_FAIL
        if not better and base["identity"] == report["identity"]:
            print("REBASE=refused  nothing improved and nothing moved: already at baseline")
            return EXIT_FAIL
        bi, ri = base["identity"], report["identity"]
        if (bi["manifest_sha256"], bi["text_sha256"]) == (ri["manifest_sha256"],
                                                          ri["text_sha256"]):
            print("REBASE=refused  the artifact did not change: a lower count on the SAME "
                  "artifact comes from the instrument (script or EvalIR semantics), and an "
                  "instrument change moves a baseline only through --reseat --reason TEXT")
            return EXIT_FAIL
        write_baseline(baseline_path, got, report["identity"],
                       base["history"] + [_history_entry("rebase", args.reason, report)])
        print(f"REBASE=written {baseline_path}")
        return EXIT_PASS
    if args.reseat:
        bi, ri = base["identity"], report["identity"]
        if (bi["manifest_sha256"], bi["text_sha256"]) != (ri["manifest_sha256"], ri["text_sha256"]):
            print("RESEAT=refused  the artifact changed; a reseat re-measures the SAME artifact "
                  "after an instrument change (script or EvalIR semantics) and nothing else")
            return EXIT_FAIL
        if (bi["semantics_digest"], bi["script_sha256"]) == (ri["semantics_digest"],
                                                             ri["script_sha256"]):
            print("RESEAT=refused  the instrument did not change")
            return EXIT_FAIL
        write_baseline(baseline_path, report["metrics"], ri,
                       base["history"] + [_history_entry("reseat", args.reason, report)])
        print(f"RESEAT=written {baseline_path}")
        return EXIT_PASS
    return code


def read_semantics_texts(repo_root):
    texts = {}
    for key, rel in SEMANTICS_SOURCES.items():
        p = os.path.join(repo_root, rel)
        if not os.path.isfile(p):
            raise Refusal(f"missing semantics source {rel}")
        texts[key] = open(p, encoding="utf-8").read()
    return texts


# ---------------------------------------------------------------------------
# Self-test: synthetic artifacts, the REAL in-tree EvalIR semantics sources.
# ---------------------------------------------------------------------------
P = TARGET_PREFIX + "infer::<impl " + CRATE + "::tc::TypeChecker<'_>>::"
SYN_FUNCS = [
    # 0 infer_type: calls tick_heartbeat and infer_type_fast; returns iff both do.
    (P + "infer_type::<__trust_args@0>", """bb0(%0: ptr):
    %1 = call @func.2(%0)
    %2 = call @func.1(%0)
    ret %2"""),
    # 1 infer_type_fast: a returning path through a helper, and an arm holding `borrow_mut`
    # (imaged since crystal D1: it shares `borrow`'s arm) and `end_borrow` (no image).
    (P + "infer_type_fast::<__trust_args@0>", """bb0(%0: ptr):
    %1 = const bool true
    condbr %1, bb1, bb2
bb1:
    %2 = call @func.3(%0)
    ret %2
bb2:
    %3 = borrow_mut %0  ; #proof: exclusive_borrow
    end_borrow %3
    %4 = undef struct.4  ; #proof: fresh_symbolic_havoc
    %5 = insertfield struct.4 %4, 0, %3
    %6 = undef (u32, bool)  ; #proof: fresh_symbolic_havoc
    %7 = insertfield (u32, bool) %6, 0, %5
    ret %7"""),
    # 2 tick_heartbeat: the only ret is behind an insertfield on an undef.
    (TARGET_PREFIX + "heartbeat::<impl " + CRATE + "::tc::TypeChecker<'_>>::"
     "tick_heartbeat::<__trust_args@0>", """bb0(%0: ptr):
    %1 = undef struct.1  ; #proof: fresh_symbolic_havoc
    %2 = const i64 0
    %3 = insertfield struct.1 %1, 0, %2
    ret %3"""),
    # 3 helper: returns; carries a tuple-typed aggregate idiom and a value havoc.
    ("helper::ok::<__trust_args@0>", """bb0(%0: ptr):
    %1 = undef (u32, bool)  ; #proof: fresh_symbolic_havoc
    %2 = const u32 7
    %3 = alloca (u32, bool)
    store (u32, bool) %1, ptr %3
    %4 = undef u64  ; #proof: fresh_symbolic_havoc
    %5 = copy ptr %0
    ret %5"""),
    # 4,5 mutual recursion with no base case: GFP says they return, LFP does not.
    ("helper::rec_a::<__trust_args@0>", """bb0(%0: ptr):
    %1 = call @func.5(%0)
    ret %1"""),
    ("helper::rec_b::<__trust_args@0>", """bb0(%0: ptr):
    %1 = call @func.4(%0)
    ret %1"""),
    # 6 an assert of a const false (through a copy) before the only ret.
    ("helper::panics::<__trust_args@0>", """bb0:
    %0 = const bool false
    %1 = copy bool %0
    assert %1  ; #proof: no_panic
    ret"""),
    # 7 a pointer-to-integer bitcast (unmodelled: crystal D12 images only `ptr -> ptr`), and an
    # undef feeding a condbr.
    ("helper::bitcast::<__trust_args@0>", """bb0(%0: ptr):
    %1 = bitcast ptr %0 to u64
    ret %1"""),
    ("helper::havoc_branch::<__trust_args@0>", """bb0:
    %0 = undef bool  ; #proof: fresh_symbolic_havoc
    condbr %0, bb1, bb1
bb1:
    ret"""),
    # 9 a tuple-typed insertfield on an undef base: the review's regex misses it.
    ("helper::tuple_if::<__trust_args@0>", """bb0:
    %0 = undef (u32, bool)  ; #proof: fresh_symbolic_havoc
    %1 = const u32 1
    %2 = insertfield (u32, bool) %0, 0, %1
    ret %2"""),
    # 10 an undef reaches a condbr only THROUGH extractfield (propagation).
    ("helper::propagated::<__trust_args@0>", """bb0:
    %0 = undef struct.2  ; #proof: fresh_symbolic_havoc
    %1 = extractfield bool %0, 0
    condbr %1, bb1, bb1
bb1:
    ret"""),
    # 11 a call_indirect through a parameter: an unknown callee.
    ("helper::indirect::<__trust_args@0>", """bb0(%0: ptr):
    %1 = call_indirect %0(functy.0)(%0) cc=rustcc
    ret %1"""),
    # 12 a Bool `bor`: a BinOp with no IRBinOp image in the projector.
    ("helper::bool_or::<__trust_args@0>", """bb0(%0: bool, %1: bool):
    %2 = bor bool %0, %1
    ret %2"""),
    # 13 a load through a havoc pointer.
    ("helper::havoc_load::<__trust_args@0>", """bb0:
    %0 = undef ptr  ; #proof: fresh_symbolic_havoc
    %1 = load u32, ptr %0
    ret %1"""),
    # 14 an instruction kind with no IRInst image on the only path.
    ("helper::end_borrow::<__trust_args@0>", """bb0(%0: ptr):
    end_borrow %0
    ret %0"""),
    # 15, 16 a cast and a binop EvalIR never models.
    ("helper::inttoptr::<__trust_args@0>", """bb0(%0: u64):
    %1 = inttoptr u64 %0 to ptr
    ret %1"""),
    ("helper::frem::<__trust_args@0>", """bb0(%0: f64, %1: f64):
    %2 = frem f64 %0, %1
    ret %2"""),
    # 17 a gep whose INDEX is a havoc (the Lever-A offset shape); its base is a real pointer.
    ("helper::havoc_gep_index::<__trust_args@0>", """bb0(%0: ptr):
    %1 = undef u64  ; #proof: fresh_symbolic_havoc
    %2 = gep inbounds u8, ptr %0, %1
    ret %2"""),
]
SYN_EDGES = {0: [2, 1], 1: [3], 4: [5], 5: [4]}


def synth_artifact(root, funcs=None, edges=None, mutate_text=None, mutate_manifest=None):
    funcs = SYN_FUNCS if funcs is None else funcs
    edges = SYN_EDGES if edges is None else edges
    lines = [TEXT_HEADER, 'module "clean_kernel::callees"', "type ty.0 = u8",
             "global internal @g0 [ty.0 x 1] = array[ 0 ]", "global @g1 ptr",
             "global internal @g2 [ty.0 x 2]", "global internal mut @g3 [ty.0 x 1] = array[ 0 ]",
             "global internal @g4 [ty.0 x 1] = array[ -1 ]",
             "global internal @g5 [ty.9 x 1] = array[ 0 ]", "global internal @g6 u8 = 0",
             # Crystal plan step 18 (`const-images`): a struct global whose aggregate holds the
             # ADDRESS of a function of this module (by exact name, addend 0) is imaged (g7);
             # one naming no function (g8), carrying an addend (g9), or with an array
             # initializer at a struct type (g10) is not; g11 is a tuple-typed image.
             "global internal @g7 struct.1 = { symaddr<helper::ok::<__trust_args@0>>, 7 }",
             "global internal @g8 struct.1 = { symaddr<helper::nosuch>, 7 }",
             "global internal @g9 struct.1 = { symaddr<helper::ok::<__trust_args@0> + 8>, 7 }",
             "global internal @g10 struct.1 = array[ 0 ]",
             "global internal @g11 (u8, ptr) = { 1, symaddr<helper::frem::<__trust_args@0>> }",
             "functy.0 = (ptr) -> (ptr)"]
    for name, body in funcs:
        lines.append(f"fn @{name}(functy.0) {{")
        lines.append("    ; #producer: trust-ir")
        lines.extend(body.split("\n"))
        lines.append("}")
    lines.append('obligation 0 panic_freedom pending "synthetic"')
    text = "\n".join(lines) + "\n"
    if mutate_text:
        text = mutate_text(text)
    members = []
    for k, (name, _) in enumerate(funcs):
        calls = [{"site": funcs[c][0], "resolved": funcs[c][0], "class": "member"}
                 for c in edges.get(k, [])]
        members.append({"sidecar_func_id": k, "name": name, "calls": calls})
    man = {"schema": KNOWN_MANIFEST_SCHEMAS[0], "crate": CRATE, "lowering": "ok",
           "members": members, "escaping": [],
           "artifacts": {"text": f"{CRATE}.callees.trust-ir.txt",
                         "text_bytes": len(text.encode())}}
    if mutate_manifest:
        mutate_manifest(man)
    cdir = os.path.join(root, "callees")
    os.makedirs(cdir, exist_ok=True)
    with open(os.path.join(cdir, f"{CRATE}.callees.trust-ir.txt"), "w") as fh:
        fh.write(text)
    with open(os.path.join(cdir, f"{CRATE}.callees.manifest.json"), "w") as fh:
        json.dump(man, fh)
    return root


def self_test():
    texts = read_semantics_texts(REPO_ROOT)
    results = []

    def arm(name, fn):
        try:
            fn()
            results.append((name, True, ""))
        except AssertionError as exc:
            results.append((name, False, str(exc)))
        except Exception as exc:  # noqa: BLE001 - an arm must never crash the battery
            results.append((name, False, f"{type(exc).__name__}: {exc}"))

    def main_code(argv):
        try:
            return run(build_parser().parse_args(argv))
        except Refusal as exc:
            print(f"REFUSED: {exc}")
            return EXIT_REFUSED

    def quiet(argv):
        import contextlib
        import io
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            code = main_code(argv)
        return code, buf.getvalue()

    def refused(mut_text=None, mut_man=None, funcs=None, edges=None, needle=""):
        with tempfile.TemporaryDirectory() as td:
            synth_artifact(td, funcs, edges, mut_text, mut_man)
            try:
                measure(td, texts)
            except Refusal as exc:
                assert needle in str(exc), f"refused, but for {exc!s:.200}"
                return
            raise AssertionError("measured instead of refusing")

    def a_measures_exactly():
        with tempfile.TemporaryDirectory() as td:
            rep = measure(synth_artifact(td), texts)
        m = rep["metrics"]
        assert m["infer_type_fast.unprojectable_bodies"] == 1, m
        assert m["infer_type_fast.unprojectable_bodies_operator_level"] == 1, m
        assert m["infer_type_fast.unprojectable_bodies_projector"] == 1, m
        assert m["infer_type_fast.non_returning_bodies"] == 0, m
        assert m["infer_type.non_returning_bodies"] == 2, m
        assert m["tick_heartbeat.non_returning_bodies"] == 1, m
        assert m["targets.non_returning"] == 2, m
        assert rep["targets"]["infer_type_fast"]["returns"] is True
        assert rep["targets"]["tick_heartbeat"]["returns"] is False
        why = rep["targets"]["tick_heartbeat"]["why_not"]["blocked_frontier"]
        assert why and "undef_insertfield" in why[0]["reasons"][0], why
        chain = rep["targets"]["infer_type"]["why_not"]["first_blocker_chain"]
        assert [c["function"].rsplit("::", 1)[-1] for c in chain] == \
            ["infer_type", "tick_heartbeat"], chain
        assert chain[-1]["first_blocker"].startswith("undef_insertfield"), chain
        hv = rep["closures"]["infer_type_fast"]["havoc"]
        # helper::ok: %1 (tuple) is STORED -> a value use; %4 is unused. infer_type_fast's
        # bb2 builds two aggregates from undefs (one tuple-typed): the idiom, not a havoc.
        assert (hv["undef_defs"], hv["value_havoc"], hv["unused"], hv["aggregate_idiom"]) == \
            (4, 1, 1, 2), hv
        # The review's literal rule: unused counted as value, and the tuple idiom missed.
        assert hv["review_rule_value_count"] == 3 and hv["review_rule_value_count_is"] == {
            "aggregate_idiom_the_regex_missed": 1, "unused": 1, "value": 1}, hv
        assert m["infer_type_fast.value_havoc_undefs"] == 1, m

    def a_seq_atomics():
        # Crystal D10: the native atomics are imaged exactly as the projector's `fn
        # seq_atomic_image` says, derived from its source; with that function gone, nothing is.
        sem = derive_semantics(texts)
        assert sorted(sem["seq_atomic_image"]) == sorted(SEQ_VARIANTS), sem["seq_atomic_image"]
        for line in ("%5 = atomicrmw add relaxed usize ptr %3, %4",
                     "%6, %7 = cmpxchg usize ptr %0, %1, %2 seq_cst seq_cst",
                     "%8 = atomic_load acquire ptr, ptr %0",
                     "atomic_store release usize %1, ptr %0", "fence seq_cst"):
            i = parse_inst(line)
            assert unimaged(i, sem) is None and unimaged_operand(i, sem) is None, line
        for line, mnem in (("%5 = atomicrmw umax relaxed usize ptr %3, %4", "atomicrmw"),
                           ("%6, %7 = cmpxchg weak usize ptr %0, %1, %2 seq_cst relaxed", "cmpxchg")):
            assert unimaged(parse_inst(line), sem) == ("kind", mnem), line
        assert ("atomicrmw", "ptr") in UNDEF_OTHER_ROLES and \
            parse_inst("%5 = atomicrmw add relaxed usize ptr %3, %4")["roles"]["ptr"] == 3
        gone = derive_semantics(dict(texts, projector=texts["projector"].replace(
            "fn seq_atomic_image(", "fn seq_atomic_image_gone(")))
        assert gone["seq_atomic_image"] == {} and \
            unimaged(parse_inst("%5 = atomicrmw add relaxed usize ptr %3, %4"), gone) == \
            ("kind", "atomicrmw"), "without the projector's image an atomic is unimaged"
        # The fall-through hands every NON-atomic back to `fn inst`, by name; a native atomic
        # named there (so `fn inst` would refuse it) is refused, never read as imaged.
        seq_at = texts["projector"].index("fn seq_atomic_image(")
        handed = texts["projector"][:seq_at] + texts["projector"][seq_at:].replace(
            "            | Inst::MakeAggregate { .. } => return Ok(None),",
            "            | Inst::MakeAggregate { .. }\n            | Inst::Fence { .. } => return Ok(None),", 1)
        assert handed != texts["projector"], "mutation did not apply"
        try:
            derive_semantics(dict(texts, projector=handed))
            raise AssertionError("a native atomic handed back to `fn inst` was accepted")
        except Refusal as exc:
            assert "hands native atomics ['Fence'] back" in str(exc), str(exc)[:300]

    def a_lfp_not_gfp():
        with tempfile.TemporaryDirectory() as td:
            synth_artifact(td)
            mod = parse_artifact(td)
            sem = derive_semantics(texts)
            lfp = fixpoint(mod, sem, PRIMARY)
            gfp = fixpoint(mod, sem, dict(PRIMARY, fixpoint="gfp"))
        assert 4 not in lfp and 5 not in lfp, "LFP must not let a base-less recursion return"
        assert 4 in gfp and 5 in gfp, "GFP control: the same pair returns there"

    def a_rules_fire():
        with tempfile.TemporaryDirectory() as td:
            synth_artifact(td)
            mod = parse_artifact(td)
            sem = derive_semantics(texts)
            ret = fixpoint(mod, sem, PRIMARY)
            for k in range(6, 18):
                assert k not in ret, f"synthetic body {k} must not return"
            assert 3 in ret, "helper::ok must return"
            for k, fam in ((6, "assert_false"), (7, "cast_unmodelled"), (8, "undef_branch"),
                           (9, "undef_insertfield"), (11, "call_unknown"),
                           (12, "unimaged_op"), (13, "undef_other"), (14, "unimaged_kind"),
                           (15, "cast_unmodelled"), (16, "cast_unmodelled"),
                           (17, "undef_other"), (1, None)):
                if fam is None:
                    continue
                assert k in fixpoint(mod, sem, dict(PRIMARY, **{fam: False})), \
                    f"body {k} must return once the {fam} rule is off"
            assert 10 in fixpoint(mod, sem, dict(PRIMARY, propagate=False)), \
                "body 10 must return without undef propagation"
            rev = fixpoint(mod, sem, REVIEW)
            assert 9 in rev, "the review's \\S+ regex does not see a tuple insertfield"
            assert 2 not in rev, "the review rule does see struct insertfield on undef"

    def a_gate_cycle():
        with tempfile.TemporaryDirectory() as td:
            art = synth_artifact(os.path.join(td, "art"))
            bl = os.path.join(td, "baseline.json")
            base = ["--artifact-dir", art, "--repo-root", REPO_ROOT, "--baseline", bl]
            code, out = quiet(base)
            assert code == EXIT_REFUSED and "no baseline" in out, out
            code, out = quiet(base + ["--init", "--reason", ""])
            assert code == EXIT_REFUSED, "an empty reason must be refused"
            code, out = quiet(base + ["--init", "--reason", "self-test"])
            assert code == EXIT_PASS and os.path.isfile(bl), out
            code, out = quiet(base)
            assert code == EXIT_PASS and "at baseline" in out, out
            code, out = quiet(base + ["--init", "--reason", "again"])
            assert code == EXIT_REFUSED, "--init must never overwrite"
            # A baseline BETTER than its own artifact, history and digest kept consistent
            # (the most careful forger): the same-identity comparison still fails it.
            b = json.load(open(bl))
            b["metrics"]["infer_type.non_returning_bodies"] -= 1
            b["history"][-1]["metrics"]["infer_type.non_returning_bodies"] -= 1
            b["payload_sha256"] = _payload_digest(b)
            json.dump(b, open(bl, "w"))
            code, out = quiet(base)
            assert code == EXIT_FAIL and "OWN artifact" in out, out
            # A LOOSER baseline, digest recomputed but history left alone: refused.
            b2 = json.load(open(bl))
            b2["metrics"]["infer_type.non_returning_bodies"] += 5
            b2["history"][-1]["metrics"]["infer_type.non_returning_bodies"] -= 1
            b2["payload_sha256"] = _payload_digest(b2)
            json.dump(b2, open(bl + ".loose", "w"))
            code, out = quiet(["--artifact-dir", art, "--repo-root", REPO_ROOT,
                               "--baseline", bl + ".loose"])
            assert code == EXIT_REFUSED and "moved by hand" in out, out
            # The same hand edit WITHOUT re-digesting: refused as tampered.
            b["metrics"]["infer_type.non_returning_bodies"] -= 1
            json.dump(b, open(bl, "w"))
            code, out = quiet(base)
            assert code == EXIT_REFUSED and "edited by hand" in out, out

    def a_regression_and_rebase():
        with tempfile.TemporaryDirectory() as td:
            art = synth_artifact(os.path.join(td, "art"))
            bl = os.path.join(td, "baseline.json")
            base = ["--artifact-dir", art, "--repo-root", REPO_ROOT, "--baseline", bl]
            assert quiet(base + ["--init", "--reason", "t"])[0] == EXIT_PASS
            # Regression: a new artifact whose helper::ok loses its only ret path.
            worse = [list(x) for x in SYN_FUNCS]
            worse[3][1] = worse[3][1].replace("    ret %5", "    %6 = const bool false\n"
                                              "    assert %6\n    ret %5")
            art2 = synth_artifact(os.path.join(td, "art2"), [tuple(x) for x in worse])
            b2 = ["--artifact-dir", art2, "--repo-root", REPO_ROOT, "--baseline", bl]
            code, out = quiet(b2)
            assert code == EXIT_FAIL and "REGRESSION" in out, out
            code, out = quiet(b2 + ["--rebase", "--reason", "try to hide it"])
            assert code == EXIT_FAIL and "REBASE=refused" in out, out
            code, out = quiet(b2 + ["--reseat", "--reason", "try to hide it"])
            assert code == EXIT_FAIL and "RESEAT=refused" in out, out
            # Improvement: tick_heartbeat's aggregate built from a const, not an undef.
            better = [list(x) for x in SYN_FUNCS]
            better[2][1] = better[2][1].replace(
                "%1 = undef struct.1  ; #proof: fresh_symbolic_havoc", "%1 = const struct.1 { 0 }")
            art3 = synth_artifact(os.path.join(td, "art3"), [tuple(x) for x in better])
            b3 = ["--artifact-dir", art3, "--repo-root", REPO_ROOT, "--baseline", bl]
            code, out = quiet(b3)
            assert code == EXIT_PASS and "--rebase" in out, out
            code, out = quiet(b3 + ["--rebase"])
            assert code == EXIT_REFUSED, "a rebase with no reason must be refused"
            code, out = quiet(b3 + ["--rebase", "--reason", "tick_heartbeat builds typed"])
            assert code == EXIT_PASS and "REBASE=written" in out, out
            code, out = quiet(b3 + ["--rebase", "--reason", "again"])
            assert code == EXIT_FAIL, "nothing improved: a second rebase is refused"
            h = json.load(open(bl))["history"]
            assert [e["action"] for e in h] == ["init", "rebase"], h
            # And the old, worse artifact is now a regression against the lowered baseline.
            assert quiet(base)[0] == EXIT_FAIL

    def a_metric_set_moved():
        with tempfile.TemporaryDirectory() as td:
            art = synth_artifact(os.path.join(td, "art"))
            bl = os.path.join(td, "baseline.json")
            base = ["--artifact-dir", art, "--repo-root", REPO_ROOT, "--baseline", bl]
            assert quiet(base + ["--init", "--reason", "t"])[0] == EXIT_PASS
            b = json.load(open(bl))
            b["metrics"]["infer_type.phantom"] = 0
            b["history"][-1]["metrics"]["infer_type.phantom"] = 0
            b["payload_sha256"] = _payload_digest(b)
            json.dump(b, open(bl, "w"))
            code, out = quiet(base)
            assert code == EXIT_REFUSED and "metric set moved" in out, out

    def a_semantics_anchor():
        mutated = dict(texts)
        mutated["machine"] = texts["machine"].replace(
            "| IRScalar.undef_ => IRStepResult.fault (IROutcome.type_error IRFault.not_agg)",
            "| IRScalar.undef_ => IRStepResult.value IRScalar.undef_", 1)
        assert mutated["machine"] != texts["machine"], "mutation did not apply"
        try:
            derive_semantics(mutated)
        except Refusal as exc:
            assert "ir_insert_field" in str(exc), str(exc)[:300]
            return
        raise AssertionError("a changed insertfield undef_ arm was not refused")

    def a_semantics_comment_cannot_anchor():
        # Delete the real arm, and plant the exact text in a COMMENT: still refused.
        arm_txt = "| IRInst.unreachable => IRConfig.halted (IROutcome.ub IRFault.unreachable)"
        mutated = dict(texts)
        mutated["machine"] = texts["machine"].replace(arm_txt, "| IRInst.unreachable => "
                                                      "IRConfig.halted (IROutcome.stuck "
                                                      "IRFault.no_frame)", 1)
        mutated["machine"] += "\n// " + arm_txt + "\n"
        try:
            derive_semantics(mutated)
        except Refusal as exc:
            assert "unreachable" in str(exc), str(exc)[:300]
            return
        raise AssertionError("an anchor was satisfied by a comment")

    def a_census_disagrees():
        mutated = dict(texts)
        # Drop one entry wherever it sits in the list (main appended a constructor after it).
        mutated["census"] = texts["census"].replace('\n    "copy",\n', "\n", 1)
        assert mutated["census"] != texts["census"], "mutation did not apply"
        try:
            derive_semantics(mutated)
        except Refusal as exc:
            assert "census.rs" in str(exc), str(exc)[:300]
            return
        raise AssertionError("census.rs EMITTED_INSTS disagreeing with IRInst was accepted")

    def a_reseat():
        with tempfile.TemporaryDirectory() as td:
            art = synth_artifact(os.path.join(td, "art"))
            bl = os.path.join(td, "baseline.json")
            base = ["--artifact-dir", art, "--repo-root", REPO_ROOT, "--baseline", bl]
            assert quiet(base + ["--init", "--reason", "t"])[0] == EXIT_PASS

            def old_instrument(delta):
                b = json.load(open(bl))
                b["identity"]["script_sha256"] = "0" * 64
                b["history"][-1]["identity"]["script_sha256"] = "0" * 64
                for k, v in delta.items():
                    b["metrics"][k] += v
                    b["history"][-1]["metrics"][k] += v
                b["payload_sha256"] = _payload_digest(b)
                json.dump(b, open(bl, "w"))
            # An older instrument measured one body fewer on THIS artifact: reseat may
            # raise the baseline to what the current instrument measures.
            old_instrument({"infer_type.non_returning_bodies": -1})
            code, out = quiet(base)
            assert code == EXIT_FAIL and "REGRESSION" in out, out
            code, out = quiet(base + ["--reseat", "--reason", "instrument now sees one more"])
            assert code == EXIT_PASS and "RESEAT=written" in out, out
            assert quiet(base)[0] == EXIT_PASS
            # The same move with a DIFFERENT artifact is refused: a reseat never hides one.
            old_instrument({"infer_type.non_returning_bodies": -1})
            other = [list(x) for x in SYN_FUNCS]
            other[3][1] = other[3][1].replace("    ret %5", "    %6 = const bool false\n"
                                              "    assert %6\n    ret %5")
            art2 = synth_artifact(os.path.join(td, "art2"), [tuple(x) for x in other])
            code, out = quiet(["--artifact-dir", art2, "--repo-root", REPO_ROOT,
                               "--baseline", bl, "--reseat", "--reason", "hide it"])
            assert code == EXIT_FAIL and "the artifact changed" in out, out

    def a_irinst_bijection():
        mutated = dict(texts)
        mutated["syntax"] = texts["syntax"].replace("| copy : IRTy → Nat → IRInst",
                                                    "| copy : IRTy → Nat → IRInst\n"
                                                    "| borrowmut : Nat → IRInst", 1)
        assert mutated["syntax"] != texts["syntax"]
        try:
            derive_semantics(mutated)
        except Refusal as exc:
            assert "IRInst" in str(exc), str(exc)[:300]
            return
        raise AssertionError("an IRInst constructor with no census/projector arm was accepted")

    def a_borrow_mut_unimaged():
        sem = derive_semantics(texts)
        # Crystal D1: `borrow_mut` shares `borrow`'s arm, a DECLARED shared image.
        assert sem["kind_image"].get("BorrowMut") == sem["kind_image"].get("Borrow") == "borrow", \
            sem["kind_image"]
        assert "EndBorrow" not in sem["kind_image"], "end_borrow has no projector arm"
        assert "Copy" in sem["kind_image"]
        # An UNDECLARED multi-variant arm is refused: a projector that folded end_borrow into
        # the borrow arm would image it without anyone saying the semantics agree.
        # Both edits land in `fn inst`: `fn seq_atomic_image`'s fall-through ALSO names
        # `Inst::Retain` (it hands every non-atomic back to `fn inst`), and comes first.
        mutated = dict(texts)
        at = texts["projector"].index("fn inst(&mut self, i: &Inst)")
        mutated["projector"] = texts["projector"][:at] + texts["projector"][at:].replace(
            "Inst::Borrow { ptr } | Inst::BorrowMut { ptr } => format!",
            "Inst::Borrow { ptr } | Inst::BorrowMut { ptr } | Inst::Retain { ptr } => format!",
            1).replace("            | Inst::Retain { .. }\n", "", 1)
        assert mutated["projector"].count("Inst::Retain") == texts["projector"].count("Inst::Retain")
        try:
            derive_semantics(mutated)
            raise AssertionError("an undeclared shared imaging arm was accepted")
        except Refusal as exc:
            assert "SHARED_IMAGE_ARMS" in str(exc), str(exc)[:300]
        assert "BOr" not in sem["operator_image"]["BinOp"], "bor has no IRBinOp image today"
        assert "inttoptr" in sem["unmodelled_cast_ops"], sem["unmodelled_cast_ops"]

    def a_malformed():
        refused(mut_man=lambda m: m.pop("members"), needle="'members'")
        refused(mut_man=lambda m: m.pop("artifacts"), needle="'artifacts'")
        refused(mut_man=lambda m: m.pop("lowering"), needle="'lowering'")
        refused(mut_man=lambda m: m.pop("escaping"), needle="'escaping'")
        refused(mut_man=lambda m: m.update(lowering="partial"), needle="lowering")
        refused(mut_man=lambda m: m.update(schema="trust-ir-callee-sidecar-v9"), needle="schema")
        refused(mut_man=lambda m: m["artifacts"].pop("text_bytes"), needle="text_bytes")
        refused(mut_man=lambda m: m["artifacts"].update(text_bytes=m["artifacts"]["text_bytes"] + 1),
                needle="truncated")
        refused(mut_man=lambda m: m["members"][3].update(name="helper::other"), needle="manifest")
        refused(mut_man=lambda m: m["members"][1]["calls"].clear(), needle="disagree")

    def to_v3(m):
        # A well-formed v3 manifest over the same synthetic bundle (the bbs and block
        # counts are synthetic: this instrument bounds them but reads neither).
        m["schema"] = MANIFEST_SCHEMA_V3
        m["fuel"], m["fuel_exhausted"] = 64, False
        for mem in m["members"]:
            mem["mir_digest"] = "sha256:" + f"{mem['sidecar_func_id'] + 1:02x}" * 32
            mem["mir_blocks"] = len(mem["calls"]) + 1
            for j, c in enumerate(mem["calls"]):
                c["bb"] = j

    def a_manifest_v3():
        with tempfile.TemporaryDirectory() as td:
            rep2 = measure(synth_artifact(td), texts)
        with tempfile.TemporaryDirectory() as td:
            rep3 = measure(synth_artifact(td, mutate_manifest=to_v3), texts)
        assert rep3["metrics"] == rep2["metrics"], "a v3 manifest measured unlike its v2 twin"

        def v3_then(f):
            return lambda m: (to_v3(m), f(m))

        refused(mut_man=v3_then(lambda m: m["members"][1]["calls"][0].pop("bb")), needle="`bb`")
        refused(mut_man=v3_then(lambda m: m["members"][1]["calls"][0].update(bb=True)),
                needle="`bb`")
        refused(mut_man=v3_then(lambda m: m["members"][0].pop("mir_digest")), needle="`mir_digest`")
        refused(mut_man=v3_then(lambda m: m["members"][0].update(mir_digest=ZERO_MIR_DIGEST)),
                needle="`mir_digest`")
        refused(mut_man=v3_then(lambda m: m.pop("fuel")), needle="`fuel`")
        refused(mut_man=v3_then(lambda m: m.update(fuel_exhausted="no")), needle="`fuel_exhausted`")
        # The v3 keys on a manifest still LABELLED v2 are not what makes it v2: the label is
        # the key, so a v2 manifest without them reads exactly as before (a_measures_exactly).

    def a_truncated_text():
        # Sizes agree (the manifest is written after the cut): the STRUCTURE refuses it.
        refused(mut_text=lambda t: t[: t.index("    %2 = insertfield (u32, bool)")],
                needle="never closed")
        refused(mut_text=lambda t: t.replace("    ret %3\n}", "    ret %3\n", 1),
                needle="unparsed line inside a function")
        refused(mut_text=lambda t: t.replace("%2 = const i64 0", "%2 = frobnicate i64 0", 1),
                needle="unknown trust-ir mnemonic")
        refused(mut_text=lambda t: t.replace("    ret %2\nbb2:", "bb2:", 1),
                needle="no terminator")
        refused(mut_text=lambda t: t.replace("call @func.3(%0)", "call @func.99(%0)", 1),
                needle="out of range")
        refused(mut_text=lambda t: t.replace("insertfield struct.1 %1, 0, %2",
                                             "insertfield struct.1 %1 0 %2", 1),
                needle="unparsed insertfield")
        refused(mut_text=lambda t: t.replace(TEXT_HEADER, "; TrustIr text format v9", 1),
                needle="does not start")
        refused(mut_text=lambda t: t.replace("%5 = copy ptr %0", "%5 = global_addr @global.12", 1),
                needle="names no declared global")
        # An operand the printer grammar does not produce is REFUSED, never "imaged".
        refused(mut_text=lambda t: t.replace("%3 = alloca (u32, bool)", "%3 = alloca frob<3>", 1),
                needle="unparsed trust-ir type")
        refused(mut_text=lambda t: t.replace("%2 = const u32 7", "%2 = const u32 0x7", 1),
                needle="unparsed Const operands")
        refused(mut_text=lambda t: t.replace("%2 = const u32 7", "%2 = const u32 zork", 1),
                needle="unparsed trust-ir constant")
        refused(mut_text=lambda t: t.replace("global @g1 ptr", "global @g1 ptr junk", 1),
                needle="unparsed global")
        refused(mut_text=lambda t: t.replace('module "clean_kernel::callees"',
                                             'module "clean_kernel::callees"\nlocale en_US', 1),
                needle="unknown top-level form")

    def a_targets():
        bad = [list(x) for x in SYN_FUNCS]
        bad[1][0] = bad[1][0].replace("infer_type_fast", "infer_type_slow")
        refused(funcs=[tuple(x) for x in bad], needle="infer_type_fast")
        twice = list(SYN_FUNCS) + [(SYN_FUNCS[1][0].replace("@0>", "@1>"), SYN_FUNCS[1][1])]
        refused(funcs=twice, edges={**SYN_EDGES, len(SYN_FUNCS): [3]},
                needle="2 matching functions")

    def a_operand_images():
        # helper::ok (body 3, in infer_type_fast's closure) gains ONE operand before
        # its ret. Refused operands must block it and count as unprojectable at the
        # projector level only; imaged controls must change nothing.
        # Crystal memo §18: a TOP-LEVEL negative integer constant is imaged (its bit pattern);
        # one inside an aggregate is not.
        refused_ops = ("%6 = alloca closure.0", "%6 = const (i64, u8) { -1, 0 }",
                       "%6 = const struct.1 { 0, { -3 } }", "%6 = undef fatptr<slice ty.0>",
                       "%6 = ptr_data fatptr<slice ty.2> %0", "%6 = undef [ty.0 x 4]",
                       "%6 = undef &mut closure.1", "%6 = undef char",
                       "%6 = global_addr @global.1",
                       "%6 = global_addr @global.2", "%6 = global_addr @global.3",
                       "%6 = global_addr @global.4", "%6 = global_addr @global.5",
                       "%6 = global_addr @global.6", "%6 = global_addr @global.8",
                       "%6 = global_addr @global.9", "%6 = global_addr @global.10")
        imaged_ops = ("%6 = undef (closure.0, u8)", "%6 = undef &mut struct.3",
                      "%6 = const () phantomdata", "%6 = const f64 -1.5",
                      "%6 = undef fatptr<str>", "%6 = global_addr @global.0",
                      # crystal E5: the three kinds the M0 producer spells beside `str`.
                      "%6 = ptr_data fatptr<dyn.2> %0", "%6 = undef fatptr<container_len>",
                      "%6 = undef fatptr<container_vtable>",
                      # crystal plan step 18: a function TYPE, a `fndef` constant, and the
                      # struct/tuple globals whose aggregates carry function addresses.
                      "%6 = copy functy.0 %0", "%6 = const functy.0 fndef<func.3>",
                      "%6 = global_addr @global.7", "%6 = global_addr @global.11",
                      "%6 = const u128 340282366920938463463374607431768211455",
                      "%6 = undef *const Rc<(u8, char)>", "%6 = undef usize",
                      "%6 = const i64 -1", "%6 = const isize -2", "%6 = const u8 -1")
        for op, refused_ in [(o, True) for o in refused_ops] + [(o, False) for o in imaged_ops]:
            funcs = [list(x) for x in SYN_FUNCS]
            funcs[3][1] = funcs[3][1].replace("    ret %5", f"    {op}\n    ret %5")
            with tempfile.TemporaryDirectory() as td:
                synth_artifact(td, [tuple(x) for x in funcs])
                rep = measure(td, texts)
                mod = parse_artifact(td)
                sem = derive_semantics(texts)
                on = fixpoint(mod, sem, PRIMARY)
                off = fixpoint(mod, sem, dict(PRIMARY, unimaged_operand=False))
            m = rep["metrics"]
            assert m["infer_type_fast.unprojectable_bodies"] == 1, (op, m)
            assert m["infer_type_fast.unprojectable_bodies_projector"] == (2 if refused_ else 1), \
                (op, m)
            assert (3 not in on) == refused_ and 3 in off, (op, sorted(on), sorted(off))
        # Off the ret path, a refused operand leaves the per-block (gated) model
        # returning, and the whole-body (informational) rung refuses the body.
        funcs = [list(x) for x in SYN_FUNCS]
        funcs[3][1] = ("bb0(%0: ptr):\n    %1 = const bool true\n    condbr %1, bb1, bb2\n"
                       "bb1:\n    ret %0\nbb2:\n    %2 = alloca closure.0\n    ret %0")
        with tempfile.TemporaryDirectory() as td:
            rep = measure(synth_artifact(td, [tuple(x) for x in funcs]), texts)
        lad = rep["reconciliation_ladder"]
        assert lad[len(LADDER) - 1]["non_returning"]["infer_type_fast"] == 0, lad[-2]
        assert lad[-1]["non_returning"]["infer_type_fast"] == 2, lad[-1]
        assert rep["metrics"]["infer_type_fast.unprojectable_bodies_projector"] == 2, rep["metrics"]

    def a_operand_derived():
        sem = derive_semantics(texts)
        img = sem["operand_image"]
        assert "Closure" not in img["ty_variants"] and img["fat_kinds"] == \
            ["ContainerLen", "ContainerVtable", "Str", "TraitObject"], img
        assert img["int_refuses_negative"] is True, img
        # DERIVED, not typed: a projector that grows a closure arm images closures,
        # and one that drops the negative-Int refusal images negative constants.
        grown = dict(texts)
        grown["projector"] = texts["projector"].replace(
            "            Ty::Tuple(es) => format!(\"(tuple {})\", es.len()),",
            "            Ty::Tuple(es) => format!(\"(tuple {})\", es.len()),\n"
            "            Ty::Closure(id) => format!(\"(closure {})\", id.0),", 1)
        grown["projector"] = grown["projector"].replace(
            "                if *v < 0 {", "                if *v < i128::MIN {", 1)
        assert grown["projector"].count("Ty::Closure(id)") == 1, "mutation did not apply"
        g = derive_semantics(grown)["operand_image"]
        assert "Closure" in g["ty_variants"] and g["int_refuses_negative"] is False, g
        # A projector arm that starts imaging a field the text model does not read.
        typed = dict(texts)
        typed["projector"] = texts["projector"].replace(
            'format!("(assert {})", cond.0)',
            'format!("(assert {} {})", cond.0, self.ty(cond)?)', 1)
        assert typed["projector"] != texts["projector"], "mutation did not apply"
        try:
            derive_semantics(typed)
            raise AssertionError("a newly typed projector field was accepted")
        except Refusal as exc:
            assert "Inst::Assert" in str(exc), str(exc)[:300]
        # The global model's anchors: dropping the `mut` refusal REFUSES.
        loose = dict(texts)
        loose["projector"] = texts["projector"].replace("if g.mutable {", "if false {", 1)
        assert loose["projector"] != texts["projector"], "mutation did not apply"
        try:
            derive_semantics(loose)
            raise AssertionError("a moved projector global rule was accepted")
        except Refusal as exc:
            assert "global rules moved" in str(exc), str(exc)[:300]

    def a_uninit_lane_parse_and_placement():
        # Crystal E3b: `uninit` reads as a Constant::Uninit node, and stands ONLY as a direct
        # struct/tuple lane; anywhere else the artifact is malformed (a REFUSAL).
        node, j = parse_const_text("{ 0, uninit }")
        assert node == ("Aggregate", None, [("Int", 0, []), ("Uninit", None, [])]), node
        tys, cst = operand_nodes("Const", "struct.1 { 0, uninit }")
        assert cst[2][1][0] == "Uninit", cst
        operand_nodes("Const", "(u32, bool) { uninit, true }")
        for bad in ("u64 uninit", "struct.1 uninit", "enum.1 { 0, uninit }",
                    "(struct.1, u8) { { 0, uninit }, 1 }", "[ty.0 x 2] array[ uninit, 0 ]"):
            try:
                operand_nodes("Const", bad)
                raise AssertionError(f"accepted a misplaced uninit: {bad}")
            except Refusal as exc:
                assert "uninit" in str(exc), str(exc)[:200]
        try:
            parse_global("global internal @g struct.1 = { 0, uninit }")
            raise AssertionError("accepted an uninit in a global initializer")
        except Refusal as exc:
            assert "global initializer" in str(exc), str(exc)[:200]

    def a_uninit_lane_is_pending_not_gated():
        # Crystal E3b: tick_heartbeat's only ret is behind an insertfield on an undef seed. Spelled
        # the uninit-lanes way the seed is a CONSTANT, so the undef_insertfield family no longer
        # fires; reader A (pinned trust-ir, no Constant::Uninit) has no image for it, so the GATED
        # model still blocks the body (unimaged_operand), and only the informational pending-pin
        # figure -- reader B's `(undef)` image -- lets it return.
        funcs = [list(x) for x in SYN_FUNCS]
        funcs[2][1] = funcs[2][1].replace(
            "%1 = undef struct.1  ; #proof: fresh_symbolic_havoc", "%1 = const struct.1 { uninit }")
        assert "uninit" in funcs[2][1], "self-test: tick_heartbeat moved"
        with tempfile.TemporaryDirectory() as td:
            rep = measure(synth_artifact(td, [tuple(x) for x in funcs]), texts)
            base = measure(synth_artifact(os.path.join(td, "b")), texts)
        m = rep["metrics"]
        assert m["tick_heartbeat.non_returning_bodies"] == 1, m
        assert rep["targets"]["tick_heartbeat"]["returns"] is False
        why = rep["targets"]["tick_heartbeat"]["why_not"]["blocked_frontier"][0]["reasons"]
        # `_node_name` names the constant's TOP node (as for a negative Int inside an aggregate).
        assert any(r.startswith("unimaged_operand: const Aggregate") for r in why), why
        assert base["pending_pin_images"] is not None
        pend = rep["pending_pin_images"]
        assert pend["gated"] is False and pend["images"]["Uninit"]["clean"] == "IRConst.undef_", pend
        assert pend["non_returning"]["tick_heartbeat"] == 0, pend
        assert pend["targets_returning"]["tick_heartbeat"] is True, pend
        assert pend["bodies_carrying_uninit_lanes"]["tick_heartbeat"] == 1, pend
        assert base["pending_pin_images"]["non_returning"] == {
            t: base["metrics"][f"{t}.non_returning_bodies"] for t in TARGETS}, \
            "with no uninit lane the pending figure IS the gated one"

    def a_pending_image_is_derived():
        # The pending image is DERIVED from reader B's lane arm and the core shape table: a
        # reader B without the arm pends nothing; a reader B imaging `uninit` as a core constant
        # the shape table does not declare is REFUSED; one whose core constant is not undef_'s
        # is REFUSED; and once reader A carries its own arm nothing is pending.
        sem = derive_semantics(texts)
        assert sem["pending_const_images"] == {
            "Uninit": {"reader_b_core": "(undef)", "clean": "IRConst.undef_"}}, sem
        gone = dict(texts)
        gone["reader_b"] = texts["reader_b"].replace('if e == "uninit" {', 'if e == "UNINIT" {', 1)
        assert gone["reader_b"] != texts["reader_b"], "mutation did not apply"
        assert derive_semantics(gone)["pending_const_images"] == {}
        odd = dict(texts)
        odd["reader_b"] = texts["reader_b"].replace(
            'elems.push(Sx::tag("undef", vec![]));', 'elems.push(Sx::tag("nothing", vec![]));', 1)
        assert odd["reader_b"] != texts["reader_b"], "mutation did not apply"
        try:
            derive_semantics(odd)
            raise AssertionError("an undeclared core image was accepted")
        except Refusal as exc:
            assert "shape table" in str(exc), str(exc)[:300]
        wrong = dict(texts)
        wrong["reader_b"] = texts["reader_b"].replace(
            'elems.push(Sx::tag("undef", vec![]));', 'elems.push(Sx::tag("null", vec![]));', 1)
        try:
            derive_semantics(wrong)
            raise AssertionError("a lane imaged as another constant was accepted")
        except Refusal as exc:
            assert "IRConst.undef_" in str(exc), str(exc)[:300]
        grown = dict(texts)
        grown["projector"] = texts["projector"].replace(
            '            Constant::PhantomData => String::from("(phantomdata)"),',
            '            Constant::PhantomData => String::from("(phantomdata)"),\n'
            '            Constant::Uninit => String::from("(undef)"),', 1)
        assert grown["projector"] != texts["projector"], "mutation did not apply"
        g = derive_semantics(grown)
        assert "Uninit" in g["operand_image"]["const_variants"], g["operand_image"]
        assert g["pending_const_images"] == {}, "reader A imaging it leaves nothing pending"

    def a_instrument_moves_need_reseat():
        with tempfile.TemporaryDirectory() as td:
            art = synth_artifact(os.path.join(td, "art"))
            bl = os.path.join(td, "baseline.json")
            base = ["--artifact-dir", art, "--repo-root", REPO_ROOT, "--baseline", bl]
            assert quiet(base + ["--init", "--reason", "t"])[0] == EXIT_PASS

            def old_instrument(delta, drop=()):
                b = json.load(open(bl))
                for e in (b, b["history"][-1]):
                    e["identity"]["script_sha256"] = "0" * 64
                    for k, v in delta.items():
                        e["metrics"][k] += v
                    for k in drop:
                        e["metrics"].pop(k)
                b["payload_sha256"] = _payload_digest(b)
                json.dump(b, open(bl, "w"))
            # An older instrument counted MORE on this same artifact: the lower count
            # is the instrument's, so --rebase must not launder it; --reseat records it.
            old_instrument({"infer_type.non_returning_bodies": 3})
            code, out = quiet(base)
            assert code == EXIT_PASS and "better" in out, out
            code, out = quiet(base + ["--rebase", "--reason", "fewer, by a script edit"])
            assert code == EXIT_FAIL and "artifact did not change" in out, out
            code, out = quiet(base + ["--reseat", "--reason", "instrument recount"])
            assert code == EXIT_PASS and "RESEAT=written" in out, out
            # A new metric (an instrument change on the same artifact) enters by reseat
            # only; the plain gate refuses the moved set.
            old_instrument({}, drop=("infer_type.unprojectable_bodies_projector",))
            code, out = quiet(base)
            assert code == EXIT_REFUSED and "metric set moved" in out, out
            code, out = quiet(base + ["--reseat", "--reason", "projector-level metric"])
            assert code == EXIT_PASS and "NEW METRIC" in out and "RESEAT=written" in out, out
            assert quiet(base)[0] == EXIT_PASS
            h = [e["action"] for e in json.load(open(bl))["history"]]
            assert h == ["init", "reseat", "reseat"], h

    DECL = "alloc::alloc::{extern#0}::__rust_alloc"
    DECL_FN = f"fn @{DECL}(functy.0) {{\n}}\n"
    OBL0 = 'obligation 0 panic_freedom pending "synthetic"'

    def with_helper_body(tail):
        """SYN_FUNCS with helper::ok (func 3) ending in `tail` instead of its copy+ret."""
        name, body = SYN_FUNCS[3]
        assert body.endswith("    %5 = copy ptr %0\n    ret %5"), "self-test: helper::ok moved"
        return SYN_FUNCS[:3] + [(name, body[: -len("    ret %5")] + tail)] + SYN_FUNCS[4:]

    def add_decl(text, fn=DECL_FN):
        assert text.count(OBL0) == 1
        return text.replace(OBL0, fn + OBL0)

    def foreign_row(man, k=3, name=DECL):
        man["members"][k]["calls"].append({"site": name, "resolved": name,
                                           "class": f"foreign-terminal: {name}"})

    def a_declarations():
        called = with_helper_body(f"    %6 = call @func.{len(SYN_FUNCS)}(%0)\n    ret %5")
        havoc = with_helper_body("    %6 = const bool false\n    assert %6  ; #proof: no_panic\n    ret %5")
        with tempfile.TemporaryDirectory() as td:
            rep = measure(synth_artifact(os.path.join(td, "d"), called, None, add_decl, foreign_row), texts)
            old = measure(synth_artifact(os.path.join(td, "h"), havoc, None, None, foreign_row), texts)
            base = measure(synth_artifact(os.path.join(td, "b")), texts)
        m, mo = rep["metrics"], old["metrics"]
        assert rep["artifact"]["declarations"] == 1 and base["artifact"]["declarations"] == 0, rep["artifact"]
        # The declaration is not a body: every closure keeps its size; the call is counted apart.
        for t in TARGETS:
            assert rep["closures"][t]["closure_bodies"] == base["closures"][t]["closure_bodies"], t
        assert rep["closures"]["infer_type_fast"]["calls_to_declarations"] == 1, rep["closures"]
        # A declared call BLOCKS: helper::ok (and so infer_type_fast) no longer returns...
        assert m["infer_type_fast.non_returning_bodies"] == 2, m
        assert rep["targets"]["infer_type_fast"]["returns"] is False
        chain = rep["targets"]["infer_type_fast"]["why_not"]["first_blocker_chain"]
        assert "bodiless declaration" in chain[-1]["first_blocker"], chain
        # ...EXACTLY as the halting `assert false` it replaces did: every gated metric agrees.
        assert m == mo, {k: (m[k], mo[k]) for k in m if m[k] != mo[k]}

    def a_declaration_tables_refused():
        called = with_helper_body(f"    %6 = call @func.{len(SYN_FUNCS)}(%0)\n    ret %5")
        cases = (
            ("not foreign", lambda t: add_decl(t, "fn @ext::not_foreign(functy.0) {\n}\n"),
             lambda m_: foreign_row(m_, name="ext::not_foreign"), called, "not an {extern#N} foreign"),
            ("declared twice", lambda t: add_decl(t, DECL_FN + DECL_FN), foreign_row, called, "declared twice"),
            ("body past the members", lambda t: add_decl(t, f"fn @{DECL}(functy.0) {{\nbb0:\n    ret\n}}\n"),
             foreign_row, called, "has a body"),
            ("never called", add_decl, None, None, "no member calls"),
            ("called but not a row of the caller", add_decl, None, called, "no non-member call row"),
            ("bodiless member", lambda t: t.replace("fn @helper::ok::<__trust_args@0>(functy.0) {\n    ; #producer: "
                                                    "trust-ir\n" + SYN_FUNCS[3][1] + "\n}",
                                                    "fn @helper::ok::<__trust_args@0>(functy.0) {\n}"),
             None, None, "is a MEMBER and has no blocks"),
        )
        for label, mt, mm, fs, needle in cases:
            try:
                refused(mt, mm, fs, None, needle)
            except AssertionError as exc:
                raise AssertionError(f"{label}: {exc}") from exc

    def a_symaddr_by_name():
        # Crystal plan step 18: the printer spells `symaddr<{symbol}>` RAW and an instance name
        # can carry an unbalanced `>` (`fn(u8) -> ptr`). Read against the module's function
        # names, the symbol is exactly that name; without them bracket matching cannot delimit
        # it, and the global is not imaged (no detail), never imaged under a wrong name.
        name = "f::<fn(u8) -> ptr>"
        line = f"global internal @g struct.1 = {{ symaddr<{name}>, 7 }}"
        g = parse_global(line, frozenset({name, "f::<fn(u8)"}))
        assert g["init"][2][0] == ("SymbolAddr", name, []), g
        img = {"ty_variants": ["Struct", "I64"], "ty_recursive": [], "ty_needs_width": [],
               "fat_kinds": [], "const_variants": ["Int"], "const_recursive": [],
               "int_refuses_negative": True}
        assert global_imaged(g, {}, img, frozenset({name})) is None
        assert global_imaged(g, {}, img, frozenset()) is not None
        try:
            bare = parse_global(line)
        except Refusal:
            return
        assert bare["init"][2][0][1] is None, bare

    def a_by_value_and_tls():
        # Crystal D1: a markerless call_indirect with an exact, complete, all-member dispatch set
        # whose targets are declared at the call's functy returns when SOME target returns; each
        # missing piece of that evidence leaves it `call_unknown`.
        ind = "helper::indirect::<__trust_args@0>"
        ok_ = "helper::ok::<__trust_args@0>"
        lanes_on = "ON: indirect-by-value: x; tls-cells: y"

        def row(targets, complete=True, members=True):
            return (f"{ind}: indirect call (non-const func operand of type fn()); enumerated targets "
                    f"{len(targets)} [{', '.join(targets)}]"
                    + (f" {INDIRECT_ALL_MEMBERS}" if members else " (some enumerated target is not a member)")
                    + (f" {INDIRECT_SCAN_COMPLETE} the set is complete only under the address-taken "
                       f"hypothesis)" if complete else " (crate-wide address-taken scan INCOMPLETE for "
                       "this type: 1 site(s) outside it; a lower bound)"))

        def man(lanes=lanes_on, rows=None, tls=None):
            def mut(m_):
                m_["producer"] = {"value_lanes": lanes}
                m_["escaping"] = list(rows if rows is not None else [row([ok_])])
                if tls is not None:
                    m_["tls_cells"] = tls
            return mut

        def run(mm, mt=None, funcs=None):
            with tempfile.TemporaryDirectory() as td:
                synth_artifact(td, funcs, None, mt, mm)
                mod = parse_artifact(td)
                sem = derive_semantics(texts)
                return mod, sem, fixpoint(mod, sem, PRIMARY)
        mod, sem, ret = run(man())
        assert mod["by_value_sites"] == [(11, "bb0", [3])], mod["by_value_sites"]
        assert 11 in ret, "a credited by-value call returns when its target does"
        assert 3 in closure(mod["funcs"], 11), "the closure follows a by-value target"
        controls = (
            ("no lane", man(lanes="ON: fn-values: x"), None),
            ("incomplete scan", man(rows=[row([ok_], complete=False)]), None),
            ("not all members", man(rows=[row([ok_], members=False)]), None),
            ("tiles no member", man(rows=[row(["helper::nosuch"])]), None),
            ("two rows, two sets", man(rows=[row([ok_]), row(["helper::panics::<__trust_args@0>"])]), None),
            ("a marker in the block", man(), lambda t: t.replace(
                "    %1 = call_indirect %0(functy.0)(%0) cc=rustcc",
                "    %9 = const bool false\n    assert %9\n    %1 = call_indirect %0(functy.0)(%0) cc=rustcc")),
            ("a target at another functy", man(), lambda t: t.replace(
                f"fn @{ok_}(functy.0)", f"fn @{ok_}(functy.1)").replace(
                "functy.0 = (ptr) -> (ptr)", "functy.0 = (ptr) -> (ptr)\nfuncty.1 = (ptr, ptr) -> (ptr)")),
        )
        for label, mm, mt in controls:
            m2, _s, r2 = run(mm, mt)
            assert not m2["by_value_sites"] and 11 not in r2, f"{label}: must stay call_unknown"
        # A credited call whose callee is a `copy` at a non-function type never dispatches (the
        # copy of an fnptr_ at `ptr` faults, and any value it admits is not an fnptr_); a copy at
        # the call's own functy is fine.
        def copied(ty):
            return lambda t: t.replace(
                "    %1 = call_indirect %0(functy.0)(%0) cc=rustcc",
                f"    %9 = copy {ty} %0\n    %1 = call_indirect %9(functy.0)(%0) cc=rustcc")
        m6, s6, r6 = run(man(), copied("ptr"))
        assert m6["by_value_sites"] and 11 not in r6, "a callee copied at ptr must fault"
        assert 11 in fixpoint(m6, s6, dict(PRIMARY, callee_not_fnptr=False)), \
            "and only the callee_not_fnptr rule blocks it"
        m7, _s, r7 = run(man(), copied("functy.0"))
        assert m7["by_value_sites"] and 11 in r7, "a callee copied at its functy dispatches"
        # A credited call whose only target never returns does not return either.
        m3, _s, r3 = run(man(rows=[row(["helper::panics::<__trust_args@0>"])]))
        assert m3["by_value_sites"] and 11 not in r3, "a non-returning target blocks the call"
        # Crystal D11: a certified TLS address is imaged; uncertified, uncovered, or with its image
        # function gone from the projector, it is not; rows without the lane, or forged, refuse.
        tls_body = ("helper::tls::<__trust_args@0>", """bb0(%0: ptr):
    %1 = dialect_op trust_rust.thread_local_addr() -> ptr [schema=str:"trust-rust.thread-local-addr/v1"] [symbol=str:"k::VAL"]
    ret %1""")
        funcs = list(SYN_FUNCS) + [tls_body]
        k_tls = len(funcs) - 1
        good = {"symbol": "k::VAL", "unique_symbol": True, "pointer_free": True,
                "definitely_not_sync": True, "certified": True}
        assert sem["tls_input_image"].get("ctor") == "globaladdr", sem["tls_input_image"]
        m4, s4, r4 = run(man(tls=[good]), None, funcs)
        assert k_tls in r4 and m4["tls_certified"] == frozenset({"k::VAL"}), "certified: imaged"
        for label, tls in (("no rows", None),
                           ("uncertified", [dict(good, pointer_free=False, certified=False)]),
                           ("another symbol", [dict(good, symbol="k::OTHER")])):
            _m, _s, r5 = run(man(tls=tls), None, funcs)
            assert k_tls not in r5, f"{label}: the op stays unimaged"
        stripped = dict(texts)
        stripped["projector"] = texts["projector"].replace("fn tls_input_image(", "fn tls_input_gone(", 1)
        assert derive_semantics(stripped)["tls_input_image"] == {}, "no image function, no image"
        for label, mm, needle in (("rows without the lane", man(lanes="ON: indirect-by-value: x", tls=[good]),
                                   "tls-cells"),
                                  ("forged certified", man(tls=[dict(good, definitely_not_sync=False)]),
                                   "conjunction")):
            try:
                run(mm, None, funcs)
                raise AssertionError(f"{label}: accepted")
            except Refusal as exc:
                assert needle in str(exc), (label, str(exc)[:200])

    def a_d12_ub_halts_and_thunks():
        # Crystal memo §18. D12: a `bitcast ptr -> ptr` is imaged as `copy (ptr)` -- it returns,
        # an undef operand is the copy's fault, a callee reached through it is not an fnptr_, and
        # without the projector's function it is `cast_unmodelled` again.
        sem = derive_semantics(texts)
        assert sem["ptr_bitcast_identity"].get("ctor") == "copy", sem["ptr_bitcast_identity"]
        assert set(sem["negative_int_image"].get("types", ())) >= {"I64", "Isize", "U8"}
        # The width match's fall-through is NAMED (the projector's crate forbids `_`): a width arm
        # moved into it is no longer imaged, and a match with no named fall-through -- the D1b
        # `_ => return Ok(None),` spelling included -- is refused, never read as imaging nothing.
        neg_at = texts["projector"].index("fn negative_int_const_image(")
        head, tail = texts["projector"][:neg_at], texts["projector"][neg_at:]
        moved = head + re.sub(r"\n\s*Ty::I8 \| Ty::U8 => 8,", "", tail, count=1).replace(
            "Ty::Bool\n", "Ty::I8\n            | Ty::U8\n            | Ty::Bool\n", 1)
        assert moved.count("Ty::I8 | Ty::U8 => 8,") == texts["projector"].count(
            "Ty::I8 | Ty::U8 => 8,") - 1, "mutation did not apply"
        moved_tys = set(derive_semantics(dict(texts, projector=moved))["negative_int_image"]["types"])
        assert "I8" not in moved_tys and "U8" not in moved_tys and "I64" in moved_tys, moved_tys
        wild = head + re.sub(r"Ty::Bool\n(?:\s*\| Ty::[A-Za-z0-9]+(?:\([^()]*\))?\n)*"
                             r"\s*\| Ty::Handle\(_\) => return Ok\(None\),",
                             "_ => return Ok(None),", tail, count=1)
        assert wild != texts["projector"], "mutation did not apply"
        try:
            derive_semantics(dict(texts, projector=wild))
            raise AssertionError("a width match with no named fall-through was accepted")
        except Refusal as exc:
            assert "named `=> return Ok(None)` fall-through" in str(exc), str(exc)[:300]
        assert sem["ub_halt_image"].get("ctor") == "unreachable", sem["ub_halt_image"]
        bodies = [
            ("helper::d12_ok::<__trust_args@0>", "bb0(%0: ptr):\n    %1 = bitcast ptr %0 to ptr\n    ret %1"),
            ("helper::d12_undef::<__trust_args@0>",
             "bb0:\n    %0 = undef ptr  ; #proof: fresh_symbolic_havoc\n    %1 = bitcast ptr %0 to ptr\n"
             "    ret %1"),
            ("helper::d12_callee::<__trust_args@0>",
             "bb0(%0: ptr):\n    %1 = bitcast ptr %0 to ptr\n    %2 = call_indirect %1(functy.0)(%0) cc=rustcc\n"
             "    ret %2"),
        ]
        funcs = list(SYN_FUNCS) + bodies
        k0 = len(SYN_FUNCS)

        def run(fs, mt=None, mm=None, texts_=texts):
            with tempfile.TemporaryDirectory() as td:
                synth_artifact(td, fs, None, mt, mm)
                mod = parse_artifact(td)
                sem_ = derive_semantics(texts_)
                return mod, sem_, fixpoint(mod, sem_, PRIMARY)
        _m, s1, r1 = run(funcs)
        assert k0 in r1, "a pointer bitcast imaged as copy returns"
        assert k0 + 1 not in r1 and k0 + 1 in fixpoint(_m, s1, dict(PRIMARY, undef_other=False)), \
            "an undef operand of the imaged copy is the copy's fault"
        assert k0 + 2 not in r1 and k0 + 2 in fixpoint(
            _m, s1, dict(PRIMARY, callee_not_fnptr=False, call_unknown=False)), \
            "a callee through a ptr-typed copy image is not an fnptr_"
        gone = dict(texts, projector=texts["projector"].replace(
            "fn ptr_bitcast_identity_image(", "fn ptr_bitcast_identity_gone(", 1))
        _m, s2, r2 = run(funcs, texts_=gone)
        assert s2["ptr_bitcast_identity"] == {} and k0 not in r2 and k0 in fixpoint(
            _m, s2, dict(PRIMARY, cast_unmodelled=False)), "no projector image: cast_unmodelled"
        # A UB halt (its obligation SITES the assert) is the `unreachable` family, never
        # `assert_false`; the same assert under the panic wording stays `assert_false`; a UB halt
        # with no site is REFUSED; one sited off a halting assert has no image.
        halt = ("helper::halts::<__trust_args@0>",
                "bb0:\n    %0 = const bool false\n    assert %0  ; #proof: no_panic\n    unreachable")
        fs = list(SYN_FUNCS) + [halt]
        kh = len(SYN_FUNCS)

        def obligation(desc, site):
            return lambda t: t.replace('obligation 0 panic_freedom pending "synthetic"',
                                       f'obligation 0 panic_freedom pending "synthetic"\n'
                                       f'obligation 1 panic_freedom pending "{desc}" function {kh} formula "f" "p" '
                                       f'source "s" assertion "a" range 0 0 0 0 0{site}')
        ub = f"reaching `core::hint::unreachable_unchecked` {UB_HALT_WORDING}"
        m3, s3, r3 = run(fs, obligation(ub, f" site f{kh}/bb0#1"))
        assert kh not in r3 and mod_reason(m3, s3, kh) == "unreachable", mod_reason(m3, s3, kh)
        assert kh not in fixpoint(m3, s3, dict(PRIMARY, assert_false=False)), \
            "dropping assert_false does not free a UB halt"
        m4, s4, _r4 = run(fs, obligation("panic call `core::panicking::panic` must be unreachable",
                                          f" site f{kh}/bb0#1"))
        assert mod_reason(m4, s4, kh) == "assert_false", mod_reason(m4, s4, kh)
        for label, site, needle in (("no site", "", "no site"),):
            try:
                run(fs, obligation(ub, site))
                raise AssertionError(f"{label}: accepted")
            except Refusal as exc:
                assert needle in str(exc), (label, str(exc)[:200])
        m5, s5, _r5 = run(fs, obligation(ub, f" site f{kh}/bb0#0"))
        assert mod_reason(m5, s5, kh) == "unimaged_kind", mod_reason(m5, s5, kh)
        # D13: a by-value site whose enumerated target is a SHIM at `((), (ptr)) -> (ptr)` is
        # credited through the shim's supplied ABI thunk at the call's `(ptr) -> (ptr)`; without
        # the lane named it is refused; a malformed thunk is refused; a constant naming the SHIM
        # as a value withdraws the credit.
        shim = ("helper::shim#shim:ClosureOnce", "bb0(%0: (), %1: (ptr)):\n    %2 = extractfield ptr %1, 0\n    ret %2")
        fs = list(SYN_FUNCS) + [shim]
        ks = len(SYN_FUNCS)
        ind = "helper::indirect::<__trust_args@0>"
        row = (f"{ind}: indirect call (non-const func operand of type fn(*const u8) -> *const u8); enumerated "
               f"targets 1 [{shim[0]}] {INDIRECT_ALL_MEMBERS} {INDIRECT_SCAN_COMPLETE} the set is complete "
               f"only under the address-taken hypothesis)")
        thunk = (f"fn @{shim[0]}{THUNK_SUFFIX}(functy.0) {{\n    ; #producer: {THUNK_PRODUCER_TEXT}\n"
                 f"bb0(%0: ptr):\n    %1 = const () phantomdata\n    %2 = const (ptr) {{ 0 }}\n"
                 f"    %3 = insertfield (ptr) %2, 0, %0\n    %4 = call @func.{ks}(%1, %3)\n    ret %4\n}}\n")

        def with_thunk(body=thunk, extra=""):
            def mt(t):
                t = t.replace(f"fn @{shim[0]}(functy.0)", f"fn @{shim[0]}(functy.1)").replace(
                    "functy.0 = (ptr) -> (ptr)", "functy.0 = (ptr) -> (ptr)\nfuncty.1 = ((), (ptr)) -> (ptr)")
                return t.replace('obligation 0 panic_freedom pending "synthetic"',
                                 body + extra + 'obligation 0 panic_freedom pending "synthetic"')
            return mt

        def man(lanes="ON: indirect-by-value: x; fnptr-thunks: y"):
            def mm(m_):
                m_["producer"] = {"value_lanes": lanes}
                m_["escaping"] = [row]
            return mm
        m6, _s6, r6 = run(fs, with_thunk(), man())
        kt = len(fs)
        assert m6["abi_thunks"] == 1 and m6["by_value_sites"] == [(11, "bb0", [kt])], m6["by_value_sites"]
        assert 11 in r6 and kt in r6 and ks in r6, "the site returns through the thunk and its shim"
        assert {kt, ks} <= closure(m6["funcs"], 11), "the closure follows the thunk to the shim"
        _m, _s, r7 = run(fs, lambda t: with_thunk(body="")(t), man())
        assert 11 not in r7, "no thunk: the shim's signature is not the call's, call_unknown"
        _m, _s, r8 = run(fs, with_thunk(extra="global internal @gx struct.1 = { fndef<func.%d> }\n" % ks), man())
        assert 11 not in r8, "a constant naming the SHIM as a value withdraws the thunk credit"
        for label, mt, mm, needle in (
                ("lane not named", with_thunk(), man("ON: indirect-by-value: x"), "fnptr-thunks"),
                ("wrong lane", with_thunk(body=thunk.replace("insertfield (ptr) %2, 0, %0",
                                                             "insertfield (ptr) %2, 0, %1")), man(),
                 "exact rust-call spread"),
                ("named for no shim", with_thunk(body=thunk.replace("ClosureOnce#", "ClosureTwice#")), man(),
                 "names no member shim")):
            try:
                run(fs, mt, mm)
                raise AssertionError(f"{label}: accepted")
            except Refusal as exc:
                assert needle in str(exc), (label, str(exc)[:200])

    def a_quoted_symbols():
        # C-M0: trust-ir WS4.3 prints a non-bare symbol QUOTED (`fn @"..."`, `global @"..."`). The
        # same bundle printed that way measures IDENTICALLY; a module mixing a quoted and a raw
        # symbol, and a quoted bare-able name, are REFUSED (no trust-ir printer writes either).
        vt = "__trust_vtable__core::fmt::Debug$&u64__"

        def ws43(t):
            t = re.sub(r"(?m)^(rustcc )?fn @(.*)\(functy\.(\d+)\) \{$",
                       lambda m_: f"{m_.group(1) or ''}fn @{tir_symbols.spell_symbol(m_.group(2))}"
                                  f"(functy.{m_.group(3)}) {{", t)
            return t.replace("global @g1 ptr", f"global @g1 ptr\nglobal @{tir_symbols.spell_symbol(vt)} ptr")

        def raw_vt(t):
            return t.replace("global @g1 ptr", f"global @g1 ptr\nglobal @{vt} ptr")

        with tempfile.TemporaryDirectory() as td:
            legacy = measure(synth_artifact(td, mutate_text=raw_vt), texts)
        with tempfile.TemporaryDirectory() as td:
            synth_artifact(td, mutate_text=ws43)
            qtext = open(os.path.join(td, "callees", f"{CRATE}.callees.trust-ir.txt")).read()
            quoted = measure(td, texts)
            names = {g["name"] for g in parse_artifact(td)["globals_list"]}
        assert f'fn @"{SYN_FUNCS[0][0]}"(functy.0) {{' in qtext and f'global @"{vt}" ptr' in qtext, qtext[:400]
        assert vt in names, names
        assert quoted["metrics"] == legacy["metrics"] and quoted["targets"] == legacy["targets"], \
            (quoted["metrics"], legacy["metrics"])
        refused(mut_text=lambda t: re.sub(r"(?m)^fn @(helper::ok[^(]*)\(",
                                          lambda m_: f"fn @{tir_symbols.spell_symbol(m_.group(1))}(", t,
                                          count=1),
                needle="mixes a QUOTED symbol")
        refused(mut_text=lambda t: t.replace("global @g1 ptr", 'global @"g1" ptr'),
                needle="must be spelled bare")

    def a_const_tuple_type():
        # C-M0 (the D3 arm's ABI thunk #2990, the lane's first TWO-argument thunk): a `const` whose
        # type is a tuple reads its type with the type grammar, not `^(\S+|\(.*?\))`, which read
        # `const (i32, ptr) { 0, 0 }` as type `(i32,`; the exact two-lane thunk is then accepted.
        inst = parse_inst("%3 = const (i32, ptr) { 0, 0 }")
        assert (inst["const_ty"], inst["const_value"]) == ("(i32, ptr)", "{ 0, 0 }"), inst
        assert parse_inst("%1 = const () phantomdata")["const_ty"] == "()"
        assert parse_inst("%1 = const (u8, (i32, ptr)) { 1, { 0, 0 } }")["const_ty"] == "(u8, (i32, ptr))"
        assert parse_inst("%1 = const bool false")["const_value"] == "false"
        for bad_ in ("%1 = const (i32, ptr){ 0, 0 }", "%1 = const (i32, ptr)", "%1 = const (i32, ptr "):
            try:
                parse_inst(bad_)
                raise AssertionError(f"{bad_!r}: accepted")
            except Refusal:
                pass
        shim = ("helper::shim2#shim:ClosureOnce",
                "bb0(%0: (), %1: (i32, ptr)):\n    %2 = extractfield ptr %1, 1\n    ret %2")
        fs = list(SYN_FUNCS) + [shim]
        ks = len(SYN_FUNCS)
        thunk = (f"fn @{shim[0]}{THUNK_SUFFIX}(functy.2) {{\n    ; #producer: {THUNK_PRODUCER_TEXT}\n"
                 f"bb0(%0: i32, %1: ptr):\n    %2 = const () phantomdata\n    %3 = const (i32, ptr) {{ 0, 0 }}\n"
                 f"    %4 = insertfield (i32, ptr) %3, 0, %0\n    %5 = insertfield (i32, ptr) %4, 1, %1\n"
                 f"    %6 = call @func.{ks}(%2, %5)\n    ret %6\n}}\n")

        def mt(t):
            t = t.replace(f"fn @{shim[0]}(functy.0)", f"fn @{shim[0]}(functy.1)").replace(
                "functy.0 = (ptr) -> (ptr)", "functy.0 = (ptr) -> (ptr)\nfuncty.1 = ((), (i32, ptr)) -> (ptr)"
                "\nfuncty.2 = (i32, ptr) -> (ptr)")
            return t.replace('obligation 0 panic_freedom pending "synthetic"',
                             thunk + 'obligation 0 panic_freedom pending "synthetic"')

        def mm(m_):
            m_["producer"] = {"value_lanes": "ON: fnptr-thunks: y"}
        with tempfile.TemporaryDirectory() as td:
            synth_artifact(td, fs, None, mt, mm)
            mod = parse_artifact(td)
        assert mod["abi_thunks"] == 1 and mod["funcs"][len(fs)].get("thunk_of") == ks, mod["abi_thunks"]
        refused(funcs=fs, mut_text=lambda t: mt(t).replace("insertfield (i32, ptr) %4, 1, %1",
                                                            "insertfield (i32, ptr) %4, 1, %0"),
                mut_man=mm, needle="exact rust-call spread")

    def a_d14_vtable_certify():
        # E5 (memo §23): the projector CERTIFIES D14's align read -- `ptr_metadata .. to ptr`, a
        # byte `gep` to +16 (or +8), `load usize`, and the unchanged word as a new trait object's
        # metadata -- and refuses the body at the first other use of a vtable word; the model marks
        # exactly that use, from rules DERIVED off the projector's functions.
        sem = derive_semantics(texts)
        d = sem["d14_vtable_certify"]
        assert d["seed_kinds"] == ["ContainerVtable", "TraitObject"] and d["load_slots"] == [8, 16], d

        def body(tail, off="16", load_ty="usize"):
            return ("helper::d14::<__trust_args@0>",
                    "bb0(%0: fatptr<container_vtable>):\n"
                    "    %1 = ptr_metadata fatptr<container_vtable> %0 to ptr\n"
                    "    %2 = ptr_data fatptr<container_vtable> %0\n"
                    f"    %3 = copy ptr %1\n    %4 = const i64 {off}\n    %5 = gep i8, ptr %3, %4\n"
                    f"    %6 = load {load_ty}, ptr %5\n    %7 = load u8, ptr %2\n" + tail)

        def marked(texts_, b):
            fs = list(SYN_FUNCS) + [b]
            with tempfile.TemporaryDirectory() as td:
                synth_artifact(td, fs)
                mod = parse_artifact(td)
            sem_ = derive_semantics(texts_)
            annotate_d14(mod, sem_)
            ins = mod["funcs"][len(SYN_FUNCS)]["blocks"][0]["insts"]
            return [i["mnem"] for i in ins if unimaged_operand(i, sem_)]
        rebuild = "    %8 = ptr_from_parts fatptr<dyn.3> ptr %2, ptr %1\n    ret %6"
        assert marked(texts, body(rebuild)) == [], marked(texts, body(rebuild))
        assert marked(texts, body(rebuild, off="8")) == []
        assert marked(texts, body(rebuild, off="24")) == ["load"]
        assert marked(texts, body(rebuild, load_ty="u64")) == ["load"]
        assert marked(texts, body("    store usize %6, ptr %1\n    ret %6")) == ["store"]
        assert marked(texts, body("    ret %1")) == ["ret"]
        gone = dict(texts, projector=texts["projector"].replace(
            "fn d14_vtable_certify(", "fn d14_vtable_gone(", 1))
        assert derive_semantics(gone)["d14_vtable_certify"] == {}
        assert marked(gone, body("    ret %1")) == []
        moved = dict(texts, projector=texts["projector"].replace(
            "if usize_word && (off == 8 || off == 16) {", "if usize_word && (off == 8 || off == 24) {", 1))
        assert moved != texts, "mutation did not apply"
        try:
            derive_semantics(moved)
        except Refusal as e:
            assert "d14_vtable_certify" in str(e), e
        else:
            raise AssertionError("a moved certified slot was not refused")
        widened = dict(texts, projector=texts["projector"].replace(
            "trust_ir::FatPtrKind::TraitObject { .. } | trust_ir::FatPtrKind::ContainerVtable => true",
            "trust_ir::FatPtrKind::TraitObject { .. }\n        | trust_ir::FatPtrKind::ContainerLen\n"
            "        | trust_ir::FatPtrKind::ContainerVtable => true", 1))
        assert widened != texts["projector"], "mutation did not apply"
        assert derive_semantics(widened)["d14_vtable_certify"]["seed_kinds"] == \
            ["ContainerLen", "ContainerVtable", "TraitObject"]

    def a_e5_metadata_and_fat_consts():
        # E5: a non-canonical metadata type and a constant at a container/dyn fat kind are refused
        # by the projector, and the model marks exactly those nodes (rules DERIVED off
        # `fn check_metadata_ty` and the `Inst::Const` arm).
        sem = derive_semantics(texts)
        assert sem["metadata_ty_check"]["ops"] == ["ptr_metadata", "ptr_from_parts"], sem
        assert sem["fat_const_refusal"]["kinds"] == ["ContainerLen", "ContainerVtable", "TraitObject"]

        def marked(texts_, text):
            fs = list(SYN_FUNCS) + [("helper::e5::<__trust_args@0>", text)]
            with tempfile.TemporaryDirectory() as td:
                synth_artifact(td, fs)
                mod = parse_artifact(td)
            sem_ = derive_semantics(texts_)
            annotate_d14(mod, sem_)
            ins = mod["funcs"][len(SYN_FUNCS)]["blocks"][0]["insts"]
            return [i["mnem"] for i in ins if unimaged_operand(i, sem_)]
        meta = "bb0(%0: fatptr<container_len>):\n    %1 = ptr_metadata fatptr<container_len> %0 to {}\n    ret %1"
        assert marked(texts, meta.format("u64")) == []
        assert marked(texts, meta.format("ptr")) == ["ptr_metadata"]
        assert marked(texts, meta.format("u32")) == ["ptr_metadata"]
        fat = "bb0:\n    %0 = const fatptr<{}> {{ 0, 0 }}\n    ret %0"
        assert marked(texts, fat.format("container_len")) == ["const"]
        assert marked(texts, fat.format("dyn.3")) == ["const"]
        assert marked(texts, fat.format("str")) == []
        gone = dict(texts, projector=texts["projector"].replace(
            "fn check_metadata_ty(", "fn check_metadata_gone(", 1))
        assert derive_semantics(gone)["metadata_ty_check"] == {}
        assert marked(gone, meta.format("ptr")) == []

    arm("E5 / D14: the projector's DERIVED certification images D14's align read and marks exactly "
        "the first uncertified vtable use (another slot or width, a store, an escape); without the "
        "projector function nothing is marked, and a moved slot is refused", a_d14_vtable_certify)
    arm("E5: a non-canonical metadata type and a container/dyn fat constant are refused, as the "
        "projector's DERIVED rules say; a canonical pair and a `str` constant are not",
        a_e5_metadata_and_fat_consts)
    arm("C-M0: a WS4.3 module (non-bare fn and global symbols QUOTED) measures exactly as its legacy "
        "twin; a quoted/raw mix and a quoted bare-able name are REFUSED", a_quoted_symbols)
    arm("C-M0: a `const` of TUPLE type reads its type with the type grammar (`(i32, ptr)`, never "
        "`(i32,`), so the D3 arm's exact two-lane ABI thunk is accepted and a wrong lane still refused",
        a_const_tuple_type)
    arm("measures the synthetic module exactly", a_measures_exactly)
    arm("memo §18: D12 images `bitcast ptr -> ptr` as copy (undef and callee rules follow the copy; "
        "without the projector function it is cast_unmodelled); a sited UB halt is `unreachable`, "
        "never assert_false (unsited: refused; off an assert: unimaged); D13 credits a shim site "
        "through its exact ABI thunk (no lane / malformed: refused; the shim named as a value: not "
        "credited)", a_d12_ub_halts_and_thunks)
    arm("D1: a by-value call_indirect returns iff a target of its exact, complete, same-signature "
        "set returns (every missing piece keeps call_unknown); D11: only a certified TLS address "
        "is imaged", a_by_value_and_tls)
    arm("a declared FOREIGN premise call blocks exactly as the `assert false` it replaces, and a "
        "declaration is never a closure body", a_declarations)
    arm("a malformed declaration table (non-foreign, twice, with a body, uncalled, unlisted, a "
        "bodiless member) is refused", a_declaration_tables_refused)
    arm("least fixpoint: a base-less recursion does not return (GFP control does)", a_lfp_not_gfp)
    arm("every fault family fires, and the review rule misses a tuple insertfield", a_rules_fire)
    arm("D10: native atomics are imaged exactly as the projector's seq_atomic_image says (umax and a "
        "weak cmpxchg are not), their pointer is an undef-checked base, and without the image nothing "
        "is", a_seq_atomics)
    arm("pass at baseline; baseline better than its artifact FAILS; hand edit REFUSED",
        a_gate_cycle)
    arm("regression FAILS; rebase/reseat cannot hide it; an improvement rebases", a_regression_and_rebase)
    arm("a baseline naming a different metric set is refused", a_metric_set_moved)
    arm("a moved EvalIR undef_ arm refuses the rule resting on it", a_semantics_anchor)
    arm("an anchor planted in a COMMENT does not satisfy the rule", a_semantics_comment_cannot_anchor)
    arm("an IRInst constructor with no census/projector arm is refused", a_irinst_bijection)
    arm("census.rs EMITTED_INSTS disagreeing with the IRInst inductive is refused",
        a_census_disagrees)
    arm("reseat raises a baseline only on the SAME artifact after an instrument change",
        a_reseat)
    arm("borrow_mut shares borrow's DECLARED image (an undeclared shared arm is refused); end_borrow/"
        "bor have no image; inttoptr is derived unmodelled", a_borrow_mut_unimaged)
    arm("malformed or inconsistent manifest is refused, never read as empty", a_malformed)
    arm("truncated / unknown / malformed text is refused", a_truncated_text)
    arm("a missing or ambiguous target root is refused", a_targets)
    arm("a type/constant/global the projector cannot image blocks and counts; imaged "
        "controls do not", a_operand_images)
    arm("operand images are DERIVED from the projector (a grown arm images, a moved rule "
        "refuses)", a_operand_derived)
    arm("E3b: `uninit` parses, and stands only as a direct struct/tuple lane (else REFUSED)",
        a_uninit_lane_parse_and_placement)
    arm("E3b: an uninit-seeded body is blocked in the GATED model (reader A has no image) and "
        "returns only in the informational pending-pin figure", a_uninit_lane_is_pending_not_gated)
    arm("E3b: the pending-pin image is DERIVED from reader B and the shape table, and vanishes "
        "once reader A images the constant", a_pending_image_is_derived)
    arm("an instrument-only drop is not rebase-able; reseat records it and may add a metric",
        a_instrument_moves_need_reseat)
    arm("a symaddr<NAME> is delimited by the module's function names, never by brackets alone",
        a_symaddr_by_name)
    arm("manifest v3 is read and measures as its v2 twin; a v3 missing/malformed bb, "
        "mir_digest or fuel is refused", a_manifest_v3)
    bad = [r for r in results if not r[1]]
    for name, ok, why in results:
        print(f"  {'ok  ' if ok else 'FAIL'} {name}" + (f"\n       {why}" if why else ""))
    print(f"SELFTEST={'ok' if not bad else 'fail'} arms={len(results)} failed={len(bad)}")
    return EXIT_PASS if not bad else EXIT_FAIL


def build_parser():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--artifact-dir")
    ap.add_argument("--repo-root", default=REPO_ROOT)
    ap.add_argument("--baseline", default=DEFAULT_BASELINE)
    ap.add_argument("--report")
    ap.add_argument("--rebase", action="store_true")
    ap.add_argument("--init", action="store_true")
    ap.add_argument("--reseat", action="store_true")
    ap.add_argument("--reason")
    ap.add_argument("--self-test", "--selftest", dest="self_test", action="store_true")
    ap.add_argument("--pinned-inputs", action="store_true",
                    help="print the first-party modules this script runs besides itself; run nothing")
    return ap


def main(argv=None):
    try:
        args = build_parser().parse_args(argv)
    except SystemExit as exc:
        return EXIT_REFUSED if exc.code else EXIT_PASS
    try:
        return run(args)
    except Refusal as exc:
        print(f"REFUSED: {exc}")
        return EXIT_REFUSED
    except Exception as exc:  # noqa: BLE001 - an unexpected error is never a verdict
        print(f"REFUSED: internal error {type(exc).__name__}: {exc}")
        return EXIT_REFUSED


if __name__ == "__main__":
    sys.exit(main())
