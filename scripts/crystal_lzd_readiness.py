#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0

"""Could the DERIVED closure of `Level::is_zero` be minted as one EvalIR module?

    scripts/crystal_lzd_readiness.py [--check] [--self-test] [--emit]

WHY THIS EXISTS.  Link 4 for the designated target holds today over
`ir_lzb_module`, whose function 1 is an AUTHORED model of the deref, and the
whole point of Phase B is to retire that authored function.  The material to do
it exists: the crate module carries `is_zero` and the real
`<level::LevelArc as std::ops::Deref>::deref`, and the callee sidecar derives
the three bodies that deref reaches.  Whether those five bodies can be MINTED as
one module and EXECUTED is a different question from whether they exist, and it
had been answered by reading rather than by measuring.

It is two mechanical questions and this script answers both:

  1. INSTRUCTION COVERAGE.  Every opcode in the merged text must be a modelled
     `IRInst` constructor.  The census is derived TWICE and required to agree --
     `EMITTED_INSTS` in `crates/clean-verify/tests/eval_ir/census.rs` and the
     `IRInst` inductive in
     `crates/clean-verify/src/spec/core_spec/eval_ir_syntax.rs` -- the same two
     sources, through the same function, that `scripts/evalir_coverage.py` uses
     for its denominator.  One unmodelled opcode means the module cannot be
     built at all, and that is a hard failure here rather than a surprise
     halfway through a mint.

  2. CALL CLOSURE.  Every `call` in the merged module must reach a body IN the
     merged module.  The crate module addresses its two foreign callees as
     DECLARATIONS by crate-level func id; the sidecar addresses its members by
     its own dense ids; the manifest's `roots[].crate_decl_func_ids` ->
     `roots[].sidecar_func_id` is the join, and a declaration the manifest does
     not join is left over and named.

WHAT THIS DOES NOT CLAIM.  It is a READINESS measurement, not a mint and not a
proof.  It does not build a module, register anything with the kernel, or say
that any body is CORRECT -- that is links 3-5, per chain, elsewhere.  Green here
means only that the two mechanical obstacles to attempting the mint are absent.
An opcode being modelled says the machine has a dispatch arm for it, NOT that
the arm agrees with the reference interpreter: `data/evalir_adequacy_grid.json`
carries the measured disagreements, four of which are on `borrow`/`copy`/`load`,
which this very closure uses.

FAIL-CLOSED.  An unmodelled opcode, an unresolved call, a manifest that reports
`closed: false` or a non-empty `escaping`, a missing input, or the two
denominator sources disagreeing: each aborts nonzero and writes NOTHING.

The output is content-derived (input sha256s, no timestamps), so re-running on
an unchanged tree is a no-op diff.
"""

import argparse
import copy
import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT_REL = "data/crystal_lzd_readiness.json"
SCHEMA = "crystal-lzd-readiness-v1"

CENSUS_PATH = "crates/clean-verify/tests/eval_ir/census.rs"
SYNTAX_PATH = "crates/clean-verify/src/spec/core_spec/eval_ir_syntax.rs"
CRATE_ROOT = "crates/clean-verify/tests/fixtures/level_is_zero.trust-ir.txt"
CRATE_DEREF = "crates/clean-verify/tests/fixtures/level_is_zero_deref_callee.trust-ir.txt"
SIDECAR_DIR = "data/crystal_callee_sidecar_step1_2026-09-09"
SIDECAR_TEXT = SIDECAR_DIR + "/clean_kernel.callees.trust-ir.txt"
SIDECAR_MANIFEST = SIDECAR_DIR + "/clean_kernel.callees.manifest.json"
CLOSURE_RECORD = "data/crystal_sidecar_closure_2026-09-10.json"
ACTIVATION_GEN = "scripts/gen_lzb_activation.py"
ARCINNER = "alloc::sync::ArcInner"
ARC_DEREF = "as core::ops::deref::Deref>::deref"

# Text opcode -> `IRInst` constructor name. Only the spellings that DIFFER are
# listed; everything else is the identity, and an opcode that is neither is
# UNMODELLED rather than quietly mapped.
OPCODE_TO_CTOR = {
    "const": "const_",
    "zext": "cast",
    "sext": "cast",
    "trunc": "cast",
    "bitcast": "cast",
    "ptrtoint": "cast",
    "inttoptr": "cast",
    "ptr_from_parts": "ptrfromparts",
    "ptr_metadata": "ptrmetadata",
    "ptr_data": "ptrdata",
    "global_addr": "globaladdr",
    "call_indirect": "callindirect",
    "extract_element": "extractelement",
}

# Rows that open a declaration, a type, a block or a module header -- never an
# instruction. Matched BEFORE the opcode regex, because `rustcc fn @…` would
# otherwise read as an opcode named `rustcc`, which is exactly the false
# positive this comment exists to stop (measured: it reported `rustcc` as an
# unmodelled constructor twice).
NON_INSTRUCTION = re.compile(
    r"^(?:\w+\s+)*(?:declare\s+)?fn @|^bb[\w.]*[(:]|^\}|^struct |^enum |^functy"
    r"|^type |^module |^file |^obligation |^global "
)
OPCODE = re.compile(r"^%\d+\s*=\s*([a-z_]+)")
BARE_OPCODE = re.compile(r"^([a-z_]+)\b")
# What may stand before `fn @` in a header: calling-convention / linkage words and an optional
# `declare`, as the `fn @` header regex this replaced admitted. The SYMBOL after it is read by the
# shared reader (M2, 2026-09-27): trust-ir WS4.3 prints a non-bare name QUOTED, and
# `crystal_trust_ir_symbols` decodes it, refuses what the printer cannot write, and holds a module
# to one grammar.
FN_PREFIX = re.compile(r"(?:\w+ (?=(?:\w+ )*fn @))*")
CALL_ID = re.compile(r"\bcall @func\.(\d+)")
# A `struct` row AFTER its symbol (read by the shared reader): the legacy field list and layout.
STRUCT_REST = re.compile(
    r"^ \{(?P<fields>[^}]*)\}"
    r"(?: size=(?P<size>\d+))?(?: align=(?P<align>\d+))?(?: repr=(?P<repr>\w+))?"
    r" id=(?P<id>\d+)$"
)
# The authored model's constant, read from an ANCHORED comment in the activation
# generator. A declaration that stops matching is a hard refusal, never a zero --
# the same disposition gen_lzb_activation and gen_slot_lemmas take when the const
# they pin stops matching.
AUTHORED_OFFSET = re.compile(r"^# A-CLZ-DEREF-ARC-DATA-OFFSET, measured (\d+) by$", re.M)


class ReadinessError(Exception):
    """A fail-closed refusal; nothing is written."""


# ------------------------------------------------------------------ denominator


# The census parser is IMPORTED, never re-implemented. `scripts/evalir_coverage.py`
# already derives this denominator from the same two sources and requires them to
# agree, and its own scoreboard row `evalir.denominator_disagreements` exists
# because two readers of one denominator drift. A second copy of the parser here
# would be a second reader, so this module borrows the first one outright and a
# change to the census's spelling moves both at once or neither.
sys.path.insert(0, str(Path(__file__).resolve().parent))
import evalir_coverage as _coverage  # noqa: E402
import crystal_trust_ir_symbols as tir_symbols  # noqa: E402

# Read by check_gate_registry.py (PINNED_INPUTS_MARKER): `--pinned-inputs` prints the first-party
# modules this script executes besides itself (derived from its imports).
ANSWERS_PINNED_INPUTS = True


def derive_denominator(census_text, syntax_text):
    """The pinned constructed-`Inst` census, via `evalir_coverage`'s own parser."""
    try:
        return _coverage.derive_denominator(census_text, syntax_text)
    except _coverage.CoverageError as e:
        raise ReadinessError(str(e)) from e


# ----------------------------------------------------------------------- parse


def functions(text):
    """[(name, [body lines])] in the order the text declares them, each name DECODED."""
    out, cur = [], None
    syms = tir_symbols.ModuleSymbols(FN_PREFIX)
    for n, line in enumerate(text.splitlines(), 1):
        s = line.rstrip()
        try:
            fh = syms.fn_header(s.strip(), f"line {n}")
        except tir_symbols.SymbolRefusal as e:
            raise ReadinessError(f"trust-ir text line {n}: {e}") from e
        if fh is not None:
            cur = (fh[0], [])
            out.append(cur)
            continue
        if cur is not None:
            if s.startswith("}"):
                cur = None
            else:
                cur[1].append(s)
    return out


def opcodes(text):
    """{opcode: count} over every instruction row of a trust-ir text."""
    found = {}
    for line in text.splitlines():
        s = line.split(";")[0].strip()
        if not s or NON_INSTRUCTION.match(s):
            continue
        m = OPCODE.match(s) or BARE_OPCODE.match(s)
        if m:
            found[m.group(1)] = found.get(m.group(1), 0) + 1
    return found


def sha256_file(path):
    h = hashlib.sha256()
    h.update(Path(path).read_bytes())
    return h.hexdigest()


# ---------------------------------------------------------------------- derive


def derive(root):
    root = Path(root)
    paths = {
        "crate_root": root / CRATE_ROOT,
        "crate_deref": root / CRATE_DEREF,
        "sidecar_text": root / SIDECAR_TEXT,
        "sidecar_manifest": root / SIDECAR_MANIFEST,
        "closure_record": root / CLOSURE_RECORD,
        "activation_gen": root / ACTIVATION_GEN,
        "census": root / CENSUS_PATH,
        "syntax": root / SYNTAX_PATH,
    }
    for key, p in paths.items():
        if not p.is_file():
            raise ReadinessError(f"input missing: {key} -> {p}")

    census = derive_denominator(
        paths["census"].read_text(encoding="utf-8"),
        paths["syntax"].read_text(encoding="utf-8"),
    )
    census_set = set(census)

    manifest = json.loads(paths["sidecar_manifest"].read_text(encoding="utf-8"))
    record = json.loads(paths["closure_record"].read_text(encoding="utf-8"))
    return _derive_from(paths, census, census_set, manifest, record)


def _derive_from(paths, census, census_set, manifest, record):
    if manifest.get("closed") is not True:
        raise ReadinessError(
            "the sidecar manifest reports closed=%r — a bundle that does not "
            "close its own edges cannot close anything" % (manifest.get("closed"),)
        )
    escaping = manifest.get("escaping")
    if escaping:
        raise ReadinessError(f"the sidecar manifest names escaping callees: {escaping}")

    texts = {k: paths[k].read_text(encoding="utf-8") for k in
             ("crate_root", "crate_deref", "sidecar_text")}

    # 1. INSTRUCTION COVERAGE over the merged text.
    merged = {}
    per_source = {}
    for key, text in texts.items():
        got = opcodes(text)
        per_source[key] = dict(sorted(got.items()))
        for op, n in got.items():
            merged[op] = merged.get(op, 0) + n
    unmodelled, mapping = [], {}
    for op in sorted(merged):
        ctor = OPCODE_TO_CTOR.get(op, op)
        if ctor in census_set:
            mapping[op] = ctor
        else:
            unmodelled.append({"opcode": op, "would_be": ctor, "count": merged[op]})
    if unmodelled:
        raise ReadinessError(
            "UNMODELLED opcode(s) in the derived closure: %s — the module cannot "
            "be minted until the machine has a dispatch arm for each"
            % ", ".join(u["opcode"] for u in unmodelled)
        )

    # 2. CALL CLOSURE, read from the committed closure record.
    #
    # NOT joined by crate func id, and the reason is measured rather than
    # assumed. `@func.N` is a WHOLE-CRATE index and it renumbers between dumps:
    # the committed deref fixture (the 2026-08-21 lane18 rebaseline) calls
    # `@func.7211` and `@func.6516`, while the sidecar manifest joins the same
    # two declarations at `4938` and `4939`, because the sidecar ran against a
    # later dump. The bodies agree -- the 2026-09-09 revalidation measured all
    # 21 fixtures NUMBERING-ONLY with zero structural drift -- so the ids are
    # the only thing that moved, and a Phase-B mint that joins the pair by id
    # will silently address the wrong function. The join is by NAME, and
    # `scripts/crystal_sidecar_closure.py` already performed that walk against
    # ONE dump, where the ids are coherent; its committed record is the
    # authority here.
    for key, want in (("schema", "crystal-sidecar-closure-v1"),
                      ("target", "level::Level::is_zero")):
        if record.get(key) != want:
            raise ReadinessError(
                f"the closure record's {key} is {record.get(key)!r}, expected {want!r}"
            )
    rec_manifest = record.get("sidecar_manifest") or {}
    if rec_manifest.get("closed") is not True or rec_manifest.get("escaping"):
        raise ReadinessError(
            "the closure record's own manifest summary is not closed "
            f"(closed={rec_manifest.get('closed')!r}, "
            f"escaping={rec_manifest.get('escaping')!r})"
        )
    if sorted(rec_manifest.get("members") or []) != sorted(
            m["name"] for m in manifest.get("members", [])):
        raise ReadinessError(
            "the closure record and the sidecar manifest name different members "
            "— they are not describing the same bundle"
        )
    closure = record.get("closure") or {}
    indirect = closure.get("indirect_calls")
    if indirect:
        raise ReadinessError(
            f"the closure contains {len(indirect)} indirect call(s): a "
            "`call_indirect` has no static target, so the closure is not "
            "statically known and no module over it is closed"
        )
    derived = record.get("derived_by_sidecar") or []
    declarations = closure.get("declarations")
    if declarations != len(derived):
        raise ReadinessError(
            f"the closure has {declarations} declaration(s) and the record "
            f"derives {len(derived)} of them — the difference is what no body "
            "covers, and a module over it would go stuck no_func"
        )
    if not derived:
        raise ReadinessError(
            "the record derives NO declaration; without a derived body the "
            "closure is exactly the pre-sidecar state"
        )
    joined = {}
    for d in derived:
        joined[str(d.get("crate_func_id"))] = d.get("name")

    # A structural cross-check that SURVIVES renumbering: the committed deref
    # fixture must call exactly as many distinct callees as the record has
    # declarations. Ids cannot be compared across dumps; arity can.
    crate_calls = sorted({int(x) for x in CALL_ID.findall(texts["crate_deref"])})
    if len(crate_calls) != declarations:
        raise ReadinessError(
            f"the committed deref fixture calls {len(crate_calls)} distinct "
            f"callee(s) {crate_calls} and the closure record has "
            f"{declarations} declaration(s) — the fixture and the record are "
            "not describing the same body"
        )

    for r in manifest.get("roots", []):
        if r.get("outcome") != "resolved":
            raise ReadinessError(
                "manifest root %r is %r, not resolved — its declaration has no "
                "derived body to join to" % (r.get("callee_def_path"), r.get("outcome"))
            )

    # Every sidecar-internal call must be a member or the ruled panic terminal.
    terminals = list(manifest.get("panic_terminals", []))
    internal, to_terminal = [], []
    for m in manifest.get("members", []):
        for c in m.get("calls", []):
            cls = c.get("class")
            if cls == "member":
                internal.append({"from": m["name"], "to": c["resolved"]})
            elif cls == "panic-terminal":
                to_terminal.append({"from": m["name"], "to": c["resolved"]})
            else:
                raise ReadinessError(
                    "sidecar member %r has a call classed %r, which is neither a "
                    "member nor the ruled panic terminal" % (m["name"], cls)
                )

    # 3. LAYOUT CROSS-CHECK. The authored `ir_lzb_deref` geps by SIXTEEN and
    #    `EncodesLevelArcF` places every child at `Nat.add b ir_d16`. Ledger row
    #    A-CLZ-DEREF-ARC-DATA-OFFSET carries that as a target-specific
    #    measurement taken from two runtime addresses, and names its own second
    #    discharge route: "make the deref's own callees bodyful, at which point
    #    the offset comes from the emitted code". They are bodyful, so the
    #    offset is RECOMPUTED here from rustc's own field sizes and the emitted
    #    gep constant must equal it. A disagreement means the authored model is
    #    wrong about the machine, and this refuses rather than reports.
    structs = {}
    syms = tir_symbols.ModuleSymbols(FN_PREFIX)
    for n, line in enumerate(texts["sidecar_text"].splitlines(), 1):
        try:
            row = None if syms.fn_header(line.strip(), f"line {n}") else \
                syms.type_row(line.strip(), f"line {n}")
        except tir_symbols.SymbolRefusal as e:
            raise ReadinessError(f"sidecar text line {n}: {e}") from e
        m = STRUCT_REST.match(line.strip()[row[3]:]) if row and row[0] == "struct" else None
        if m:
            structs[int(m.group("id"))] = {
                "name": row[1],
                "fields": [f.strip() for f in m.group("fields").split(",") if f.strip()],
                "size": int(m.group("size")) if m.group("size") else None,
                "align": int(m.group("align")) if m.group("align") else None,
                "repr": m.group("repr"),
            }
    inner = [v for v in structs.values() if v["name"] == ARCINNER]
    if len(inner) != 1:
        raise ReadinessError(
            f"expected exactly one `{ARCINNER}` row in the sidecar type table, "
            f"found {len(inner)}"
        )
    inner = inner[0]
    if len(inner["fields"]) < 2:
        raise ReadinessError(
            f"`{ARCINNER}` has {len(inner['fields'])} field(s); the data offset is "
            "the offset of its LAST field and there is nothing in front of it"
        )
    offset = 0
    for f in inner["fields"][:-1]:
        if not f.startswith("struct."):
            raise ReadinessError(
                f"`{ARCINNER}` header field {f!r} is not a struct row, so its size "
                "cannot be read out of this table"
            )
        fs = structs.get(int(f.split(".", 1)[1]))
        if fs is None or fs["size"] is None or fs["align"] is None:
            raise ReadinessError(
                f"`{ARCINNER}` header field {f!r} has no size/align in the table, "
                "so the data offset cannot be recomputed"
            )
        if offset % fs["align"]:
            offset += fs["align"] - (offset % fs["align"])
        offset += fs["size"]

    deref_body = [b for n, b in functions(texts["sidecar_text"]) if ARC_DEREF in n]
    if len(deref_body) != 1:
        raise ReadinessError(
            f"expected exactly one `{ARC_DEREF}` body in the bundle, "
            f"found {len(deref_body)}"
        )
    consts, emitted = {}, None
    for line in deref_body[0]:
        t = line.split(";")[0].strip()
        mc = re.match(r"^(%\d+) = const i(?:64|size) (-?\d+)$", t)
        if mc:
            consts[mc.group(1)] = int(mc.group(2))
        mg = re.match(r"^%\d+ = gep(?: inbounds)? i8, ptr %\d+, (%\d+)$", t)
        if mg:
            if emitted is not None:
                raise ReadinessError(
                    "the derived Arc::deref body geps more than once; which one is "
                    "the data offset is no longer mechanical"
                )
            emitted = consts.get(mg.group(1))
    if emitted is None:
        raise ReadinessError(
            "the derived Arc::deref body has no byte gep with a constant offset, "
            "so there is nothing to check the authored model against"
        )
    if emitted != offset:
        raise ReadinessError(
            f"the derived Arc::deref geps by {emitted} and `{ARCINNER}`'s own field "
            f"sizes put its data at {offset} — the emitted code and rustc's layout "
            "descriptor disagree, and no model can be right about both"
        )
    gen = (paths["activation_gen"]).read_text(encoding="utf-8")
    ma = AUTHORED_OFFSET.search(gen)
    if ma is None:
        raise ReadinessError(
            f"{ACTIVATION_GEN}: the anchored `# A-CLZ-DEREF-ARC-DATA-OFFSET, "
            "measured N by` comment no longer matches; the authored model's "
            "constant cannot be read, and a MISSING anchor is a refusal, not a zero"
        )
    authored = int(ma.group(1))
    if authored != offset:
        raise ReadinessError(
            f"the authored deref model geps by {authored} and the DERIVED body geps "
            f"by {offset} — ledger row A-CLZ-DEREF-ARC-DATA-OFFSET is now false of "
            "the machine it models"
        )
    payload = inner["size"] - offset if inner["size"] is not None else None

    fn_names = []
    for key in ("crate_root", "crate_deref", "sidecar_text"):
        for name, _ in functions(texts[key]):
            fn_names.append({"source": key, "name": name})

    return {
        "schema": SCHEMA,
        "verdict": "READY",
        "what": (
            "The five bodies of `level::Level::is_zero`'s derived reachable "
            "closure use only MODELLED IRInst constructors, and every call in "
            "them reaches a body in the merged pair. This is a readiness "
            "measurement for the Phase-B mint, NOT a mint and NOT a proof."
        ),
        "functions": fn_names,
        "function_count": len(fn_names),
        "distinct_opcodes": len(mapping),
        "opcode_to_constructor": mapping,
        "opcode_counts": dict(sorted(merged.items())),
        "opcodes_per_source": per_source,
        "constructor_census": len(census),
        "unmodelled": [],
        "layout_cross_check": {
            "what": (
                "The authored `ir_lzb_deref` geps by SIXTEEN. That constant is now "
                "checked against the compiler rather than against two runtime "
                "addresses, which is the second discharge route ledger row "
                "A-CLZ-DEREF-ARC-DATA-OFFSET names for itself."
            ),
            "arcinner": {
                "fields": inner["fields"],
                "size": inner["size"],
                "align": inner["align"],
                "repr": inner["repr"],
            },
            "data_offset_recomputed_from_field_sizes": offset,
            "emitted_gep_constant_in_the_derived_body": emitted,
            "authored_model_constant": authored,
            "payload_size": payload,
            "all_three_agree": True,
            "what_this_narrows": (
                "The ledger row states `ArcInner` is private `alloc` internals "
                "'with no stated repr'. rustc's own layout descriptor reports "
                "repr=c for it, and the sysroot source declares "
                "`#[repr(C, align(2))] struct ArcInner<T: ?Sized> { strong: "
                "Atomic<usize>, weak: Atomic<usize>, data: T }`. Under repr(C) the "
                "field ORDER is guaranteed, so the offset is not a layout accident: "
                "it is two pointer-sized atomic counts. The obligation that survives "
                "is the pointer width, not the layout algorithm. Closing the row is "
                "an owner act; this measurement is the evidence for it."
            ),
        },
        "the_ids_renumber_between_dumps": {
            "why_it_matters": (
                "`@func.N` is a WHOLE-CRATE index. A Phase-B mint that joins the "
                "crate module to the sidecar bundle by id will address the wrong "
                "function whenever the two came from different dumps. Join by NAME."
            ),
            "committed_deref_fixture_calls": crate_calls,
            "closure_record_declaration_ids": sorted(int(k) for k in joined),
            "bodies_agree": (
                "the 2026-09-09 revalidation measured all 21 committed fixtures "
                "NUMBERING-ONLY at HEAD with zero structural drift, so the ids are "
                "the only thing that moved"
            ),
        },
        "call_closure": {
            "crate_declarations_derived": {str(k): v for k, v in sorted(joined.items())},
            "sidecar_internal_calls": internal,
            "calls_to_the_ruled_panic_terminal": to_terminal,
            "panic_terminals": terminals,
            "escaping": [],
        },
        "not_claimed": [
            "that any body is CORRECT — that is links 3-5, per chain, elsewhere",
            "that a modelled constructor AGREES with the reference interpreter; "
            "data/evalir_adequacy_grid.json carries the measured disagreements, "
            "four of which are on borrow/copy/load, which this closure uses",
            "that the module has been minted, registered or executed",
            "A0's fifth criterion AS WRITTEN, which reads ONE spliced "
            "instruction-bearing prefix; this is two artifacts joined by a manifest",
        ],
        "provenance": {
            "derived_by": "scripts/crystal_lzd_readiness.py",
            "inputs": [
                {"path": rel, "sha256": sha256_file(paths[key])}
                for key, rel in (
                    ("crate_root", CRATE_ROOT),
                    ("crate_deref", CRATE_DEREF),
                    ("sidecar_text", SIDECAR_TEXT),
                    ("sidecar_manifest", SIDECAR_MANIFEST),
                    ("closure_record", CLOSURE_RECORD),
                    ("activation_gen", ACTIVATION_GEN),
                    ("census", CENSUS_PATH),
                    ("syntax", SYNTAX_PATH),
                )
            ],
            "denominator_sources": {
                "census": {"path": CENSUS_PATH, "anchor": "EMITTED_INSTS"},
                "syntax": {"path": SYNTAX_PATH, "anchor": "inductive IRInst : Type"},
            },
        },
    }


def render(doc):
    return json.dumps(doc, indent=2, sort_keys=False) + "\n"


# -------------------------------------------------------------------- self-test


def self_test(root):
    root = Path(root)
    failures = 0

    def arm(name, fn):
        nonlocal failures
        try:
            fn()
        except ReadinessError as e:
            print(f"  self-test ARM ok: {name} -> detected ({e})")
            return
        print(f"  self-test ARM FAILED: {name} -> mutation NOT detected")
        failures += 1

    paths = {
        "crate_root": root / CRATE_ROOT,
        "crate_deref": root / CRATE_DEREF,
        "sidecar_text": root / SIDECAR_TEXT,
        "sidecar_manifest": root / SIDECAR_MANIFEST,
        "closure_record": root / CLOSURE_RECORD,
        "activation_gen": root / ACTIVATION_GEN,
        "census": root / CENSUS_PATH,
        "syntax": root / SYNTAX_PATH,
    }
    census_text = paths["census"].read_text(encoding="utf-8")
    syntax_text = paths["syntax"].read_text(encoding="utf-8")
    census = derive_denominator(census_text, syntax_text)
    real_manifest = json.loads(paths["sidecar_manifest"].read_text(encoding="utf-8"))
    real_record = json.loads(paths["closure_record"].read_text(encoding="utf-8"))

    # 1. A constructor removed from the census: an opcode the closure uses goes
    #    unmodelled. `borrow` is chosen because Phase B added it FOR this
    #    closure, so its removal is the regression this arm is really about.
    arm(
        "a constructor the closure uses is removed from the census",
        lambda: _derive_from(paths, census, set(census) - {"borrow"}, real_manifest, real_record),
    )

    # 2. Manifest reports it is not closed.
    def not_closed():
        m = copy.deepcopy(real_manifest)
        m["closed"] = False
        _derive_from(paths, census, set(census), m, real_record)

    arm("manifest reports closed=false", not_closed)

    # 3. Manifest names an escaping callee.
    def escaping():
        m = copy.deepcopy(real_manifest)
        m["escaping"] = ["some::callee::that::got::away"]
        _derive_from(paths, census, set(census), m, real_record)

    arm("manifest names an escaping callee", escaping)

    # 4. A crate declaration loses its join: the deref calls a body nothing
    #    derives, which is precisely the pre-sidecar state.
    def unjoined():
        r = copy.deepcopy(real_record)
        r["derived_by_sidecar"] = r["derived_by_sidecar"][:1]
        _derive_from(paths, census, set(census), real_manifest, r)

    arm("a closure declaration is no longer derived by the sidecar", unjoined)

    def none_derived():
        r = copy.deepcopy(real_record)
        r["derived_by_sidecar"] = []
        r["closure"]["declarations"] = 0
        _derive_from(paths, census, set(census), real_manifest, r)

    arm("nothing is derived at all (the pre-sidecar state)", none_derived)

    def indirect():
        r = copy.deepcopy(real_record)
        r["closure"]["indirect_calls"] = [{"site": "f0/bb1#0"}]
        _derive_from(paths, census, set(census), real_manifest, r)

    arm("the closure contains an indirect call", indirect)

    def different_bundle():
        r = copy.deepcopy(real_record)
        r["sidecar_manifest"]["members"] = ["some::other::bundle::member"]
        _derive_from(paths, census, set(census), real_manifest, r)

    arm("the record and the manifest describe different bundles", different_bundle)

    # 5. A root that did not resolve.
    def unresolved_root():
        m = copy.deepcopy(real_manifest)
        m["roots"][0]["outcome"] = "declined"
        _derive_from(paths, census, set(census), m, real_record)

    arm("a manifest root did not resolve", unresolved_root)

    # 6. A sidecar-internal call with a class that is neither member nor the
    #    ruled panic terminal.
    def alien_call_class():
        m = copy.deepcopy(real_manifest)
        for mm in m["members"]:
            if mm.get("calls"):
                mm["calls"][0]["class"] = "who-knows"
                break
        _derive_from(paths, census, set(census), m, real_record)

    arm("a sidecar call is classed neither member nor panic-terminal", alien_call_class)

    # 7. The two denominator sources disagree.
    arm(
        "denominator sources disagree",
        lambda: derive_denominator(
            census_text.replace(f'"{census[0]}",', "", 1), syntax_text
        ),
    )

    # 9. M2 (2026-09-27): the SAME inputs printed by trust-ir WS4.3 -- every non-bare symbol of a
    #    `fn` header and a type/global row QUOTED -- derive the SAME document. The `fn @(.+?)` and
    #    `struct @([^ ]+)` regexes this replaced kept the quotes (the ArcInner row was then never
    #    found) and mis-cut a quoted name at its first space. A module mixing the two spellings,
    #    and an escape the printer cannot write, are refusals.
    import tempfile  # noqa: PLC0415 -- this arm's only use

    def respelled(mutate=None):
        with tempfile.TemporaryDirectory() as tmp:
            q = dict(paths)
            for key in ("crate_root", "crate_deref", "sidecar_text"):
                text = tir_symbols.respell_ws43(paths[key].read_text(encoding="utf-8"))
                q[key] = Path(tmp) / f"{key}.trust-ir.txt"
                q[key].write_text(mutate(key, text) if mutate else text, encoding="utf-8")
            if '@"' not in q["sidecar_text"].read_text(encoding="utf-8"):
                raise AssertionError("the re-spelled sidecar text carries no quoted symbol")
            return _derive_from(q, census, set(census), real_manifest, real_record)

    def verdict_surface(doc):
        # Everything but the input DIGESTS, which differ by construction (other bytes, same program).
        doc = copy.deepcopy(doc)
        doc.get("provenance", {}).pop("inputs", None)
        return doc

    try:
        q_doc, l_doc = respelled(), derive(root)
        same = verdict_surface(q_doc) == verdict_surface(l_doc) and q_doc != l_doc
    except ReadinessError as e:
        same = False
        print(f"  self-test ARM FAILED: the WS4.3-printed inputs were refused: {e}")
    if same:
        print("  self-test ARM ok: the WS4.3-printed (quoted-symbol) inputs derive the same document")
    else:
        print("  self-test ARM FAILED: the WS4.3-printed inputs derive a DIFFERENT document")
        failures += 1

    def mixed(key, text):
        if key != "sidecar_text":
            return text
        return text.replace('struct @"alloc::sync::ArcInner"', "struct @alloc::sync::ArcInner<x y>", 1)

    arm("a WS4.3 module mixing a quoted and a raw symbol", lambda: respelled(mixed))
    arm("a quoted symbol with an escape the printer cannot write",
        lambda: respelled(lambda k, t: t.replace('@"alloc::sync::ArcInner"', '@"alloc::sync\\qArcInner"', 1)
                          if k == "sidecar_text" else t))

    # 8. THE POSITIVE ARM. The unmutated inputs must derive READY, and the
    #    false positive that made this script wrong on its first run must stay
    #    dead: `rustcc fn @…` is a declaration row, not an opcode named
    #    `rustcc`.
    try:
        doc = derive(root)
    except ReadinessError as e:
        print(f"  self-test BASELINE FAILED: {e}")
        return 1
    if "rustcc" in doc["opcode_counts"]:
        print("  self-test ARM FAILED: `rustcc` read as an opcode (declaration row)")
        failures += 1
    else:
        print("  self-test ARM ok: `rustcc fn @…` is a declaration row, not an opcode")
    print(
        f"  self-test baseline ok: {doc['verdict']} — {doc['function_count']} bodies, "
        f"{doc['distinct_opcodes']} distinct opcodes, all modelled against a "
        f"{doc['constructor_census']}-constructor census"
    )
    if failures:
        print(f"self-test: {failures} arm(s) FAILED", file=sys.stderr)
        return 1
    print("self-test: all arms green")
    return 0


# ------------------------------------------------------------------------ main


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true",
                    help="refuse if the committed artifact is not what this emits")
    ap.add_argument("--self-test", action="store_true",
                    help="run the mutation arms")
    ap.add_argument("--emit", action="store_true",
                    help="write the artifact (the default when no mode is given)")
    ap.add_argument("--pinned-inputs", action="store_true",
                    help="print the first-party modules this script runs besides itself; run nothing")
    args = ap.parse_args(argv)
    if args.pinned_inputs:
        print("\n".join(tir_symbols.first_party_imports(Path(__file__))))
        return 0

    if args.self_test:
        return self_test(ROOT)
    try:
        doc = derive(ROOT)
    except ReadinessError as e:
        print(f"crystal_lzd_readiness: FAIL-CLOSED: {e}", file=sys.stderr)
        return 1
    text = render(doc)
    out = ROOT / OUT_REL
    if args.check:
        if not out.is_file():
            print(f"crystal_lzd_readiness: {OUT_REL} is absent; emit it", file=sys.stderr)
            return 1
        if out.read_text(encoding="utf-8") != text:
            print(f"crystal_lzd_readiness: {OUT_REL} is STALE; re-emit", file=sys.stderr)
            return 1
        print(f"crystal_lzd_readiness: --check: {OUT_REL} up to date "
              f"({doc['function_count']} bodies, {doc['distinct_opcodes']} opcodes, "
              f"all modelled)")
        return 0
    out.write_text(text, encoding="utf-8")
    print(f"crystal_lzd_readiness: wrote {OUT_REL}: {doc['verdict']} — "
          f"{doc['function_count']} bodies, {doc['distinct_opcodes']} distinct "
          f"opcodes, all modelled against a {doc['constructor_census']}-constructor "
          f"census; {len(doc['call_closure']['crate_declarations_derived'])} crate "
          f"declaration(s) joined")
    return 0


if __name__ == "__main__":
    sys.exit(main())
