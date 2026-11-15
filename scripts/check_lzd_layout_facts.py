#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Every layout constant in the `ir_lzd` proof, held against something MEASURED.

WHY THIS EXISTS
---------------
A4 and A5 over `ir_lzd_module` carry no authored FUNCTION. They still carry
authored NUMBERS, and until 2026-09-13 those numbers had up to four independent
spellings held in step by nothing but agreement:

  * `EncodesLevelArcD` places a Succ/Max/IMax child's `LevelArc` at `a+8` and
    `a+16`, and the child `Level` itself at `(succ b) + 16`;
  * `scripts/gen_lzd_activation.py`'s `child_of()` re-spells that `+16`;
  * the emitted body GEPs by 8 and 16, which is what actually happens;
  * `ArcInner`'s data offset is recomputable from the producer's own struct
    table, and `scripts/crystal_lzd_readiness.py` already recomputed it — but
    compared it only against the emitted gep, never against the two spellings in
    the proof.

So a reader had to take on trust that the relation describes the heap the body
walks. This gate removes the trust: every constant is derived from a COMMITTED
artifact and compared, and a disagreement is a refusal that names both sides.

It runs no compiler and reads no dump. Its inputs are
`crates/clean-verify/src/spec/core_spec/generated/ir_lzd.core.txt` (the emitted
body), `data/crystal_callee_sidecar_step1_2026-09-09/clean_kernel.callees.trust-ir.txt`
(the producer's struct table), and
`data/crystal_enum_layout_census_2026-08-21.json` (Level's own descriptor).

WHAT IT DOES NOT CLAIM
----------------------
That the producer's descriptors are faithful to rustc. That is a producer-side
fidelity obligation and it is the residual this gate makes SINGULAR rather than
discharges: after this, the proof assumes one thing (the artifact records the
layout correctly) instead of four numbers nobody checked.

    python3 scripts/check_lzd_layout_facts.py            # the gate
    python3 scripts/check_lzd_layout_facts.py --counts    # minted vs authored
    python3 scripts/check_lzd_layout_facts.py --self-test # mutation arms
    python3 scripts/check_lzd_layout_facts.py --pinned-inputs

SYMBOLS (M2, 2026-09-27). The struct table's row names are read by the shared
reader `scripts/crystal_trust_ir_symbols.py`: trust-ir WS4.3 prints a non-bare
name QUOTED (`struct @"alloc::sync::ArcInner" {`), the reader decodes it, refuses
what the printer cannot write, and holds the module to one grammar.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(ROOT / "scripts"))
import crystal_trust_ir_symbols as tir_symbols  # noqa: E402

# Read by check_gate_registry.py (PINNED_INPUTS_MARKER): `--pinned-inputs` prints the first-party
# modules this script executes besides itself (derived from its imports).
ANSWERS_PINNED_INPUTS = True

CORE = "crates/clean-verify/src/spec/core_spec/generated/ir_lzd.core.txt"
PROV = "crates/clean-verify/src/spec/core_spec/generated/ir_lzd.core.prov.json"
RELATION = "crates/clean-verify/src/spec/core_spec/eval_ir_lzd_correct.rs"
GENERATOR = "scripts/gen_lzd_activation.py"
SIDECAR = "data/crystal_callee_sidecar_step1_2026-09-09/clean_kernel.callees.trust-ir.txt"
CENSUS = "data/crystal_enum_layout_census_2026-08-21.json"
COUNTS_JSON = "data/crystal_lzd_proof_text_counts.json"

SPEC_FILES = [
    "crates/clean-verify/src/spec/core_spec/eval_ir_lzd_activation.rs",
    "crates/clean-verify/src/spec/core_spec/eval_ir_lzd_correct.rs",
    "crates/clean-verify/src/spec/core_spec/eval_ir_lzd_fresh.rs",
]

ARCINNER = "alloc::sync::ArcInner"
# A `struct` row AFTER its symbol (the symbol is the shared reader's): the legacy field list.
STRUCT_REST = re.compile(
    r"^ \{(?P<fields>[^}]*)\}"
    r"(?: size=(?P<size>\d+))?(?: align=(?P<align>\d+))?"
)


class LayoutError(Exception):
    """A layout constant in the proof disagrees with the artifact."""


def read(root: Path, rel: str) -> str:
    p = root / rel
    if not p.exists():
        raise LayoutError(f"{rel}: MISSING — this gate cannot be evaluated without it")
    return p.read_text()


# ---------------------------------------------------------------- the artifact


def gep_offsets_by_function(core: str) -> dict:
    """Every `gep`'s byte constant, keyed (func, base-ssa).

    Read off the COMMITTED core module, so this is where the emitted body
    actually reaches — not what any descriptor says it should.
    """
    consts: dict = {}
    out: dict = {}
    fn = None
    for line in core.splitlines():
        m = re.search(r"\(func (\d+)", line)
        if m:
            fn = int(m.group(1))
        m = re.search(r"\(results (\d+)\) \(const \(int 64\) \(int (-?\d+)\)\)", line)
        if m:
            consts[(fn, int(m.group(1)))] = int(m.group(2))
        m = re.search(r"\(results \d+\) \(gep \(int 8\) (\d+) \(idx (\d+)\)", line)
        if m:
            base, idx = int(m.group(1)), int(m.group(2))
            off = consts.get((fn, idx))
            if off is None:
                raise LayoutError(
                    f"{CORE}: func {fn} geps by %{idx}, which is not a 64-bit int "
                    "constant in the same function — this gate reads only the "
                    "constant-offset form and refuses rather than guessing"
                )
            out.setdefault((fn, base), set()).add(off)
    if not out:
        raise LayoutError(f"{CORE}: no `gep` found at all; the reader is broken")
    return out


def core_cfg(core: str) -> tuple:
    """Per-block geps, the CFG, and the entry switch — off the committed core.

    The set-of-offsets reading this replaced could not see WHICH variant reaches
    a gep, so an offset established on one arm silently vouched for every other
    arm. Measured 2026-09-13, that is not hypothetical: `Level::is_zero` geps +8
    only on the `max` path, and the relation asserted a +8 cell on `succ` and
    `imax` too. Both claims are true of Rust's layout and NEITHER is established
    by this artifact, which is the difference this function exists to see.
    """
    consts, geps, succs, switch = {}, {}, {}, {}
    fn = blk = None
    for line in core.splitlines():
        m = re.search(r"\(func (\d+)", line)
        if m:
            fn, blk = int(m.group(1)), None
            continue
        m = re.search(r"\(block (\d+)", line)
        if m:
            blk = int(m.group(1))
            succs.setdefault((fn, blk), set())
            continue
        m = re.search(r"\(results (\d+)\) \(const \(int 64\) \(int (-?\d+)\)\)", line)
        if m:
            consts[(fn, int(m.group(1)))] = int(m.group(2))
        m = re.search(r"\(results \d+\) \(gep \(int 8\) (\d+) \(idx (\d+)\)", line)
        if m:
            base, idx = int(m.group(1)), int(m.group(2))
            if (fn, idx) not in consts:
                raise LayoutError(
                    f"{CORE}: func {fn} geps by %{idx}, which is not a 64-bit int "
                    "constant in the same function — this gate reads only the "
                    "constant-offset form and refuses rather than guessing"
                )
            geps.setdefault((fn, blk), set()).add((base, consts[(fn, idx)]))
        m = re.search(r"\(br (\d+) ", line)
        if m:
            succs[(fn, blk)].add(int(m.group(1)))
        m = re.search(r"\(condbr \d+ (\d+) \(args[^)]*\) (\d+) ", line)
        if m:
            succs[(fn, blk)] |= {int(m.group(1)), int(m.group(2))}
        m = re.search(r"\(switch (\d+) (\d+) \(args\) \(cases (.*)\) (?:true|false)\)", line)
        if m:
            cases = {int(a): int(b)
                     for a, b in re.findall(r"\(case (\d+) (\d+) ", m.group(3))}
            switch[(fn, blk)] = (int(m.group(2)), cases)
            succs[(fn, blk)] |= set(cases.values()) | {int(m.group(2))}
    if (0, 0) not in switch:
        raise LayoutError(f"{CORE}: function 0's entry block does not switch on a tag")
    return geps, succs, switch


def receiver_offsets_per_tag(core: str, tags) -> dict:
    """For each variant tag, the receiver-relative offsets the body really geps.

    "Really" means: on the blocks reachable from the switch target for THAT tag.
    """
    geps, succs, switch = core_cfg(core)
    default, cases = switch[(0, 0)]
    out = {}
    for t in tags:
        seen, stack = set(), [cases.get(t, default)]
        while stack:
            b = stack.pop()
            if b in seen:
                continue
            seen.add(b)
            stack.extend(succs.get((0, b), ()))
        out[t] = {off for b in seen for base, off in geps.get((0, b), ()) if base == 0}
    return out


def closure_shape(core: str) -> dict:
    """Per function: is its CFG cyclic, and who does it call.

    This exists to keep ONE recorded diagnosis from being re-learned. The link-5
    note in docs/CRYSTAL_STATUS.md read, from 2026-09-11 to 2026-09-14, that the
    proven-output executor "is a bounded ACYCLIC path enumerator that fails
    closed on every backedge" and that `is_zero`'s bytes "are cyclic both ways at
    once". The first clause describes a real device in
    trust-cg-bridge/src/verify_output.rs; the second does not describe THIS
    closure, and the two together would send a lane to implement loop handling
    that changes nothing. Measured here so the refutation is re-derived on every
    push rather than believed.
    """
    geps, succs, switch = core_cfg(core)
    blocks: dict = {}
    calls: dict = {}
    fn = blk = None
    for line in core.splitlines():
        m = re.search(r"\(func (\d+)", line)
        if m:
            fn, blk = int(m.group(1)), None
            blocks.setdefault(fn, set())
            calls.setdefault(fn, [])
            continue
        if fn is None:
            continue
        m = re.search(r"\(block (\d+)", line)
        if m:
            blk = int(m.group(1))
            blocks[fn].add(blk)
        m = re.search(r"\(call (\d+) ", line)
        if m:
            calls[fn].append(int(m.group(1)))

    def cyclic(f: int) -> bool:
        colour: dict = {}

        def dfs(b: int) -> bool:
            colour[b] = 1
            for t in succs.get((f, b), ()):
                if colour.get(t) == 1:
                    return True
                if colour.get(t) is None and dfs(t):
                    return True
            colour[b] = 2
            return False

        return any(dfs(b) for b in sorted(blocks[f]) if colour.get(b) is None)

    return {
        "cyclic_cfgs": sorted(f for f in blocks if cyclic(f)),
        "functions": sorted(blocks),
        "call_graph": {f: sorted(set(v)) for f, v in sorted(calls.items())},
        "self_recursive": sorted(f for f, v in calls.items() if f in v),
    }


def relation_arms(rel_src: str) -> dict:
    """Each constructor of `EncodesLevelArcD`: its tag, and the offsets it claims."""
    arcd = const_body(rel_src, "SRC_ARCD")
    out = {}
    for chunk in arcd.split("\\n| ")[1:]:
        name = chunk.split(" :")[0]
        tag = re.search(r"ir_var ir_d(\d+)", chunk)
        if tag is None:
            raise LayoutError(f"{RELATION}: arm `{name}` names no variant tag")
        out[name] = (
            int(tag.group(1)),
            {int(x) for x in re.findall(r"Nat\.add a ir_d(\d+)", chunk)},
        )
    if not out:
        raise LayoutError(f"{RELATION}: SRC_ARCD has no constructor arms")
    return out


def arcinner_data_offset(sidecar: str) -> int:
    """Recompute `ArcInner`'s data offset from the producer's own struct table.

    The same algorithm `crystal_lzd_readiness.py` uses, and deliberately so: two
    gates recomputing one number the same way is a duplicate, but this one
    compares it against the PROOF and that one against the EMITTED CODE, so
    together they close the triangle.
    """
    structs = {}
    syms = tir_symbols.ModuleSymbols()
    for n, line in enumerate(sidecar.splitlines(), 1):
        try:
            row = None if syms.fn_header(line.strip(), f"line {n}") else \
                syms.type_row(line.strip(), f"line {n}")
        except tir_symbols.SymbolRefusal as e:
            raise LayoutError(f"{SIDECAR} line {n}: {e}") from e
        m = STRUCT_REST.match(line.strip()[row[3]:]) if row and row[0] == "struct" else None
        if not m:
            continue
        sid = re.search(r"id=(\d+)", line)
        if not sid:
            continue
        structs[int(sid.group(1))] = {
            "name": row[1],
            "fields": [f.strip() for f in m.group("fields").split(",") if f.strip()],
            "size": int(m.group("size")) if m.group("size") else None,
            "align": int(m.group("align")) if m.group("align") else None,
        }
    inner = [v for v in structs.values() if v["name"] == ARCINNER]
    if len(inner) != 1:
        raise LayoutError(
            f"{SIDECAR}: expected exactly one `{ARCINNER}` row, found {len(inner)}"
        )
    inner = inner[0]
    if len(inner["fields"]) < 2:
        raise LayoutError(
            f"`{ARCINNER}` has {len(inner['fields'])} field(s); its data offset is the "
            "offset of its LAST field and there is nothing in front of it"
        )
    off = 0
    for f in inner["fields"][:-1]:
        if not f.startswith("struct."):
            raise LayoutError(
                f"`{ARCINNER}` header field {f!r} is not a struct row, so its size "
                "cannot be read out of this table"
            )
        fs = structs.get(int(f.split(".", 1)[1]))
        if fs is None or fs["size"] is None or fs["align"] is None:
            raise LayoutError(
                f"`{ARCINNER}` header field {f!r} has no size/align in the table"
            )
        if off % fs["align"]:
            off += fs["align"] - (off % fs["align"])
        off += fs["size"]
    return off


def level_descriptor(census: dict) -> dict:
    """Level's own layout descriptor, out of the committed census."""
    rows = census.get("rows_producer_A_level_only") or {}
    if not rows:
        raise LayoutError(f"{CENSUS}: no `rows_producer_A_level_only`")
    texts = sorted(set(rows.values()))
    if len(texts) != 1:
        raise LayoutError(
            f"{CENSUS}: the three producers disagree about Level's layout, so there "
            f"is no single descriptor to check the proof against: {texts}"
        )
    t = texts[0]
    m = re.search(r"discriminants=\[([0-9,]*)\]", t)
    n = re.search(r"variants=(\d+)", t)
    niche = re.search(
        r"Niche\{untagged=(\d+) range=(\d+)\.\.=(\d+) start=(\d+) offset=(\d+)", t
    )
    if not (m and n and niche):
        raise LayoutError(f"{CENSUS}: Level's row is not the shape this reader parses: {t}")
    return {
        "text": t,
        "variants": int(n.group(1)),
        "discriminants": [int(x) for x in m.group(1).split(",") if x != ""],
        "untagged": int(niche.group(1)),
        "range": (int(niche.group(2)), int(niche.group(3))),
        "start": int(niche.group(4)),
        "offset": int(niche.group(5)),
    }


# ------------------------------------------------------------------- the proof


def const_body(src: str, name: str) -> str:
    m = re.search(r'const %s: &str = "(.*?)";\n' % re.escape(name), src, re.S)
    if not m:
        raise LayoutError(
            f"{RELATION}: `const {name}` not found. This gate reads string LITERALS, "
            "never prose; a declaration that stops matching is a refusal, not a zero"
        )
    return m.group(1)


def relation_facts(rel_src: str) -> dict:
    """The layout constants the representation relation actually spells."""
    arcd = const_body(rel_src, "SRC_ARCD")
    return {
        "receiver_offsets": {int(x) for x in re.findall(r"Nat\.add a ir_d(\d+)", arcd)},
        "child_offsets": {
            int(x) for x in re.findall(r"Nat\.add \(Nat\.succ b[12]?\) ir_d(\d+)", arcd)
        },
        "tags": {int(x) for x in re.findall(r"ir_var ir_d(\d+)", arcd)},
    }


def generator_child_offset(gen_src: str) -> int:
    m = re.search(r"def child_of\(b: str\) -> str:.*?ir_d(\d+)\)\"", gen_src, re.S)
    if not m:
        raise LayoutError(f"{GENERATOR}: could not read `child_of`'s byte offset")
    return int(m.group(1))


# ------------------------------------------------------------------- the gate


def check(root: Path) -> list:
    core = read(root, CORE)
    rel = relation_facts(read(root, RELATION))
    gen_off = generator_child_offset(read(root, GENERATOR))
    recomputed = arcinner_data_offset(read(root, SIDECAR))
    level = level_descriptor(json.loads(read(root, CENSUS)))
    prov = json.loads(read(root, PROV))
    geps = gep_offsets_by_function(core)
    notes = []

    # 1. The RECEIVER-relative field offsets, PER ARM. Not as a set: an offset
    #    the body geps on ONE variant's path must not vouch for a different
    #    variant's arm, and until 2026-09-13 it silently did.
    arms = relation_arms(read(root, RELATION))
    emitted_per_tag = receiver_offsets_per_tag(core, [t for t, _ in arms.values()])
    disagree = [
        f"`{name}` (tag {tag}) claims {sorted(claimed)} and the body geps "
        f"{sorted(emitted_per_tag[tag])} on that variant's path"
        for name, (tag, claimed) in arms.items()
        if claimed != emitted_per_tag[tag]
    ]
    if disagree:
        raise LayoutError(
            "FIELD OFFSETS DISAGREE, PER ARM: "
            + "; ".join(disagree)
            + ". A relation arm may only place a cell where the emitted body "
            "geps on THAT variant's own path. An offset that is merely true of "
            "Rust's layout, established nowhere in this artifact, is an "
            "unearned premise -- it makes the relation harder to inhabit and "
            "the theorem that consumes it correspondingly weaker."
        )
    notes.append(
        "receiver field offsets agree PER ARM: "
        + ", ".join(f"{name}{sorted(c)}" for name, (_, c) in arms.items())
    )

    # 2. The ArcInner data offset, FOUR ways: what <Arc<Level>>::deref geps by,
    #    what the producer's struct table implies, what the relation places the
    #    child Level at, and what the proof-term generator re-spells.
    emitted_arc = set().union(*[v for (f, _), v in geps.items() if f == 4]) if any(
        f == 4 for f, _ in geps
    ) else set()
    spellings = {
        "emitted gep in <Arc<Level>>::deref": emitted_arc,
        "recomputed from the producer's struct table": {recomputed},
        "EncodesLevelArcD's child placement": rel["child_offsets"],
        f"{GENERATOR}'s child_of()": {gen_off},
    }
    distinct = {frozenset(v) for v in spellings.values()}
    if len(distinct) != 1:
        raise LayoutError(
            "ARC DATA OFFSET DISAGREES across its spellings:\n  "
            + "\n  ".join(f"{k}: {sorted(v)}" for k, v in spellings.items())
            + "\nOne of them is wrong about the machine. The recomputation from the "
            "producer's own struct table is the one to trust."
        )
    notes.append(
        f"ArcInner data offset {recomputed}: emitted == recomputed == relation == generator"
    )

    # 3. Level's variant TAGS. The body switches on variant indices, so the
    #    relation's `ir_var k` must be the producer's own discriminants.
    if rel["tags"] != set(level["discriminants"]):
        raise LayoutError(
            f"VARIANT TAGS DISAGREE. The producer records Level's discriminants as "
            f"{level['discriminants']}, and the relation spells "
            f"{sorted(rel['tags'])}."
        )
    if len(level["discriminants"]) != level["variants"]:
        raise LayoutError(
            f"{CENSUS}: Level says variants={level['variants']} but lists "
            f"{len(level['discriminants'])} discriminants"
        )
    notes.append(f"Level's {level['variants']} tags {level['discriminants']}: producer == relation")

    # 4. The RECORDED REFUSAL must still describe the measured descriptor. This
    #    is what keeps `encodings_refused` honest: the reason no IREnc row exists
    #    for Level is four specific numbers, and if the descriptor ever moves,
    #    the recorded reason silently stops being the reason.
    refusals = " ".join(prov.get("encodings_refused", []))
    if "enum" not in refusals:
        raise LayoutError(f"{PROV}: no recorded encodings refusal to check")
    lo, hi = level["range"]
    required = {
        f"{level['variants']} variants": f"{level['variants']} variants",
        "the niche range": f"niche variants {lo}..{hi}",
        "the niche start": f"niche_start is {level['start']}",
        "the untagged variant": f"untagged={level['untagged']}",
    }
    missing = [k for k, v in required.items() if v not in refusals]
    if missing:
        raise LayoutError(
            "THE RECORDED REFUSAL NO LONGER DESCRIBES THE MEASURED DESCRIPTOR. "
            f"Level is {level['text']}, and the refusal in {PROV} does not state: "
            + ", ".join(missing)
            + ". A refusal that has drifted from its reason is worse than none."
        )
    notes.append("the recorded Level refusal still names the measured niche")

    # 5. The minted-vs-authored split the status page QUOTES, re-derived here
    #    and compared against the committed artifact. This check exists because
    #    the figure it guards was stale on the very commit that introduced it:
    #    "66 authored (46,977) -- minted is 67.8%" was measured mid-session and
    #    the session kept adding constants, so the number shipped describing a
    #    tree that had already moved (the truth at that commit was 71 authored,
    #    57,830 chars, 63.1%). Counting by hand and pasting the result into
    #    prose is exactly the class this repo refuses everywhere else, and a
    #    figure nobody re-derives is a figure that is wrong as soon as the next
    #    constant lands. Bound in the status page by a `claim: figure` marker,
    #    so check_doc_claims.py refuses the PROSE and this leg refuses the
    #    ARTIFACT -- neither can drift without the other going red.
    live = counts(root)
    try:
        pinned = json.loads(read(root, COUNTS_JSON))
    except FileNotFoundError as exc:
        raise LayoutError(f"{COUNTS_JSON} is missing: {exc}") from exc
    moved = [
        f"{k}: artifact says {pinned.get(k)!r}, the tree says {live[k]!r}"
        for k in ("minted_terms", "authored_terms", "minted_chars",
                  "authored_chars", "minted_pct", "headline")
        if pinned.get(k) != live[k]
    ]
    if moved:
        raise LayoutError(
            "THE PROOF-TEXT SPLIT HAS MOVED AND THE ARTIFACT HAS NOT. "
            + "; ".join(moved)
            + f". Re-mint with `python3 {Path(__file__).name} --emit-counts` and "
            "rewrite the sentence in docs/CRYSTAL_STATUS.md that quotes it -- "
            "check_doc_claims.py will refuse the prose until you do."
        )
    notes.append(
        f"proof-text split {live['minted_terms']} minted / "
        f"{live['authored_terms']} authored = {live['minted_pct']}%: "
        "artifact == tree"
    )
    # 6. The derived closure's control flow, against the recorded link-5
    #    diagnosis. Every CFG here is a DAG, so the executor's backedge refusals
    #    cannot be what stops this body -- what stops it is that `load`, `gep`,
    #    `call` and friends have no arm in the modeled fragment at all.
    shape = closure_shape(core)
    if shape["cyclic_cfgs"]:
        raise LayoutError(
            "A FUNCTION IN THE DERIVED CLOSURE NOW HAS A CYCLIC CFG: "
            f"{shape['cyclic_cfgs']}. The link-5 note in docs/CRYSTAL_STATUS.md "
            "says every body here is a DAG and that a backedge is therefore not "
            "what the proven-output gate refuses. That sentence is now false -- "
            "re-measure before editing either the note or this check."
        )
    if shape["self_recursive"] != [0]:
        raise LayoutError(
            "THE CALL-GRAPH CYCLE MOVED. The recorded reading is that function 0 "
            "(`level::Level::is_zero`) is the one self-recursive body and that its "
            "recursion is a CALL, not a branch; measured now, the self-recursive "
            f"set is {shape['self_recursive']}."
        )
    notes.append(
        f"derived closure: {len(shape['functions'])} functions, ZERO cyclic CFGs, "
        f"call graph {shape['call_graph']}, self-recursive {shape['self_recursive']}"
    )
    return notes


# ----------------------------------------------------------------- the counts


def counts(root: Path) -> dict:
    """Minted vs authored proof text — the figure the status page quotes."""
    gen = read(root, GENERATOR)
    minted = set(re.findall(r'^\s+"(SRC_[A-Z_0-9]+)":', gen, re.M))
    sizes = {}
    for f in SPEC_FILES:
        for name, body in re.findall(
            r'^const (SRC_[A-Z_0-9]+): &str = "(.*?)";$', read(root, f), re.S | re.M
        ):
            sizes[name] = len(body)
    m = {k: v for k, v in sizes.items() if k in minted}
    a = {k: v for k, v in sizes.items() if k not in minted}
    return {
        "minted_terms": len(m),
        "authored_terms": len(a),
        "minted_chars": sum(m.values()),
        "authored_chars": sum(a.values()),
        "minted_pct": round(100 * sum(m.values()) / max(1, sum(sizes.values())), 1),
        # The sentence the status page prints, commas and all. A `claim: figure`
        # marker checks that a rendered value APPEARS in the prose, so binding a
        # preformatted line binds the whole sentence; binding one derived number
        # binds almost nothing. Measured 2026-09-13: pruning four premises moved
        # minted_chars by 2,388 and authored_chars by 892 and left `minted_pct`
        # at 69.5 -- a marker on the percentage alone would have stayed green
        # across a change to every figure beside it.
        "headline": (
            f"{len(m)} minted constants = {sum(m.values()):,} characters, "
            f"{len(a)} authored = {sum(a.values()):,}"
        ),
        "largest_authored": sorted(((v, k) for k, v in a.items()), reverse=True)[:5],
    }


# --------------------------------------------------------------- the self-test


def self_test() -> int:
    """Mutate a throwaway copy of the tree and require this gate to refuse."""
    import shutil
    import tempfile

    arms = [
        (
            "the relation places a child at the wrong byte",
            RELATION,
            lambda s: s.replace("Nat.add a ir_d8", "Nat.add a ir_d9", 1),
        ),
        (
            "the generator re-spells the Arc offset differently",
            GENERATOR,
            lambda s: s.replace(
                'return f"(Nat.add (Nat.succ {b}) ir_d16)"',
                'return f"(Nat.add (Nat.succ {b}) ir_d24)"',
                1,
            ),
        ),
        (
            "a variant tag is dropped from the relation",
            RELATION,
            lambda s: s.replace("ir_var ir_d4", "ir_var ir_d5", 1),
        ),
        (
            "the recorded refusal stops naming the measured niche start",
            PROV,
            lambda s: s.replace("niche_start is 3", "niche_start is 7", 1),
        ),
        (
            "an arm claims an offset the body never geps on its own path",
            RELATION,
            lambda s: s.replace(
                "(IRScalar.ptr_ (Nat.succ b2)) Bool.true)) -> "
                "EncodesLevelArcD mem n (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) l1 -> "
                "EncodesLevelArcD mem n (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) l2 -> "
                "EncodesLevelArcD mem n (IRScalar.ptr_ a) (Level.imax l1 l2)",
                "(IRScalar.ptr_ (Nat.succ b2)) Bool.true)) -> "
                "Eq Bool (ir_nat_ltb (Nat.add a ir_d8) n) Bool.true -> "
                "EncodesLevelArcD mem n (IRScalar.ptr_ (Nat.add (Nat.succ b1) ir_d16)) l1 -> "
                "EncodesLevelArcD mem n (IRScalar.ptr_ (Nat.add (Nat.succ b2) ir_d16)) l2 -> "
                "EncodesLevelArcD mem n (IRScalar.ptr_ a) (Level.imax l1 l2)",
                1),
        ),
        (
            "a body in the derived closure acquires a backedge",
            CORE,
            lambda s: s.replace(
                "(node (results) (br 6 (args 5)))",
                "(node (results) (br 0 (args 5)))",
                1,
            ),
        ),
        (
            "the committed proof-text split stops matching the tree",
            COUNTS_JSON,
            lambda s: s.replace('"authored_terms"', '"authored_terms_WAS"', 1),
        ),
    ]
    failures = 0
    with tempfile.TemporaryDirectory() as td:
        sandbox = Path(td) / "tree"
        for rel in {CORE, PROV, RELATION, GENERATOR, SIDECAR, CENSUS, COUNTS_JSON, *SPEC_FILES}:
            dst = sandbox / rel
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / rel, dst)
        try:
            check(sandbox)
        except LayoutError as e:
            print(f"  self-test BASELINE FAILED (the unmutated tree must pass): {e}")
            return 1
        print("  self-test baseline ok: the committed tree passes")
        for name, rel, mutate in arms:
            p = sandbox / rel
            original = p.read_text()
            mutated = mutate(original)
            if mutated == original:
                print(f"  self-test ARM INERT: {name} — the mutation matched nothing")
                failures += 1
                continue
            p.write_text(mutated)
            try:
                check(sandbox)
            except LayoutError:
                print(f"  self-test ARM ok: {name} -> refused")
            else:
                print(f"  self-test ARM FAILED: {name} -> ACCEPTED")
                failures += 1
            p.write_text(original)
        # M2 (2026-09-27): the producer's struct table PRINTED BY trust-ir WS4.3 (every non-bare
        # symbol quoted) is the same table -- the gate must still pass on it; the
        # `struct @([^ ]+)` regex this replaced kept the quotes, found no ArcInner row and refused.
        # A module mixing the two spellings, and an escape no printer writes, are refused.
        side = sandbox / SIDECAR
        legacy = side.read_text()
        quoted = tir_symbols.respell_ws43(legacy)
        side.write_text(quoted)
        try:
            check(sandbox)
        except LayoutError as e:
            print(f"  self-test ARM FAILED: the WS4.3-printed struct table was refused: {e}")
            failures += 1
        else:
            if 'struct @"alloc::sync::ArcInner"' in quoted:
                print("  self-test ARM ok: the WS4.3-printed (quoted-symbol) struct table passes")
            else:
                print("  self-test ARM FAILED: the re-spelled table carries no quoted ArcInner row")
                failures += 1
        for name, text in (
                ("a module mixing a quoted and a raw symbol",
                 quoted.replace('struct @"alloc::sync::ArcInner"', "struct @alloc::sync::ArcInner<x y>", 1)),
                ("an escape the printer cannot write",
                 quoted.replace('@"alloc::sync::ArcInner"', '@"alloc::sync\\qArcInner"', 1))):
            side.write_text(text)
            try:
                check(sandbox)
            except LayoutError:
                print(f"  self-test ARM ok: {name} -> refused")
            else:
                print(f"  self-test ARM FAILED: {name} -> ACCEPTED")
                failures += 1
        side.write_text(legacy)
    print("self-test: all arms green" if not failures else f"self-test: {failures} FAILED")
    return 1 if failures else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--counts", action="store_true")
    ap.add_argument("--emit-counts", dest="emit_counts", action="store_true")
    ap.add_argument("--self-test", dest="selftest", action="store_true")
    ap.add_argument("--pinned-inputs", dest="pinned_inputs", action="store_true")
    a = ap.parse_args()
    if a.pinned_inputs:
        print("\n".join(tir_symbols.first_party_imports(Path(__file__))))
        return 0
    if a.selftest:
        return self_test()
    if a.emit_counts:
        c = counts(ROOT)
        c.pop("largest_authored", None)
        (ROOT / COUNTS_JSON).write_text(json.dumps(c, indent=2, sort_keys=True) + "\n")
        print(f"wrote {COUNTS_JSON}: {c['minted_terms']} minted / "
              f"{c['authored_terms']} authored = {c['minted_pct']}%")
        return 0
    if a.counts:
        c = counts(ROOT)
        print(
            f"ir_lzd proof text: {c['minted_terms']} minted constants "
            f"({c['minted_chars']:,} chars), {c['authored_terms']} authored "
            f"({c['authored_chars']:,}) — minted is {c['minted_pct']}%"
        )
        for v, k in c["largest_authored"]:
            print(f"    largest authored: {v:>7,}  {k}")
        return 0
    try:
        for n in check(ROOT):
            print(f"  ok  {n}")
    except LayoutError as e:
        print(f"LZD LAYOUT FACTS: REFUSED\n{e}")
        return 1
    print("lzd layout facts: every layout constant in the proof matches the artifact")
    return 0


if __name__ == "__main__":
    sys.exit(main())
