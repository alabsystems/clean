#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0

"""Crystal link 4, M0 work item W2: the STRATA census of infer_type's callee closure.

    python3 scripts/crystal_link4_strata.py --artifact-root DIR --report OUT.json   # measure (--report-full: uncapped)
    python3 scripts/crystal_link4_strata.py --artifact-root DIR --check             # the gate
    python3 scripts/crystal_link4_strata.py --artifact-root DIR --init   --reason TEXT
    python3 scripts/crystal_link4_strata.py --artifact-root DIR --rebase --reason TEXT
    python3 scripts/crystal_link4_strata.py --artifact-root DIR --reseat --reason TEXT
    python3 scripts/crystal_link4_strata.py --self-test
    python3 scripts/crystal_link4_strata.py --pinned-inputs

OFFLINE AND READ-ONLY. DIR holds one trust dump per ARM (`<DIR>/<arm dir>/callees/`, the callee
sidecar link 4 is stated over); `--arm NAME=PATH` overrides one arm's directory. The three arms
are the lane's M0 measurement set: `dp` (link 4's executability baseline artifact) and the M0
producer's `m0off` / `m0on` (memo §21, digests pinned in the baseline). Nothing here builds,
runs or writes an artifact; `--report` and the baseline writers are the only writes.

WHY THIS EXISTS. The adopted link-4 plan (vcgen route, decisions D15-D20) needs DENOMINATORS it
can trust, and three of them were hand measurements in a design transcript. This script DERIVES
them from the artifact on every run, through the lane's own reader (`crystal_link4_executability`
`parse_artifact`, `closure`, `find_targets`; `crystal_trust_ir_symbols` for every definition-site
symbol) -- never a second parser of the same dump -- and refuses to let the gated ones get worse.

WHAT IT MEASURES, per arm, over infer_type's call closure (the executability ratchet's closure):

 (1) DENOMINATORS. Bodies and instructions of the closure. On `dp` they MUST be 2,508 / 249,535
     (the plan's figures, `DP_ANCHOR`): a dp arm whose digests are the anchor's and whose closure
     is anything else is a REFUSAL (exit 2), and so is a dp arm that is not the anchored artifact.

 (2) CONFIGURATION STRATA, PROVED BY IR DOMINANCE, NEVER BY NAME. A configuration predicate is a
     test on the TAG of a CARRIER value, identified by its TYPE ROW in the artifact:
       PROF  the enum carried by TypeChecker's one field whose `Some` payload reaches (by value)
             `HeartbeatProfiler`; P-true tags = the `Some` discriminant.
       MODE  `clean_kernel::mode::CleanMode`; P-true tags = the variants E4's
             `lean_nodes_and_mode` names (Cubical, Directed), read off the enum row.
       NODE  the `ExprKind` native enum view; its tag is field 0, the variant order is READ
             (lexed) from `crates/clean-kernel/src/expr/kind.rs`, and the P-true tags are the
             variants E4 names (SProp, Squash, Cubical*, ZFC*).
     A branch is a P-test when its scrutinee is such a tag -- directly (`extractfield <int> X, 0`
     of a carrier-typed X, through copy/casts), through `icmp` against a constant, through a
     `select b, false, true` negation, or through a call to a small acyclic function whose
     SUMMARY (every entry-to-ret path, derived here) returns `[tag(*param) in S]`. A call site is
     GATED by P when one edge of a P-test, taken only if the tag is in P's excluded set, EDGE-
     DOMINATES the call's block in its function. The edge is HAVOC-dominated instead when the
     tag's subject derives from a `fresh_symbolic_havoc` undef -- an undef value, or a load
     through an address with an undef in it (`Expr::kind` today) -- because the IR then does not
     tie the branch to the input: HAVOC IS NOT A CUT. An UNDOMINATED edge is NOT A CUT. A
     stratum is what the closure loses when exactly the gated edges are removed, recomputed.
       * The heartbeat PROFILER stratum is reported as a C0 stratum, NEVER pruned (D17: the
         profiler is a deployed input under `profileHeartbeats`).
       * The cubical/ZFC stratum (MODE and NODE) is the only PRECONDITION CUT (E4's
         `lean_nodes_and_mode`); the PRUNED closure is the closure minus it.
     Every gating edge the name-seeded candidate sets propose (the 3 profiler edges; the
     cubical/ZFC entry edges) gets a VERDICT: dominated / entry_gated (its caller is reachable
     only through gated edges) / havoc / undominated, with the justifying branch. The seeds only
     choose which edges get a verdict row; no seed ever cuts anything.

 (3) FAMILY KEYS. A body's `shape` key abstracts callee ids, global ids and type ids to
     first-occurrence parameters; its `enc` key is the shape PLUS the canonical closure of every
     type row the body's type parameters reach (ids renumbered by breadth-first order, names in
     their legacy spelling, the `layout(..)` descriptor included). `ir_enc_matches` keys an
     encodings row on (kind, id) and the projector derives every row from exactly those type
     rows, so two instances whose encoding rows differ never share an `enc` key (a sound
     over-approximation: rows that differ in something the encodings ignore also split). The
     report gives the collapse ratio per arm (closure and pruned closure, both tiers) and the
     STABILITY of the partition across arms, bodies joined by `canonical_identity` name.

 (4) ASSERT CLASSIFICATION, PER SITE (D18). Every `assert` in the closure is keyed to the sited
     obligation at it (`site fN/bbM#K`, or the instruction defining its condition) and classed:
       genuine.panic_call    const-false, obligation "panic call `X` must be unreachable"
       genuine.check         computed condition keyed to an overflow / bounds / division /
                             conditional-panic obligation
       genuine.check_unsited computed condition whose slice holds a `#proof: no_overflow` or
                             `in_bounds` operation (a Rust overflow/bounds check with no site)
       trivial.true          const-true: never halts
       ub_halt               a sited undefined-behaviour halt (imaged as `unreachable`)
       stand_in.*            const-false and NOT a genuine panic: a drop-glue assumption, another
                             `[trust-*-assumption]`, or unkeyed and followed by `br`,
                             `unreachable`, a `fresh_symbolic_havoc` undef, or anything else
       unclassified.computed a computed condition with no key at all
     The whole-module SHAPE table the plan quotes (const-false asserts and the instruction after
     them) is re-derived too; on `dp` it must equal `DP_ANCHOR` or the run is refused.

 (5) LAYOUT MIXING (the D20 signal). EvalIR's memory is CELLS with single-scale GEP, so an `i8`
     or `u8` GEP by a non-zero or dynamic index steps CELLS, not bytes. A load/store's address is
     traced to a root (param, alloca, global, a loaded pointer, a pointer field, a call result)
     with the flags `byte` (a byte-scaled step) and `havoc`; through calls, arguments reach
     parameters and pointer returns reach call results (fixpoints). Two findings:
       sites    (M1) an AGGREGATE load/store whose address carries a byte step, locally or from
                a caller -- hashbrown's NEON group probe (`read_unaligned::<uint8x8_t>` reading a
                `core::ptr::Packed` over control bytes stored one `u8` at a time) is flagged
                `neon_group_probe` and listed first;
       objects  (M2) a root reached BOTH by an aggregate access at its base and by a byte-stepped
                access (itself or in a callee it is passed to), grouped by the aggregate type.
     Each is named with a call path from infer_type. Both are LOWER BOUNDS: an address that
     reaches a block parameter is rooted there (a pointer stepped round a loop keeps no flag),
     and a pointer stored to memory and loaded back starts a new root.

THE GATE (`--check`). Every gated metric is a BAD count per arm: `asserts.stand_in`,
`asserts.unclassified`, `cfg_cut.gating_edges_not_cut`, `layout_mixing.sites`,
`layout_mixing.objects`, `layout_mixing.roots`. Against the committed baseline
(`data/crystal_link4_strata_baseline.json`): any metric HIGHER -> exit 1; the same identity (arm
digests + script + source anchors) and any metric DIFFERENT -> exit 1 (a hand-edited baseline);
a baseline whose payload digest or last history entry disagrees with it -> exit 2. `--rebase`
lowers a baseline only over a CHANGED artifact with nothing worse; `--reseat` moves it over an
instrument change on the SAME artifacts, and is the only way to change the metric set.

FAIL-CLOSED (exit 2, never a zero): an arm missing or refused by the shared reader; a dp arm
that is not the anchor, or whose denominators or shape table differ from it; an annotation walk
that disagrees with the reader's instruction text; a type row read twice, or a carrier row that
is absent or ambiguous; an ExprKind variant list that cannot be read, or a switch on its tag
naming a case outside it; E4's precondition text no longer naming what the carriers encode; an
edge used in a cut that is not dominated; a baseline missing, malformed or edited.

Exit codes: 0 pass, 1 fail (regression / baseline better than its artifact / refused rebase),
2 refusal.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import sys
import tempfile
from collections import Counter, defaultdict, deque

if os.path.dirname(os.path.abspath(__file__)) not in sys.path:
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
# The lane's reader of the callee sidecar, and the ONE reader of definition-site symbols.
import crystal_link4_executability as ex  # noqa: E402
import crystal_trust_ir_symbols as tir_symbols  # noqa: E402

SCHEMA = "crystal-link4-strata/v1"
BASELINE_SCHEMA = "crystal-link4-strata-baseline/v1"
SCRIPTS_DIR = os.path.dirname(os.path.abspath(__file__))
REPO_ROOT = os.path.dirname(SCRIPTS_DIR)
# Read by check_gate_registry.py (PINNED_INPUTS_MARKER): `--pinned-inputs` prints the first-party
# modules this script executes besides itself, derived from its imports.
ANSWERS_PINNED_INPUTS = True
DEFAULT_BASELINE = os.path.join("data", "crystal_link4_strata_baseline.json")
DEFAULT_ARTIFACT_ROOT = os.path.join("target", "crystal-lane")
# The M0 measurement set. The m0 arms are immutable clonefile copies of the dumps memo §21 pins
# (the pipeline renames `dump-link-O3-m0*` on every pass); their digests live in the baseline.
ARMS = (("dp", "dump-link-O3-dp"),
        ("m0off", os.path.join("link4-strata-arms", "m0off")),
        ("m0on", os.path.join("link4-strata-arms", "m0on")))
ROOT_TARGET = "infer_type"

EXIT_PASS, EXIT_FAIL, EXIT_REFUSED = 0, 1, 2

# The plan's figures (plan §6 item 2, D18), anchored to the artifact they were measured on.
DP_ANCHOR = {
    "manifest_sha256": "ec7a86c7e46598c6f6748f3865b62b0b9a4276906d4d5d935243d326ba74789c",
    "text_sha256": "00f82b7fd277df6c177d3878c6e555339d3cc7b7360fab3f9cfa011bfc001ba1",
    "closure_bodies": 2508,
    "closure_instructions": 249535,
    # D18's whole-module shape table: const-false asserts and the instruction after each.
    "module_const_false_asserts": 2558,
    "module_const_false_next": {"br": 1345, "unreachable": 775, "havoc": 411},
}

# Source anchors: what the carrier predicates encode must still be what E4 says.
KIND_RS = "crates/clean-kernel/src/expr/kind.rs"
E4_INVENTORY = "data/crystal_e4_conversion_inventory.json"
E4_PRECONDITION = "lean_nodes_and_mode"
E4_ANCHORS = ("mode is not Cubical/Directed", "SProp / Squash / Cubical* / ZFC*")

TC_ROW = "clean_kernel::tc::TypeChecker"
MODE_ROW = "clean_kernel::mode::CleanMode"
MODE_EXCLUDED = ("Cubical", "Directed")
PROFILER_ROW = "clean_kernel::tc::heartbeat_profiler::profiler::HeartbeatProfiler"
OPTION_ROW = "core::option::Option"
NODE_VIEW_ROW = "__trust_native_enum_view::clean_kernel::expr::kind::ExprKind"
NODE_ENUM_ROW = "clean_kernel::expr::kind::ExprKind"
NODE_EXCLUDED_EXACT = ("SProp", "Squash")
NODE_EXCLUDED_PREFIX = ("Cubical", "ZFC")

# NAME SEEDS. They choose which edges get a verdict row and are reconciled against the design's
# figures; they never cut anything (the cut is the dominance-gated edge set).
PROFILER_SEED = re.compile(r"^clean_kernel::tc::heartbeat_profiler::")
PROFILER_SEED_CLOSURE = re.compile(r"closure@crates/clean-kernel/src/tc/heartbeat_profiler/")
CFG_SEED_FILES = ("reduction/kan", "reduction/cofib", "def_eq/cubical", "infer_cubical",
                  "reduction/directed", "infer_zfc")
CFG_SEED = re.compile(
    r"^clean_kernel::tc::(?:" + "|".join(f.replace("/", "::") for f in CFG_SEED_FILES) + r")::")
CFG_SEED_CLOSURE = re.compile(
    r"closure@crates/clean-kernel/src/tc/(?:" + "|".join(CFG_SEED_FILES) + r")\.rs")
# The design transcript's figures (narrow-then-widen), for reconciliation only.
DESIGN_PROFILER = {"edges": 3, "bodies": 304, "instructions": 56449}
DESIGN_CFG = {"edges": 40, "bodies": 484, "instructions": 52035, "remaining_bodies": 1720,
              "remaining_shapes": 1177}

AGG_PREFIXES = ("struct.", "enum.", "closure.", "(", "[")
BYTE_ELEMS = ("i8", "u8")
NEON_GROUP_PAYLOAD = "core::core_arch::arm_shared::neon::uint8x8_t"
PACKED_ROW = "core::ptr::Packed"


class Refusal(Exception):
    """Fail-closed: an input this script cannot fully account for (exit 2)."""


# ---------------------------------------------------------------------------
# Reading one arm: the shared reader, then three side channels it does not keep.
# ---------------------------------------------------------------------------
_ROW_ID = re.compile(r"\s+id=(\d+)$")
_TYPE_ROW = re.compile(r"^type ty\.(\d+) = (.*)$")
_CLOSURE_ROW = re.compile(r"^closure_ty functy\.(\d+) (.*)$")
_SITE = re.compile(r" site f(\d+)/bb(\d+)#(\d+)\s*$")
_OBL_HEAD = re.compile(r'^obligation \d+ (\S+) (\S+) "')
_SOURCE_ID = re.compile(r'\\"source_id\\":\\"([a-z\-]+):')


def _sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def annotate(mod, lines):
    """Attach each instruction's trailing `; #...` comment (`ann`) -- the reader strips it -- by
    walking the text beside the reader's parse. The walk must see EXACTLY the reader's
    instruction text, instruction for instruction, or the run is refused."""
    for k, f in enumerate(mod["funcs"]):
        if f.get("decl"):
            continue
        i = f["line"]  # the header's 1-based line number is the 0-based index of its first body line
        bi, ii = -1, 0
        while True:
            if i >= len(lines):
                raise Refusal(f"annotation walk: function #{k} runs past the text")
            s = lines[i]
            if s == "}":
                break
            if ex.BLOCK_RE.match(s):
                bi, ii = bi + 1, 0
                i += 1
                continue
            st = s.strip()
            if st.startswith(";") or not st:
                i += 1
                continue
            try:
                inst = f["blocks"][bi]["insts"][ii]
            except (IndexError, KeyError):
                raise Refusal(f"annotation walk: function #{k} has more instructions in the text "
                              f"than the reader parsed (line {i + 1})") from None
            if ex._strip_comment(st) != inst["text"]:
                raise Refusal(f"annotation walk: function #{k} line {i + 1} is {st[:60]!r}, the "
                              f"reader parsed {inst['text'][:60]!r}")
            q = st.rfind('"')
            c = st.find("  ;", q + 1 if q >= 0 else 0)
            inst["ann"] = st[c + 3:].strip() if c >= 0 else ""
            ii += 1
            i += 1
        n_text = sum(len(b["insts"]) for b in f["blocks"])
        if bi + 1 != len(f["blocks"]) or (f["blocks"] and ii != len(f["blocks"][-1]["insts"])) \
                or any("ann" not in x for b in f["blocks"] for x in b["insts"]):
            raise Refusal(f"annotation walk: function #{k} ({n_text} instructions) was not "
                          f"covered block for block")


def read_rows(lines):
    """Every type-table row: {(cls, id): (name or None, row text in LEGACY spelling, id-less)}."""
    syms = tir_symbols.ModuleSymbols(ex.FN_PREFIX)
    rows = {}

    def put(key, name, text):
        if key in rows:
            raise Refusal(f"type-table row {key[0]}.{key[1]} is defined twice")
        rows[key] = (name, text)

    for ln_no, ln in enumerate(lines, 1):
        if ln.startswith(("    ", "bb", "fn ", "}", ";", "obligation ")):
            continue
        try:
            tr = syms.type_row(ln, f"line {ln_no}")
        except tir_symbols.SymbolRefusal as exc:
            raise Refusal(f"line {ln_no}: {exc}") from exc
        if tr is not None and tr[0] in ("struct", "enum", "record"):
            legacy = tir_symbols.legacy_spelling(ln, tr[2], tr[3], tr[1])
            m = _ROW_ID.search(legacy)
            if not m:
                raise Refusal(f"line {ln_no}: a {tr[0]} row with no id=")
            put((tr[0], int(m.group(1))), tr[1], legacy[:m.start()])
            continue
        m = _TYPE_ROW.match(ln)
        if m:
            put(("ty", int(m.group(1))), None, m.group(2))
            continue
        try:
            gr = syms.global_row(ln, f"line {ln_no}")
        except tir_symbols.SymbolRefusal as exc:
            raise Refusal(f"line {ln_no}: {exc}") from exc
        if gr is not None:
            # A global's own NAME is an id: its canonical row is its type and initializer.
            n = sum(1 for key in rows if key[0] == "global")
            put(("global", n), gr[0], ln[:ln.index("@")] + ln[gr[2]:])
            continue
        m = _CLOSURE_ROW.match(ln)
        if m:
            # `closure.N` names the N-th `closure_ty` row (rows are keyed by the closure's
            # functy, which two closures of one signature share).
            n = sum(1 for key in rows if key[0] == "closure")
            put(("closure", n), None, f"functy.{m.group(1)} {m.group(2)}")
    return rows


def _obligation_class(kind, src, desc):
    if desc.startswith("[trust-"):
        m = re.match(r"\[(trust-[a-z\-]+)\]", desc)
        tag = m.group(1) if m else "trust-?"
        return {"trust-drop-glue-assumption": "assume.drop_glue",
                "trust-absent-callee-assumption": "assume.absent_callee"}.get(tag, "assume." + tag)
    if ex.UB_HALT_WORDING in desc:
        return "ub_halt"
    if desc.startswith("panic call"):
        return "panic_call"
    if kind == "bounds_check":
        return "check.bounds"
    if kind == "arithmetic_safety":
        return "check.arith"
    if src == "mir-conditional-panic":
        return "check.conditional_panic"
    return "other:" + kind


def _quoted_at(s, i):
    """The body of the double-quoted string starting at s[i] (escapes kept), by a linear scan:
    a backtracking regex over a long obligation line cost gigabytes."""
    if s[i:i + 1] != '"':
        raise Refusal(f"no quoted string at column {i} of {s[:80]!r}")
    j = i + 1
    while j < len(s) and s[j] != '"':
        j += 2 if s[j] == "\\" else 1
    if j >= len(s):
        raise Refusal(f"unterminated quoted string in {s[:80]!r}")
    return s[i + 1:j]


def read_obligations(lines):
    """{(func, block label, index): [obligation class, ...]} for every SITED obligation, and the
    per-class count of the unsited ones (function-level `all assertions hold` rows are skipped)."""
    sited = defaultdict(list)
    unsited = Counter()
    for ln in lines:
        if not ln.startswith("obligation "):
            continue
        h = _OBL_HEAD.match(ln)
        if not h:
            raise Refusal(f"unparsed obligation line {ln[:100]!r}")
        desc = _quoted_at(ln, h.end() - 1)
        src = _SOURCE_ID.search(ln)
        cls = _obligation_class(h.group(1), src.group(1) if src else None, desc)
        m = _SITE.search(ln)
        if m:
            sited[(int(m.group(1)), "bb" + m.group(2), int(m.group(3)))].append(cls)
        elif desc.endswith(": all assertions hold"):
            continue
        else:
            unsited[cls] += 1
    return sited, unsited


class Arm:
    """One measured artifact."""

    def __init__(self, name, directory):
        self.name = name
        self.dir = directory
        cdir = os.path.join(directory, "callees")
        tpath = os.path.join(cdir, f"{ex.CRATE}.callees.trust-ir.txt")
        mpath = os.path.join(cdir, f"{ex.CRATE}.callees.manifest.json")
        try:
            self.mod = ex.parse_artifact(directory)
        except ex.Refusal as exc:
            raise Refusal(f"arm {name}: the shared reader refused {directory}: {exc}") from exc
        self.funcs = self.mod["funcs"]
        lines = open(tpath, encoding="utf-8").read()[:-1].split("\n")
        annotate(self.mod, lines)
        self.rows = read_rows(lines)
        self.obl, self.unsited_obl = read_obligations(lines)
        self.identity = {"manifest_sha256": _sha256(mpath), "text_sha256": _sha256(tpath)}
        if self.identity["manifest_sha256"] != self.mod["manifest_sha256"] \
                or self.identity["text_sha256"] != self.mod["text_sha256"]:
            raise Refusal(f"arm {name}: the files changed while they were read")
        try:
            self.targets = ex.find_targets(self.funcs)
        except ex.Refusal as exc:
            raise Refusal(f"arm {name}: {exc}") from exc
        self.root = self.targets[ROOT_TARGET]
        self.by_row_name = defaultdict(list)
        for key, (nm, _t) in self.rows.items():
            if nm is not None:
                self.by_row_name[nm].append(key)
        self._succ = None

    # -- the call graph (the reader's closure rule: calls and by-value dispatch, bodies only) --
    def edges_of(self, k):
        out = []
        for b in self.funcs[k]["blocks"]:
            for j, i in enumerate(b["insts"]):
                if i["mnem"] == "call":
                    cs = [i["callee"]]
                else:
                    cs = list(i.get("by_value_targets") or ())
                for c in cs:
                    if not self.funcs[c].get("decl"):
                        out.append((k, b["label"], j, c))
        return out

    def succ(self, k):
        if self._succ is None:
            self._succ = {}
        if k not in self._succ:
            self._succ[k] = self.edges_of(k)
        return self._succ[k]

    def reach(self, root=None, cut=frozenset()):
        root = self.root if root is None else root
        seen = {root}
        stack = [root]
        while stack:
            k = stack.pop()
            for e in self.succ(k):
                if e in cut:
                    continue
                if e[3] not in seen:
                    seen.add(e[3])
                    stack.append(e[3])
        return seen

    def view(self, k):
        cache = self.__dict__.setdefault("_views", {})
        if k not in cache:
            cache[k] = FuncView(self, k)
        return cache[k]

    def ninst(self, bodies):
        return sum(len(b["insts"]) for k in bodies for b in self.funcs[k]["blocks"])

    def row_key(self, name, cls=None):
        keys = [k for k in self.by_row_name.get(name, []) if cls is None or k[0] == cls]
        if len(keys) != 1:
            raise Refusal(f"arm {self.name}: {len(keys)} type rows named {name!r} (need exactly one)")
        return keys[0]


# ---------------------------------------------------------------------------
# Source anchors: the ExprKind variant order (lexed Rust) and E4's precondition text.
# ---------------------------------------------------------------------------
def _split_top(s, sep=","):
    """Split at depth-0 separators; brackets and string literals are respected."""
    out, depth, cur, i = [], 0, [], 0
    while i < len(s):
        c = s[i]
        if c == '"':
            j = i + 1
            while j < len(s) and s[j] != '"':
                j += 2 if s[j] == "\\" else 1
            cur.append(s[i:j + 1])
            i = j + 1
            continue
        if c in "([{<":
            depth += 1
        elif c in ")]}>":
            depth -= 1
        if c == sep and depth == 0:
            out.append("".join(cur))
            cur = []
        else:
            cur.append(c)
        i += 1
    if "".join(cur).strip():
        out.append("".join(cur))
    return out


def expr_kind_variants(src):
    """The variants of `pub enum ExprKind`, in declaration order, from the comment-blanked source.
    A variant carrying any attribute but `serde`/`doc` (a `cfg` would move the discriminants) or
    an explicit discriminant is a refusal: the order would not be the tag."""
    _blank_comments = ex._lexer()
    code = _blank_comments(src)
    m = re.search(r"\bpub enum ExprKind\s*\{", code)
    if not m:
        raise Refusal(f"{KIND_RS}: no `pub enum ExprKind {{`")
    depth, j = 1, m.end()
    while j < len(code) and depth:
        if code[j] == '"':
            j += 1
            while j < len(code) and code[j] != '"':
                j += 2 if code[j] == "\\" else 1
        elif code[j] == "{":
            depth += 1
        elif code[j] == "}":
            depth -= 1
        j += 1
    body = code[m.end():j - 1]
    names = []
    for item in _split_top(body):
        t = item.strip()
        while t.startswith("#["):
            k, d = 2, 1
            while k < len(t) and d:
                d += {"[": 1, "]": -1}.get(t[k], 0)
                k += 1
            attr = t[2:k - 1].strip()
            if not (attr.startswith("serde") or attr.startswith("doc")):
                raise Refusal(f"{KIND_RS}: ExprKind variant attribute #[{attr[:40]}] could move "
                              f"the discriminants")
            t = t[k:].strip()
        vm = re.match(r"([A-Z][A-Za-z0-9_]*)\s*(?:$|\(|\{)", t)
        if not vm or re.search(r"\}\s*=|\)\s*=|^[A-Za-z0-9_]+\s*=", t):
            raise Refusal(f"{KIND_RS}: unparsed ExprKind variant {t[:60]!r}")
        names.append(vm.group(1))
    if len(names) < 20 or len(set(names)) != len(names):
        raise Refusal(f"{KIND_RS}: ExprKind reads as {len(names)} variants: not the enum")
    return names


def check_e4_anchor(repo_root):
    p = os.path.join(repo_root, E4_INVENTORY)
    try:
        inv = json.load(open(p))
        stmt = inv["exclusion_preconditions"][E4_PRECONDITION]["statement"]
    except (OSError, ValueError, KeyError, TypeError) as exc:
        raise Refusal(f"{E4_INVENTORY}: no {E4_PRECONDITION} statement ({exc})") from exc
    for a in E4_ANCHORS:
        if a not in stmt:
            raise Refusal(f"{E4_INVENTORY} {E4_PRECONDITION} no longer says {a!r}: the carrier "
                          f"predicates encode a precondition E4 no longer states")
    return stmt


def read_sources(repo_root):
    kp = os.path.join(repo_root, KIND_RS)
    try:
        ksrc = open(kp, encoding="utf-8").read()
    except OSError as exc:
        raise Refusal(f"missing {KIND_RS}: {exc}") from exc
    variants = expr_kind_variants(ksrc)
    stmt = check_e4_anchor(repo_root)
    digest = hashlib.sha256(json.dumps({"variants": variants, "e4": stmt}).encode()).hexdigest()
    return {"expr_kind_variants": variants, "e4_statement": stmt, "digest": digest}


# ---------------------------------------------------------------------------
# Carriers: the configuration predicates' subjects, identified by TYPE ROW.
# ---------------------------------------------------------------------------
_ENUM_VARIANT = re.compile(r"^\s*(\"(?:[^\"\\]|\\.)*\"|[A-Za-z0-9_.$]+)\s*(?:\((.*)\)|\{(.*)\})?\s*=\s*(-?\d+)\s*$")
_FIELD = re.compile(r"^\s*(?:(?:\"(?:[^\"\\]|\\.)*\"|[A-Za-z0-9_.$]+):\s+)?(.+?)(?:\s+@(\d+))?\s*$")


def _braced(text):
    a = text.find("{")
    if a < 0:
        return ""
    depth, j = 0, a
    while j < len(text):
        depth += {"{": 1, "}": -1}.get(text[j], 0)
        if depth == 0:
            return text[a + 1:j]
        j += 1
    raise Refusal(f"unbalanced type row {text[:80]!r}")


def struct_fields(arm, key):
    """[(type text, offset or None)] of a struct row, in field order."""
    _nm, text = arm.rows[key]
    out = []
    for item in _split_top(_braced(text)):
        m = _FIELD.match(item)
        if not m:
            raise Refusal(f"arm {arm.name}: unparsed field {item!r} of {key[0]}.{key[1]}")
        out.append((m.group(1).strip(), int(m.group(2)) if m.group(2) else None))
    return out


def enum_variants(arm, key):
    """[(variant name, discriminant, [payload type texts])] of an enum row."""
    _nm, text = arm.rows[key]
    out = []
    for item in _split_top(_braced(text)):
        m = _ENUM_VARIANT.match(item)
        if not m:
            raise Refusal(f"arm {arm.name}: unparsed variant {item!r} of enum.{key[1]}")
        name = m.group(1).strip('"')
        payload = m.group(2) if m.group(2) is not None else (m.group(3) or "")
        tys = [(_FIELD.match(p).group(1).strip()) for p in _split_top(payload)] if payload.strip() else []
        out.append((name, int(m.group(4)), tys))
    return out


_TOKEN_KEY = re.compile(r"\b(struct|enum|record|ty|closure)\.(\d+)\b")


def _tok_key(s):
    m = re.fullmatch(r"(struct|enum|record|ty|closure)\.(\d+)", s.strip())
    return (m.group(1), int(m.group(2))) if m else None


def reaches_by_value(arm, key, target, seen=None):
    """Does the value of row `key` CONTAIN (by value: struct fields, enum payloads, ty aliases,
    arrays and tuples -- never through a pointer) a value of row `target`?"""
    seen = set() if seen is None else seen
    if key == target:
        return True
    if key in seen or key not in arm.rows:
        return False
    seen.add(key)
    _nm, text = arm.rows[key]
    if key[0] == "ty":
        inner = [text]
    elif key[0] == "enum":
        inner = [t for _n, _d, tys in enum_variants(arm, key) for t in tys]
    elif key[0] in ("struct", "record"):
        inner = [t for t, _o in struct_fields(arm, key)]
    else:
        return False
    for t in inner:
        for m in _TOKEN_KEY.finditer(t.replace("fatptr<", "\0").split("\0")[0]):
            if reaches_by_value(arm, (m.group(1), int(m.group(2))), target, seen):
                return True
    return False


def derive_carriers(arm, sources):
    """{carrier: {"key": (cls, id), "universe": {tag: variant}, "excluded": set}} plus the TC row
    and where CleanMode is carried (the reading of E4's precondition is printed from it)."""
    tc = arm.row_key(TC_ROW, "struct")
    mode_key = arm.row_key(MODE_ROW, "enum")
    mode_vars = enum_variants(arm, mode_key)
    mode_excl = {d for n, d, _t in mode_vars if n in MODE_EXCLUDED}
    if {n for n, _d, _t in mode_vars if n in MODE_EXCLUDED} != set(MODE_EXCLUDED):
        raise Refusal(f"arm {arm.name}: CleanMode has no {MODE_EXCLUDED} variants")
    # The profiler's row and its opaque `datatype::` twin (a producer prints both spellings).
    prof_rows = [k for k, (nm, _t) in arm.rows.items()
                 if nm in (PROFILER_ROW, "datatype::" + PROFILER_ROW)]
    if not prof_rows:
        raise Refusal(f"arm {arm.name}: no type row named {PROFILER_ROW!r}")
    prof_fields = []
    for idx, (t, off) in enumerate(struct_fields(arm, tc)):
        k = _tok_key(t)
        if k and k[0] == "enum" and arm.rows.get(k, (None,))[0] == OPTION_ROW:
            some = [v for v in enum_variants(arm, k) if v[0] == "Some"]
            if some and any(reaches_by_value(arm, _tok_key(p), r)
                            for p in some[0][2] if _tok_key(p) for r in prof_rows):
                prof_fields.append((idx, k, some[0][1], off))
    if len(prof_fields) != 1:
        raise Refusal(f"arm {arm.name}: {len(prof_fields)} TypeChecker fields carry an "
                      f"Option<..HeartbeatProfiler..> (need exactly one)")
    pidx, pkey, psome, poff = prof_fields[0]
    # The ExprKind tag view: the legacy printer's `__trust_native_enum_view::..` struct, or the
    # M0 printer's struct of the enum's own name whose first field is its `__tag`.
    views = [k for k, (nm, text) in arm.rows.items() if k[0] == "struct" and (
        nm == NODE_VIEW_ROW or (nm == NODE_ENUM_ROW and _braced(text).lstrip().startswith("__tag:")))]
    if len(views) != 1:
        raise Refusal(f"arm {arm.name}: {len(views)} ExprKind tag-view rows (need exactly one)")
    view = views[0]
    variants = sources["expr_kind_variants"]
    node_excl = {i for i, n in enumerate(variants)
                 if n in NODE_EXCLUDED_EXACT or n.startswith(NODE_EXCLUDED_PREFIX)}
    mode_holders = sorted(arm.rows[k][0] or f"{k[0]}.{k[1]}" for k in arm.rows
                          if k[0] in ("struct", "record") and any(
                              _tok_key(t) == mode_key for t, _o in struct_fields(arm, k)))
    return {
        "PROF": {"key": pkey, "universe": {d: n for n, d, _t in enum_variants(arm, pkey)},
                 "excluded": {psome}, "tc_field": pidx, "tc_offset": poff},
        "MODE": {"key": mode_key, "universe": {d: n for n, d, _t in mode_vars},
                 "excluded": mode_excl},
        "NODE": {"key": view, "universe": dict(enumerate(variants)), "excluded": node_excl},
        "_tc": tc,
        "_mode_holders": mode_holders,
    }


# ---------------------------------------------------------------------------
# Per-function value analysis: definitions, types, tags, boolean tests, havoc provenance.
# ---------------------------------------------------------------------------
_EXTRACT = re.compile(r"^%\d+ = extractfield (.+) %(\d+), (\d+)$")
_LOAD = re.compile(r"^%\d+ = (?:volatile )?load (.+), ptr %(\d+)(?:, align \d+)?$")
_GEP = re.compile(r"^%\d+ = gep (?:inbounds )?(.+), ptr %(\d+)((?:, %\d+)*)$")
_ICMP = re.compile(r"^%\d+ = icmp ([a-z]+) (.+) %(\d+), %(\d+)$")
_SELECT = re.compile(r"^%\d+ = select (.+) %(\d+), %(\d+), %(\d+)$")
_INT_TY = re.compile(r"^(?:[iu](?:8|16|32|64|128)|[iu]size|bool)$")
TAG_CASTS = ("copy", "bitcast", "zext", "sext", "trunc")
PTR_PASS = ("borrow", "borrow_mut", "copy", "bitcast", "ptrtoptr")


class FuncView:
    """Lazy per-function facts."""

    def __init__(self, arm, k):
        self.arm, self.k = arm, k
        self.f = arm.funcs[k]
        self.defs = {}
        self.block_of = {}
        for bi, b in enumerate(self.f["blocks"]):
            for p in b["params"]:
                self.defs[p] = ("param", bi)
            for j, i in enumerate(b["insts"]):
                for r in i["res"]:
                    self.defs[r] = ("inst", bi, j, i)
        self.labels = [b["label"] for b in self.f["blocks"]]
        self.entry_params = self.f["blocks"][0]["params"] if self.f["blocks"] else []
        self._dom = None

    def inst(self, v):
        d = self.defs.get(v)
        return d[3] if d and d[0] == "inst" else None

    def const_int(self, v):
        i = self.inst(v)
        if i is not None and i["mnem"] == "const":
            try:
                return int(i["const_value"])
            except ValueError:
                return None
        return None

    def const_bool(self, v):
        i = self.inst(v)
        if i is not None and i["mnem"] == "const" and i["const_ty"] == "bool":
            return i["const_value"] == "true"
        if i is not None and i["mnem"] == "copy" and i["ty"] == "bool":
            return self.const_bool(i["roles"]["operand"])
        return None

    def vtype(self, v):
        i = self.inst(v)
        if i is None:
            return None
        m = i["mnem"]
        if m == "load":
            lm = _LOAD.match(i["text"])
            return lm.group(1) if lm else None
        if m == "extractfield":
            em = _EXTRACT.match(i["text"])
            return em.group(1) if em else None
        if m in ("undef", "copy", "insertfield"):
            return i.get("ty")
        if m == "const":
            return i.get("const_ty")
        return None

    # -- havoc provenance: does a value or an address derive from an undef? --
    def origins(self, v):
        """(undef?, entry params): what `v` derives from, through the value and ADDRESS chains
        (gep base and indices, pointer passes, loads, field reads, calls by their summaries). A
        block parameter derives from EVERY incoming argument: a may-analysis, so a value is
        havoc when any path could make it one -- the direction that never proves a false cut.
        Computed for the whole function as a LEAST FIXPOINT (both components only grow), so a
        value on a loop is never frozen before an undef reaches it round the back edge."""
        tab = self.__dict__.get("_orig")
        if tab is None:
            tab = self._origins_table()
            self._orig = tab
        return tab.get(v, (False, frozenset()))

    def _origins_table(self):
        incoming = defaultdict(list)
        for b in self.f["blocks"]:
            for t, args in b["insts"][-1].get("succ", ()):
                incoming[t].append(args)
        tab = {v: (False, frozenset()) for v in self.defs}

        def step(v, d):
            und, ps = False, set()

            def add(x):
                nonlocal und
                u, q = tab.get(x, (False, frozenset()))
                und = und or u
                ps.update(q)

            if d[0] == "param":
                if d[1] == 0:
                    ps.add(self.entry_params.index(v))
                else:
                    pos = self.f["blocks"][d[1]]["params"].index(v)
                    for args in incoming.get(self.labels[d[1]], ()):
                        if pos < len(args):
                            add(args[pos])
                return und, frozenset(ps)
            i = d[3]
            m = i["mnem"]
            if m == "undef":
                und = True
            elif m == "gep":
                add(i["roles"]["base"])
                for x in i["gep_indices"]:
                    add(x)
            elif m in PTR_PASS:
                add(i["roles"]["ptr" if m in ("borrow", "borrow_mut") else "operand"])
            elif m == "load":
                add(i["roles"]["ptr"])
            elif m == "extractfield":
                add(self._extract_source(i))
            elif m == "call":
                c = i["callee"]
                und = und or self.arm.ret_undef.get(c, False)
                for p in self.arm.ret_params.get(c, ()):
                    if p < len(i["roles"]["args"]):
                        add(i["roles"]["args"][p])
            elif m in ("ptr_data", "ptr_metadata"):
                add(i["roles"]["ptr"])
            elif m == "ptr_from_parts":
                add(i["roles"]["data"])
            elif i["kind"] == "Cast":
                add(i["roles"]["operand"])
            return und, frozenset(ps)

        changed = True
        while changed:
            changed = False
            for v, d in self.defs.items():
                new = step(v, d)
                if new != tab[v]:
                    tab[v] = new
                    changed = True
        return tab

    def _extract_source(self, i):
        """The value an `extractfield` reads: through an insertfield chain, the inserted field
        when the index matches (the producer's `undef T; insertfield ..` aggregate idiom is not a
        havoc at a field it wrote), else the aggregate the chain started from."""
        em = _EXTRACT.match(i["text"])
        idx = int(em.group(3)) if em else None
        agg = i["roles"]["aggregate"]
        for _ in range(64):
            d = self.inst(agg)
            if d is None or d["mnem"] != "insertfield":
                break
            im = ex._insertfield_parts(d["text"])
            if im and im[3] == idx:
                return im[4]
            agg = d["roles"]["aggregate"]
        return agg

    def havoc(self, v):
        return self.origins(v)[0]

    # -- tags --
    def tag(self, v, carriers):
        """(carrier, subject havoc?) when v is the tag of a carrier-typed value."""
        for _ in range(16):
            i = self.inst(v)
            if i is None:
                return None
            if i["mnem"] in TAG_CASTS and "operand" in i["roles"]:
                v = i["roles"]["operand"]
                continue
            break
        i = self.inst(v)
        if i is None or i["mnem"] != "extractfield":
            return None
        em = _EXTRACT.match(i["text"])
        if not em or em.group(3) != "0" or not _INT_TY.match(em.group(1)):
            return None
        x = int(em.group(2))
        xt = self.vtype(x)
        ck = _tok_key(xt) if xt else None
        for name, c in carriers.items():
            if name.startswith("_") or ck != c["key"]:
                continue
            return name, self.havoc(x)
        return None

    def bool_test(self, v, carriers, depth=0):
        """(carrier, S, havoc): v is true exactly when the carrier's tag is in S."""
        if depth > 12:
            return None
        i = self.inst(v)
        if i is None:
            return None
        m = i["mnem"]
        if m == "copy" and i.get("ty") == "bool":
            return self.bool_test(i["roles"]["operand"], carriers, depth + 1)
        if m == "icmp":
            im = _ICMP.match(i["text"])
            if not im:
                return None
            a, b = int(im.group(3)), int(im.group(4))
            for x, y, flip in ((a, b, False), (b, a, True)):
                t = self.tag(x, carriers)
                c = self.const_int(y)
                if t and c is not None:
                    uni = carriers[t[0]]["universe"]
                    op = im.group(1)
                    if flip:
                        op = {"ult": "ugt", "ugt": "ult", "ule": "uge", "uge": "ule",
                              "slt": "sgt", "sgt": "slt", "sle": "sge", "sge": "sle"}.get(op, op)
                    rel = {"eq": lambda z: z == c, "ne": lambda z: z != c,
                           "ult": lambda z: z < c, "slt": lambda z: z < c,
                           "ule": lambda z: z <= c, "sle": lambda z: z <= c,
                           "ugt": lambda z: z > c, "sgt": lambda z: z > c,
                           "uge": lambda z: z >= c, "sge": lambda z: z >= c}.get(op)
                    if rel is None:
                        return None
                    return t[0], frozenset(z for z in uni if rel(z)), t[1]
            return None
        if m == "select":
            sm = _SELECT.match(i["text"])
            if not sm or sm.group(1) != "bool":
                return None
            cnd, th, el = int(sm.group(2)), int(sm.group(3)), int(sm.group(4))
            tb, eb = self.const_bool(th), self.const_bool(el)
            inner = self.bool_test(cnd, carriers, depth + 1)
            if inner is None:
                return None
            uni = frozenset(carriers[inner[0]]["universe"])
            if tb is False and eb is True:
                return inner[0], uni - inner[1], inner[2]
            if tb is True and eb is False:
                return inner
            return None
        if m == "not" or (i["kind"] == "BinOp" and i["sub"] == "Xor"):
            if m == "not":
                inner = self.bool_test(i["roles"]["operand"], carriers, depth + 1)
            else:
                l, r = i["roles"]["lhs"], i["roles"]["rhs"]
                if self.const_bool(r) is True:
                    inner = self.bool_test(l, carriers, depth + 1)
                elif self.const_bool(l) is True:
                    inner = self.bool_test(r, carriers, depth + 1)
                else:
                    return None
            if inner is None:
                return None
            return inner[0], frozenset(carriers[inner[0]]["universe"]) - inner[1], inner[2]
        if m == "call":
            s = self.arm.pred_summary.get(i["callee"])
            if s is None:
                return None
            p, car, S = s
            args = i["roles"]["args"]
            if p >= len(args):
                return None
            return car, S, self.havoc(args[p])
        return None

    # -- dominance --
    def dominators(self):
        if self._dom is not None:
            return self._dom
        blocks = self.f["blocks"]
        succ = {b["label"]: [t for t, _a in b["insts"][-1].get("succ", ())] for b in blocks}
        preds = {b["label"]: [] for b in blocks}
        for lbl, ss in succ.items():
            for s in ss:
                preds[s].append(lbl)
        entry = blocks[0]["label"]
        order, seen, stack = [], {entry}, [(entry, iter(succ[entry]))]
        while stack:
            n, it = stack[-1]
            nxt = next(it, None)
            if nxt is None:
                order.append(n)
                stack.pop()
            elif nxt not in seen:
                seen.add(nxt)
                stack.append((nxt, iter(succ[nxt])))
        rpo = order[::-1]
        pos = {lbl: i for i, lbl in enumerate(rpo)}
        idom = {entry: entry}

        def meet(a, b):
            while a != b:
                while pos[a] > pos[b]:
                    a = idom[a]
                while pos[b] > pos[a]:
                    b = idom[b]
            return a

        changed = True
        while changed:
            changed = False
            for n in rpo[1:]:
                ps = [p for p in preds[n] if p in idom]
                if not ps:
                    continue
                new = ps[0]
                for p in ps[1:]:
                    new = meet(p, new)
                if idom.get(n) != new:
                    idom[n] = new
                    changed = True
        self._dom = (idom, preds, succ, entry)
        return self._dom

    def dominates(self, a, b):
        idom, _p, _s, entry = self.dominators()
        if b not in idom or a not in idom:
            return False
        while True:
            if b == a:
                return True
            if b == entry:
                return False
            b = idom[b]

    def edge_dominates(self, d, s, b):
        """The CFG edge d->s dominates block b: s dominates b, and s is entered only from d
        (or from blocks s itself dominates: loop back edges)."""
        _idom, preds, _succ, entry = self.dominators()
        if s == entry or not self.dominates(s, b):
            return False
        return all(p == d or self.dominates(s, p) for p in preds[s])

    def branch_edges(self, carriers):
        """[(carrier, from block, to block, S, havoc, text)]: every CFG edge of a P-test, with the
        tag set under which it is taken."""
        out = []
        for b in self.f["blocks"]:
            t = b["insts"][-1]
            if t["mnem"] == "condbr":
                bt = self.bool_test(t["roles"]["cond"], carriers)
                if bt is None:
                    continue
                car, S, hv = bt
                uni = frozenset(carriers[car]["universe"])
                (tt, _a), (ft, _b) = t["succ"][0], t["succ"][1]
                if tt == ft:
                    continue
                out.append((car, b["label"], tt, S, hv, t["text"]))
                out.append((car, b["label"], ft, uni - S, hv, t["text"]))
            elif t["mnem"] == "switch":
                tg = self.tag(t["roles"]["selector"], carriers)
                if tg is None:
                    continue
                car, hv = tg
                uni = frozenset(carriers[car]["universe"])
                sm = re.match(r"^switch %\d+ \[((?: -?\d+: bb\d+(?:\([^)]*\))?)*) default: (bb\d+)", t["text"])
                cases = [(int(v), "bb" + l) for v, l in re.findall(r" (-?\d+): bb(\d+)", sm.group(1))]
                for v, _l in cases:
                    if v not in uni:
                        raise Refusal(f"arm {self.arm.name}: function #{self.k} switches on a "
                                      f"{car} tag with case {v}, outside its {len(uni)} variants")
                targets = defaultdict(set)
                for v, lbl in cases:
                    targets[lbl].add(v)
                targets[sm.group(2)] |= uni - {v for v, _l in cases}
                for lbl, S in targets.items():
                    out.append((car, b["label"], lbl, frozenset(S), hv, t["text"]))
        return out


# ---------------------------------------------------------------------------
# Interprocedural summaries: what a return derives from, and predicate functions.
# ---------------------------------------------------------------------------
def return_summaries(arm, bodies):
    """arm.ret_undef[k] / arm.ret_params[k]: whether k's returned value may derive from an undef,
    and from which parameters -- a least fixpoint over the call graph (both only grow)."""
    arm.ret_undef, arm.ret_params = {}, {}
    for _round in range(64):
        changed = False
        for k in bodies:
            fv = FuncView(arm, k)
            und, ps = False, set()
            for b in fv.f["blocks"]:
                t = b["insts"][-1]
                if t["mnem"] == "ret":
                    for x in t["uses"]:
                        u, q = fv.origins(x)
                        und, ps = und or u, ps | q
            if und != arm.ret_undef.get(k, False) or frozenset(ps) != arm.ret_params.get(k, frozenset()):
                arm.ret_undef[k], arm.ret_params[k] = und, frozenset(ps)
                changed = True
        if not changed:
            return
    raise Refusal(f"arm {arm.name}: return summaries did not reach a fixpoint")


def _subject_param(fv, tag_value):
    """For a tag read inside a predicate function: ('deref', p) when the carrier value is loaded
    through entry parameter p (pointer passes only), ('value', p) when it IS parameter p."""
    v = tag_value
    for _ in range(16):
        i = fv.inst(v)
        if i is not None and i["mnem"] in TAG_CASTS and "operand" in i["roles"]:
            v = i["roles"]["operand"]
            continue
        break
    i = fv.inst(v)
    if i is None or i["mnem"] != "extractfield":
        return None
    x = i["roles"]["aggregate"]
    d = fv.defs.get(x)
    if d and d[0] == "param" and d[1] == 0:
        return ("value", fv.entry_params.index(x))
    xi = fv.inst(x)
    if xi is None or xi["mnem"] != "load":
        return None
    a = xi["roles"]["ptr"]
    for _ in range(16):
        ai = fv.inst(a)
        if ai is not None and ai["mnem"] in PTR_PASS:
            a = ai["roles"]["ptr" if ai["mnem"] in ("borrow", "borrow_mut") else "operand"]
            continue
        break
    d = fv.defs.get(a)
    if d and d[0] == "param" and d[1] == 0:
        return ("deref", fv.entry_params.index(a))
    return None


def _returned_const(fv, path, v):
    """The bool constant `v` holds at the end of `path` (a list of block indices), reading an
    alloca through the LAST store to it on the path; None when it is not a known constant."""
    c = fv.const_bool(v)
    if c is not None:
        return c
    i = fv.inst(v)
    if i is None or i["mnem"] != "load":
        return None
    slot = i["roles"]["ptr"]
    last = None
    for bi in path:
        for x in fv.f["blocks"][bi]["insts"]:
            if x["mnem"] == "store" and x["roles"]["ptr"] == slot:
                last = x["roles"]["value"]
            if x is i:
                break
    return None if last is None else fv.const_bool(last)


def predicate_summaries(arm, bodies, carriers, max_blocks=24, max_paths=64):
    """arm.pred_summary[k] = (param, carrier, S): k returns a bool that is true exactly when the
    carrier tag of its parameter (the value, or the value it points to) is in S. Derived by
    enumerating EVERY entry-to-ret path of a small acyclic body: every branch on the way must be
    a P-test of that one subject, every path must return a known constant, and the true-paths'
    and false-paths' tag sets must partition the carrier's universe. Anything else: no summary."""
    arm.pred_summary = {}
    for k in bodies:
        f = arm.funcs[k]
        if not f["blocks"] or len(f["blocks"]) > max_blocks:
            continue
        fv = FuncView(arm, k)
        idx = {lbl: i for i, lbl in enumerate(fv.labels)}
        edges = {}
        subject = None
        ok = True
        for b in f["blocks"]:
            t = b["insts"][-1]
            if t["mnem"] not in ("condbr", "switch"):
                continue
            be = [e for e in fv.branch_edges(carriers) if e[1] == b["label"]]
            if not be or any(e[4] for e in be):
                ok = False
                break
            src = _subject_param(fv, t["roles"]["selector"]) if t["mnem"] == "switch" else None
            if t["mnem"] == "condbr":
                ok = False  # a condbr predicate function is not summarised: none needed yet
                break
            key = (be[0][0], src)
            if src is None or (subject is not None and subject != key):
                ok = False
                break
            subject = key
            for e in be:
                edges[(e[1], e[2])] = e[3]
        if not ok or subject is None:
            continue
        uni = frozenset(carriers[subject[0]]["universe"])
        true_s, false_s, n_paths = set(), set(), 0
        stack = [([0], uni)]
        while stack and ok:
            path, S = stack.pop()
            b = f["blocks"][path[-1]]
            t = b["insts"][-1]
            if t["mnem"] == "ret":
                n_paths += 1
                c = _returned_const(fv, path, t["uses"][0]) if len(t["uses"]) == 1 else None
                if c is None or n_paths > max_paths:
                    ok = False
                    break
                (true_s if c else false_s).update(S)
                continue
            if t["mnem"] not in ("br", "condbr", "switch"):
                ok = False
                break
            for lbl, _a in t.get("succ", ()):
                j = idx[lbl]
                if j in path:
                    ok = False
                    break
                stack.append((path + [j], S & edges.get((b["label"], lbl), uni)))
        if ok:
            if (true_s & false_s) or (true_s | false_s) != uni:
                # Holds by construction (one subject, switches only, every exit a `ret`); a
                # summary that did not partition the universe would be no predicate at all.
                raise Refusal(f"internal: predicate summary of function #{k} does not "
                              f"partition its carrier's tags")
            arm.pred_summary[k] = (subject[1][1], subject[0], frozenset(true_s))


# ---------------------------------------------------------------------------
# (2) Configuration strata by dominance.
# ---------------------------------------------------------------------------
def gated_edges(arm, bodies, carriers):
    """{carrier: {"dominated": {edge: why}, "havoc": {edge: why}}} over every call site of
    `bodies` that an excluded-tag edge of a P-test edge-dominates."""
    out = {c: {"dominated": {}, "havoc": {}} for c in carriers if not c.startswith("_")}
    for k in sorted(bodies):
        fv = arm.view(k)
        bes = [e for e in fv.branch_edges(carriers)
               if e[3] and e[3] <= carriers[e[0]]["excluded"]]
        if not bes:
            continue
        for e in arm.succ(k):
            for car, d, s, S, hv, text in bes:
                if fv.edge_dominates(d, s, e[1]):
                    why = {"branch_block": d, "edge_to": s, "branch": text,
                           "taken_for": sorted(carriers[car]["universe"][z] for z in S),
                           "subject": "havoc" if hv else "input"}
                    out[car]["havoc" if hv else "dominated"].setdefault(e, why)
    # Every edge a cut will use is re-checked here, not trusted from the loop above.
    for car in out:
        for e, why in out[car]["dominated"].items():
            fv = arm.view(e[0])
            if not fv.dominates(why["edge_to"], e[1]):
                raise Refusal(f"internal: cut edge {e} is not dominated by {why['edge_to']}")
    return out


def havoc_branch_dominating(fv, block):
    """A branch whose scrutinee is a havoc value OF NO CARRIER TYPE (so it is no P-test) and one
    of whose edges dominates `block`: the IR branches on garbage there, and says nothing about
    what the source tested. Still NOT a cut; recorded so it is not mistaken for no branch."""
    for b in fv.f["blocks"]:
        t = b["insts"][-1]
        if t["mnem"] not in ("condbr", "switch"):
            continue
        scrut = t["roles"]["cond" if t["mnem"] == "condbr" else "selector"]
        if not fv.havoc(scrut):
            continue
        for s, _a in t["succ"]:
            if fv.edge_dominates(b["label"], s, block):
                return {"branch_block": b["label"], "edge_to": s, "branch": t["text"][:160],
                        "subject": "havoc", "test": "unrecognized: a branch on a havoc value"}
    return None


def seed_entry_edges(arm, bodies, is_seed):
    seed = {k for k in bodies if is_seed(arm.funcs[k]["name"])}
    edges = [e for k in sorted(bodies) if k not in seed for e in arm.succ(k) if e[3] in seed]
    return seed, edges


def _cfg_seed(name):
    base = name.split("::<__trust")[0]
    return bool(CFG_SEED.match(base) or CFG_SEED_CLOSURE.search(name))


def _prof_seed(name):
    return bool(PROFILER_SEED.match(name.split("::<__trust")[0]) or PROFILER_SEED_CLOSURE.search(name))


def _short(name, n=110):
    s = tir_symbols.canonical_identity(name)
    return s if len(s) <= n else s[:n - 3] + "..."


def strata(arm, carriers):
    full = arm.reach()
    g = gated_edges(arm, full, carriers)
    prof_cut = frozenset(g["PROF"]["dominated"])
    cfg_cut = frozenset(g["MODE"]["dominated"]) | frozenset(g["NODE"]["dominated"])
    cfg_havoc = frozenset(g["MODE"]["havoc"]) | frozenset(g["NODE"]["havoc"])
    prof_keep = arm.reach(cut=prof_cut)
    pruned = arm.reach(cut=cfg_cut)
    if_exact = arm.reach(cut=cfg_cut | cfg_havoc)
    prof_keep_h = arm.reach(cut=prof_cut | frozenset(g["PROF"]["havoc"]))

    def verdicts(edges, dom, hav, keep, keep_h):
        rows = []
        for e in edges:
            if e in dom:
                v, why = "dominated", dom[e]
            elif e[0] not in keep:
                v, why = "entry_gated", {"caller_reachable_only_through_gated_edges": True}
            elif e in hav:
                v, why = "havoc", hav[e]
            elif e[0] not in keep_h:
                v, why = "havoc", {"caller_reachable_only_through_gated_or_havoc_edges": True}
            else:
                hb = havoc_branch_dominating(arm.view(e[0]), e[1])
                v, why = ("havoc", hb) if hb else ("undominated", None)
            rows.append({"caller": _short(arm.funcs[e[0]]["name"]), "block": e[1], "index": e[2],
                         "callee": _short(arm.funcs[e[3]]["name"]), "verdict": v, "why": why})
        return rows

    prof_seed, prof_edges = seed_entry_edges(arm, full, _prof_seed)
    cfg_seed, cfg_edges = seed_entry_edges(arm, prof_keep_names(arm, full, prof_edges), _cfg_seed)
    dom_cfg = {**g["MODE"]["dominated"], **g["NODE"]["dominated"]}
    hav_cfg = {**g["MODE"]["havoc"], **g["NODE"]["havoc"]}
    prof_rows = verdicts(prof_edges, g["PROF"]["dominated"], g["PROF"]["havoc"], prof_keep,
                         prof_keep_h)
    cfg_rows = verdicts(cfg_edges, dom_cfg, hav_cfg, pruned, if_exact)
    seed_prof_keep = arm.reach(cut=frozenset(prof_edges))
    seed_both_keep = arm.reach(cut=frozenset(prof_edges) | frozenset(cfg_edges))

    def size(s):
        return {"bodies": len(s), "instructions": arm.ninst(s)}

    def gated_list(d):
        return [{"caller": _short(arm.funcs[e[0]]["name"]), "block": e[1], "index": e[2],
                 "callee": _short(arm.funcs[e[3]]["name"]), **why} for e, why in sorted(d.items())]

    return {
        "full": full, "pruned": pruned, "prof_keep": prof_keep, "prof_cut": prof_cut,
        "report": {
            "closure": size(full),
            "profiler_stratum_C0": {
                "reading": "D17: discharged at C0 (safety + frame), NOT pruned from the theorem",
                **size(full - prof_keep), "gated_edges": len(prof_cut),
                "gated": gated_list(g["PROF"]["dominated"]),
                "havoc_gated": gated_list(g["PROF"]["havoc"])},
            "cfg_cut": {
                "reading": "E4 lean_nodes_and_mode: the only precondition cut; the pruned "
                           "closure is the closure minus this stratum",
                **size(full - pruned), "gated_edges": len(cfg_cut),
                "gated": gated_list(dom_cfg), "havoc_gated": gated_list(hav_cfg),
                "if_havoc_tests_were_exact": size(full - if_exact)},
            "pruned_closure": size(pruned),
            "seed_verdicts": {
                "profiler": {"seed_bodies": len(prof_seed), "entry_edges": len(prof_edges),
                             "counts": dict(Counter(r["verdict"] for r in prof_rows)),
                             "edges": prof_rows},
                "cfg": {"seed_bodies": len(cfg_seed), "entry_edges": len(cfg_edges),
                        "counts": dict(Counter(r["verdict"] for r in cfg_rows)),
                        "edges": cfg_rows}},
            "design_reconciliation": {
                "profiler_name_seeded": {"edges": len(prof_edges),
                                         **size(full - seed_prof_keep),
                                         "design": DESIGN_PROFILER},
                "cfg_name_seeded_after_profiler": {
                    "edges": len(cfg_edges), **size(seed_prof_keep - seed_both_keep),
                    "remaining_bodies": len(seed_both_keep), "design": DESIGN_CFG},
            },
            "carriers": {c: {"row": f"{v['key'][0]}.{v['key'][1]}",
                             "excluded": sorted(v["universe"][z] for z in v["excluded"])}
                         for c, v in carriers.items() if not c.startswith("_")},
            "mode_carried_by": carriers["_mode_holders"],
            "predicate_summaries": sorted(
                {"function": _short(arm.funcs[k]["name"]), "param": p, "carrier": c,
                 "true_for": sorted(carriers[c]["universe"][z] for z in S)}
                for k, (p, c, S) in arm.pred_summary.items()),
        },
        "cfg_rows": cfg_rows,
        "if_exact": if_exact,
        "seed_both_keep": seed_both_keep,
    }


def prof_keep_names(arm, full, prof_edges):
    """The design's order: the cubical/ZFC seed is taken over the closure the profiler seed
    leaves, so its entry edges are not the profiler's."""
    return arm.reach(cut=frozenset(prof_edges)) & full


# ---------------------------------------------------------------------------
# (3) Family keys.
# ---------------------------------------------------------------------------
_BODY_TOKEN = re.compile(
    r"(?:@|fndef<)func\.(\d+)|@global\.(\d+)|\b(functy|struct|enum|record|ty|closure)\.(\d+)\b"
    r"|symaddr<([^>]*)>")


class Canon:
    """Canonical forms of type rows and globals, with ids renumbered breadth-first from a root."""

    def __init__(self, arm):
        self.arm = arm
        self.memo = {}
        self.functys = {("functy", k): v for k, v in arm.mod["functys"].items()}

    def row(self, key):
        if key[0] == "functy":
            return self.functys.get(key)
        if key[0] == "global":
            r = self.arm.rows.get(key)
            return None if r is None else r[1]
        r = self.arm.rows.get(key)
        return None if r is None else r[1]

    def closure_hash(self, key):
        """sha256 of the row graph reachable from `key`, nodes numbered in BFS order, each row's
        nested tokens replaced by those numbers. Row NAMES stay (legacy spelling)."""
        if key in self.memo:
            return self.memo[key]
        num = {key: 0}
        order = [key]
        parts = []
        q = deque([key])
        while q:
            k = q.popleft()
            text = self.row(k)
            if text is None:
                parts.append(f"{k[0]}:<absent>")
                continue

            def sub(m, _num=num, _order=order, _q=q):
                if m.group(1) is not None or m.group(5) is not None:
                    return "F$"  # a function a row names (a vtable global): a parameter
                nk = ("global", int(m.group(2))) if m.group(2) is not None \
                    else (m.group(3), int(m.group(4)))
                if nk not in _num:
                    _num[nk] = len(_order)
                    _order.append(nk)
                    _q.append(nk)
                return f"{nk[0]}#{_num[nk]}"

            parts.append(f"{k[0]}:" + _BODY_TOKEN.sub(sub, text))
        h = hashlib.sha256("\n".join(parts).encode()).hexdigest()
        self.memo[key] = h
        return h


def family_keys(arm, bodies):
    """{body: (shape key, enc key)}."""
    canon = arm.__dict__.setdefault("_canon", Canon(arm))
    out = {}
    for k in bodies:
        f = arm.funcs[k]
        params = {}
        tys, glbs = [], []

        def sub(m, _p=params, _t=tys, _g=glbs):
            if m.group(1) is not None:
                key = ("func", m.group(1))
                tag = "F"
            elif m.group(2) is not None:
                key = ("global", int(m.group(2)))
                tag = "G"
            elif m.group(5) is not None:
                key = ("func", "sym:" + m.group(5))
                tag = "F"
            else:
                key = (m.group(3), int(m.group(4)))
                tag = m.group(3)
            if key not in _p:
                _p[key] = sum(1 for x in _p if x[0] == key[0] or (tag == "F" and x[0] == "func"))
                if tag == "G":
                    _g.append(key)
                elif tag != "F":
                    _t.append(key)
            return f"{tag}${_p[key]}"

        lines = [_BODY_TOKEN.sub(sub, f"functy.{f['functy']}")]
        for b in f["blocks"]:
            lines.append(f"{b['label']}{b['params']}")
            lines.extend(_BODY_TOKEN.sub(sub, i["text"]) for i in b["insts"])
        shape = "\n".join(lines)
        rows = [canon.closure_hash(t) for t in tys]
        for g in glbs:
            rows.append("global:" + canon.closure_hash(g))
        sh = hashlib.sha256(shape.encode()).hexdigest()
        out[k] = (sh, hashlib.sha256((shape + "\n" + "\n".join(rows)).encode()).hexdigest())
    return out


def family_report(arm, keys, bodies):
    shape = Counter(keys[k][0] for k in bodies)
    enc = Counter(keys[k][1] for k in bodies)
    n = len(bodies)
    return {"bodies": n, "shape_families": len(shape), "enc_families": len(enc),
            "shape_collapse_ratio": round(n / len(shape), 4) if shape else None,
            "enc_collapse_ratio": round(n / len(enc), 4) if enc else None,
            "enc_duplicate_bodies": n - len(enc),
            "largest_enc_families": [
                {"size": c, "example": _short(arm.funcs[min(k for k in bodies
                                                          if keys[k][1] == h)]["name"], 140)}
                for h, c in enc.most_common(5) if c > 1]}


def family_stability(arms_keys):
    """Pairwise, over bodies joined by `canonical_identity` name (unambiguous in both arms):
    byte-equal keys, and whether the PARTITION agrees (each family maps to exactly one family
    with the same members). Input: {arm: ({canonical name: keys}, [canonical names of the set])},
    names that occur twice in one arm's set are left out of the join."""
    named = {}
    for a, (keys, names) in arms_keys.items():
        c = Counter(names)
        named[a] = {n: keys[n] for n in names if c[n] == 1}
    out = {}
    names = sorted(named)
    for i, a in enumerate(names):
        for b in names[i + 1:]:
            common = sorted(set(named[a]) & set(named[b]))
            row = {"joined_bodies": len(common),
                   "only_in_" + a: len(set(named[a]) - set(named[b])),
                   "only_in_" + b: len(set(named[b]) - set(named[a]))}
            for tier, t in (("shape", 0), ("enc", 1)):
                eq = sum(1 for n in common if named[a][n][t] == named[b][n][t])
                fa, fb = defaultdict(set), defaultdict(set)
                for n in common:
                    fa[named[a][n][t]].add(n)
                    fb[named[b][n][t]].add(n)
                stable = sum(1 for fam in fa.values()
                             if len({named[b][n][t] for n in fam}) == 1
                             and fb[named[b][next(iter(fam))][t]] == fam)
                split = sum(1 for fam in fa.values() if len({named[b][n][t] for n in fam}) > 1)
                merged = sum(1 for fam in fb.values() if len({named[a][n][t] for n in fam}) > 1)
                row[tier] = {"byte_equal_keys": eq, "families": len(fa), "stable_families": stable,
                             "split_families": split, "merged_families": merged}
            out[f"{a}~{b}"] = row
    return out


# ---------------------------------------------------------------------------
# (4) Assert classification per site (D18).
# ---------------------------------------------------------------------------
GENUINE_OBL = ("check.bounds", "check.arith", "check.conditional_panic")
CHECK_ANN = ("no_overflow", "in_bounds")


def _false_true_ids(f):
    """The reader's rule (`static_block_reasons`): a const bool, or a copy of one, function-wide."""
    fs, ts = set(), set()
    for b in f["blocks"]:
        for i in b["insts"]:
            if i["mnem"] == "const" and i["const_ty"] == "bool":
                (fs if i["const_value"] == "false" else ts).update(i["res"])
            elif i["mnem"] == "copy" and i["roles"]["operand"] in fs:
                fs.update(i["res"])
            elif i["mnem"] == "copy" and i["roles"]["operand"] in ts:
                ts.update(i["res"])
    return fs, ts


def _slice_has_check_ann(fv, v, depth=0, seen=None):
    seen = set() if seen is None else seen
    if v in seen or depth > 8:
        return False
    seen.add(v)
    i = fv.inst(v)
    if i is None:
        return False
    if any(a in i.get("ann", "") for a in CHECK_ANN):
        return True
    return any(_slice_has_check_ann(fv, u, depth + 1, seen) for u in i["uses"])


def classify_assert(arm, k, b, j, fs, ts):
    i = b["insts"][j]
    c = i["roles"]["cond"]
    nxt = b["insts"][j + 1]
    nm = nxt["mnem"]
    if nm == "undef":
        nm = "havoc" if "fresh_symbolic_havoc" in nxt.get("ann", "") else "undef"
    elif nm not in ("br", "unreachable"):
        nm = "other"
    obl = list(arm.obl.get((k, b["label"], j), ()))
    if not obl and j > 0 and c in b["insts"][j - 1]["res"]:
        obl = list(arm.obl.get((k, b["label"], j - 1), ()))
    cond = "false" if c in fs else "true" if c in ts else "computed"
    if i.get("ub_halt"):
        return "ub_halt", cond, nm, obl
    if cond == "true":
        return "trivial.true", cond, nm, obl
    if cond == "false":
        if "panic_call" in obl:
            return "genuine.panic_call", cond, nm, obl
        if "assume.drop_glue" in obl:
            return "stand_in.drop_glue_assumption", cond, nm, obl
        if any(o.startswith("assume.") for o in obl):
            return "stand_in.assumption", cond, nm, obl
        if any(o in GENUINE_OBL for o in obl):
            return "genuine.check_folded_false", cond, nm, obl
        return "stand_in.unkeyed_" + nm, cond, nm, obl
    if any(o in GENUINE_OBL or o == "panic_call" for o in obl):
        return "genuine.check", cond, nm, obl
    if any(o.startswith("assume.") for o in obl):
        return "stand_in.assumption_computed", cond, nm, obl
    if any(a in i.get("ann", "") for a in CHECK_ANN) or _slice_has_check_ann(arm.view(k), c):
        return "genuine.check_unsited", cond, nm, obl
    if nm == "havoc":
        # The lowering's idiom for an operation it does not model: assert the operation's
        # PRECONDITION, then havoc its result (`char::from_u32_unchecked`'s range check,
        # `Layout::from_size_align_unchecked`'s alignment check). A violated precondition there is
        # undefined behaviour, not a Rust panic, so a sanctioned halt would make it free.
        return "stand_in.unkeyed_computed_havoc", cond, nm, obl
    return "unclassified.computed", cond, nm, obl


def assert_census(arm, bodies):
    per_class = Counter()
    per_fn = {}
    shape = Counter()
    shape_fns = set()
    module_shape = Counter()
    module_fns = set()
    for k, f in enumerate(arm.funcs):
        if f.get("decl"):
            continue
        fs, ts = _false_true_ids(f)
        for b in f["blocks"]:
            for j, i in enumerate(b["insts"]):
                if i["mnem"] != "assert":
                    continue
                cls, cond, nm, _obl = classify_assert(arm, k, b, j, fs, ts)
                if cond == "false":
                    module_shape[nm] += 1
                    module_fns.add(k)
                if k not in bodies:
                    continue
                per_class[cls] += 1
                per_fn.setdefault(k, Counter())[cls] += 1
                if cond == "false":
                    shape[nm] += 1
                    shape_fns.add(k)
    stand_in = sum(v for c, v in per_class.items() if c.startswith("stand_in."))
    return {
        "closure": {"asserts": sum(per_class.values()), "classes": dict(sorted(per_class.items())),
                    "stand_in": stand_in,
                    "genuine": sum(v for c, v in per_class.items() if c.startswith("genuine.")),
                    "unclassified": per_class.get("unclassified.computed", 0),
                    "const_false_shape": {"asserts": sum(shape.values()), "functions": len(shape_fns),
                                          "next": dict(sorted(shape.items()))}},
        "module_const_false_shape": {"asserts": sum(module_shape.values()),
                                     "functions": len(module_fns),
                                     "next": dict(sorted(module_shape.items()))},
        "unsited_obligations": dict(sorted(arm.unsited_obl.items())),
        "per_function": sorted(
            ({"function": _short(arm.funcs[k]["name"], 160),
              "stand_in": sum(v for c, v in cnt.items() if c.startswith("stand_in.")),
              "classes": dict(sorted(cnt.items()))} for k, cnt in per_fn.items()),
            key=lambda r: (-r["stand_in"], r["function"])),
    }


# ---------------------------------------------------------------------------
# (5) Layout mixing (the D20 signal).
# ---------------------------------------------------------------------------
def _is_aggregate(ty):
    ty = ty.strip()
    return ty.startswith(AGG_PREFIXES) and ty not in ("()",)


class AddrView:
    """Address provenance per function: (root, flags) with flags from {byte, havoc}."""

    def __init__(self, arm, k):
        self.arm, self.k = arm, k
        self.fv = arm.view(k)
        self.memo = {}

    def addr(self, v, depth=0):
        if v in self.memo:
            return self.memo[v]
        self.memo[v] = (("cycle", v), frozenset())
        fv = self.fv
        d = fv.defs.get(v)
        res = (("other", v), frozenset())
        if d is None:
            res = (("unbound", v), frozenset())
        elif d[0] == "param":
            res = (("param", fv.entry_params.index(v)), frozenset()) if d[1] == 0 \
                else (("phi", v), frozenset())
        else:
            i = d[3]
            m = i["mnem"]
            if m == "gep" and depth < 64:
                root, fl = self.addr(i["roles"]["base"], depth + 1)
                gm = _GEP.match(i["text"])
                elem = gm.group(1).strip() if gm else ""
                flags = set(fl)
                for x in i["gep_indices"]:
                    c = fv.const_int(x)
                    if fv.havoc(x):
                        flags.add("havoc")
                    if c != 0:
                        flags.add("byte" if elem in BYTE_ELEMS else "elem")
                res = (root, frozenset(flags))
            elif m in PTR_PASS and depth < 64:
                res = self.addr(i["roles"]["ptr" if m in ("borrow", "borrow_mut") else "operand"],
                                depth + 1)
            elif m == "alloca":
                res = (("alloca", v), frozenset())
            elif m == "global_addr":
                res = (("global", i["global"]), frozenset())
            elif m == "load":
                res = (("loadptr", v), frozenset())
            elif m == "extractfield":
                res = (("fieldptr", v), frozenset())
            elif m == "undef":
                res = (("havoc", v), frozenset({"havoc"}))
            elif m == "call" and depth < 64:
                ra = self.arm.ret_alias.get(i["callee"])
                if ra is not None and ra[0] < len(i["roles"]["args"]):
                    root, fl = self.addr(i["roles"]["args"][ra[0]], depth + 1)
                    res = (root, fl | ra[1])
                else:
                    res = (("callret", v), frozenset())
        self.memo[v] = res
        return res

    def accesses(self):
        """[(root, flags, type, is aggregate, instruction text)] for every load/store."""
        out = []
        for b in self.fv.f["blocks"]:
            for i in b["insts"]:
                m = i["mnem"]
                if m == "load":
                    lm = _LOAD.match(i["text"])
                    ty = lm.group(1) if lm else "?"
                elif m == "store":
                    sm = re.match(r"^(?:volatile )?store (.+) %\d+, ptr %\d+", i["text"])
                    ty = sm.group(1) if sm else "?"
                elif m in ("atomic_load", "atomic_store", "atomicrmw", "cmpxchg"):
                    ty = "atomic"
                else:
                    continue
                root, fl = self.addr(i["roles"]["ptr"])
                out.append((root, fl, ty, _is_aggregate(ty), i["text"]))
        return out


def pointer_returns(arm, bodies):
    """arm.ret_alias[k] = (param, flags) when every `ret` of k returns an address rooted at the
    same parameter (the flags any of them carries); a least fixpoint."""
    arm.ret_alias = {}
    for _round in range(64):
        changed = False
        for k in bodies:
            av = AddrView(arm, k)
            roots = set()
            flags = set()
            n = 0
            for b in av.fv.f["blocks"]:
                t = b["insts"][-1]
                if t["mnem"] == "ret" and len(t["uses"]) == 1:
                    root, fl = av.addr(t["uses"][0])
                    roots.add(root)
                    flags |= fl
                    n += 1
            new = None
            if n and len(roots) == 1 and next(iter(roots))[0] == "param":
                new = (next(iter(roots))[1], frozenset(flags))
            if arm.ret_alias.get(k) != new:
                arm.ret_alias[k] = new
                changed = True
        if not changed:
            return
    raise Refusal(f"arm {arm.name}: pointer-return summaries did not reach a fixpoint")


def _agg_name(arm, ty):
    k = _tok_key(ty)
    if k and k in arm.rows and arm.rows[k][0]:
        return arm.rows[k][0]
    return ty


def _is_neon_probe(arm, ty):
    k = _tok_key(ty)
    if not k or arm.rows.get(k, (None,))[0] != PACKED_ROW:
        return False
    return any(arm.rows.get(_tok_key(t) or ("", -1), (None,))[0] == NEON_GROUP_PAYLOAD
               for t, _o in struct_fields(arm, k))


def _byte_kind(fl):
    """'exact' / 'havoc' for a byte-stepped address (havoc: an undef index or base on the way),
    None when the address takes no byte step."""
    if "byte" not in fl:
        return None
    return "havoc" if "havoc" in fl else "exact"


def layout_mixing(arm, bodies, paths):
    """M1 sites and M2 objects over `bodies` (see the docstring, item 5). An address whose byte
    step goes through a havoc (an undef index: `Expr::kind` today) is reported apart: it is an
    executability defect, not evidence about the memory model."""
    pointer_returns(arm, bodies)
    views = {k: AddrView(arm, k) for k in bodies}
    acc = {k: views[k].accesses() for k in bodies}
    calls = defaultdict(list)  # callee -> [(caller, [(root, flags) per arg])]
    for k in bodies:
        for b in arm.funcs[k]["blocks"]:
            for i in b["insts"]:
                if i["mnem"] == "call" and i["callee"] in views:
                    calls[i["callee"]].append((k, [views[k].addr(a) for a in i["roles"]["args"]]))
    # Top-down: which parameters can receive a byte-stepped address, and from which function
    # the byte step comes (per kind).
    byte_in = {"exact": {}, "havoc": {}}
    changed = True
    while changed:
        changed = False
        for callee, sites in calls.items():
            for caller, args in sites:
                for p, (root, fl) in enumerate(args):
                    for kind in ("exact", "havoc"):
                        if (callee, p) in byte_in[kind]:
                            continue
                        if _byte_kind(fl) == kind:
                            byte_in[kind][(callee, p)] = caller
                        elif root[0] == "param" and (caller, root[1]) in byte_in[kind]:
                            byte_in[kind][(callee, p)] = byte_in[kind][(caller, root[1])]
                        else:
                            continue
                        changed = True
    sites = {"exact": [], "havoc": []}
    for k in sorted(bodies):
        for root, fl, ty, agg, text in acc[k]:
            if not agg:
                continue
            for kind in ("exact", "havoc"):
                via = None
                if _byte_kind(fl) == kind:
                    via = "local"
                elif root[0] == "param" and (k, root[1]) in byte_in[kind]:
                    via = _short(arm.funcs[byte_in[kind][(k, root[1])]]["name"], 120)
                if via is None:
                    continue
                origin = k if via == "local" else byte_in[kind][(k, root[1])]
                sites[kind].append({"function": _short(arm.funcs[k]["name"], 160), "access": text,
                                    "type": _agg_name(arm, ty), "byte_step_in": via,
                                    "neon_group_probe": _is_neon_probe(arm, ty),
                                    "path": paths.get(k, []),
                                    "path_to_byte_step": paths.get(origin, [])})
                break
    for kind in sites:
        sites[kind].sort(key=lambda x: (not x["neon_group_probe"], x["function"], x["access"]))
    # Bottom-up: what each (function, root) is accessed as, itself and through callees.
    summ = defaultdict(set)  # (k, root) -> {("AGG", type) | ("BYTE", kind)}
    for k in bodies:
        for root, fl, ty, agg, _t in acc[k]:
            bk = _byte_kind(fl)
            if bk:
                summ[(k, root)].add(("BYTE", bk))
            elif agg and not ({"elem", "havoc"} & fl):
                summ[(k, root)].add(("AGG", ty))
    changed = True
    while changed:
        changed = False
        for callee, sites_ in calls.items():
            for caller, args in sites_:
                for p, (root, fl) in enumerate(args):
                    src = summ.get((callee, ("param", p)))
                    if not src:
                        continue
                    bk = _byte_kind(fl)
                    if bk:
                        add = {("BYTE", bk)}
                    elif {"elem", "havoc"} & fl:
                        add = {t for t in src if t[0] == "BYTE"}
                    else:
                        add = set(src)
                    tgt = summ[(caller, root)]
                    if not add <= tgt:
                        tgt |= add
                        changed = True
    objects = {"exact": defaultdict(list), "havoc": defaultdict(list)}
    roots = Counter()
    for (k, root), tags in summ.items():
        aggs = sorted(t[1] for t in tags if t[0] == "AGG")
        if not aggs:
            continue
        kind = "exact" if ("BYTE", "exact") in tags else "havoc" if ("BYTE", "havoc") in tags \
            else None
        if kind is None:
            continue
        roots[kind] += 1
        for ty in aggs:
            objects[kind][_agg_name(arm, ty)].append((k, root))

    def obj_rows(d):
        rows = []
        for name, lst in d.items():
            ks = sorted({k for k, _r in lst})
            rows.append({"object_type": name, "roots": len(lst), "functions": len(ks),
                         "example": _short(arm.funcs[ks[0]]["name"], 140),
                         "example_root": list(lst[0][1]), "path": paths.get(ks[0], [])})
        rows.sort(key=lambda r: (-r["functions"], r["object_type"]))
        return rows

    return {
        "sites": sites["exact"], "objects": obj_rows(objects["exact"]),
        "mixed_roots": roots["exact"],
        "sites_local": sum(1 for x in sites["exact"] if x["byte_step_in"] == "local"),
        "sites_via_call": sum(1 for x in sites["exact"] if x["byte_step_in"] != "local"),
        "neon_group_probe_sites": sum(1 for x in sites["exact"] if x["neon_group_probe"]),
        "havoc_offset": {"sites": len(sites["havoc"]), "mixed_roots": roots["havoc"],
                         "objects": obj_rows(objects["havoc"])[:25],
                         "site_examples": sites["havoc"][:10]},
        "byte_step_accesses": {kd: sum(1 for k in bodies for a_ in acc[k]
                                       if _byte_kind(a_[1]) == kd) for kd in ("exact", "havoc")},
        "aggregate_accesses": sum(1 for k in bodies for a_ in acc[k] if a_[3]),
    }


def call_paths_avoiding(arm, bodies, avoid):
    """Shortest paths from infer_type, preferring ones that avoid `avoid` (the profiler's gated
    edges), so a named path is a main-line one whenever one exists."""
    out = {}
    for cut in (frozenset(avoid), frozenset()):
        parent = {arm.root: None}
        q = deque([arm.root])
        while q:
            k = q.popleft()
            for e in arm.succ(k):
                if e in cut or e[3] not in bodies or e[3] in parent:
                    continue
                parent[e[3]] = k
                q.append(e[3])
        for k in parent:
            if k in out:
                continue
            p, chain = k, []
            while p is not None:
                chain.append(_short(arm.funcs[p]["name"], 90))
                p = parent[p]
            out[k] = chain[::-1]
    return out


# ---------------------------------------------------------------------------
# Measuring the arms, the report, the metrics.
# ---------------------------------------------------------------------------
def measure_arm(arm, sources):
    carriers = derive_carriers(arm, sources)
    full = arm.reach()
    return_summaries(arm, full)
    predicate_summaries(arm, full, carriers)
    sr = strata(arm, carriers)
    pruned = sr["pruned"]
    keys = family_keys(arm, full)
    asserts_full = assert_census(arm, full)
    asserts_pruned = assert_census(arm, pruned)
    paths = call_paths_avoiding(arm, full, sr["prof_cut"])
    mixing = layout_mixing(arm, pruned, paths)
    rep = {
        "dir": arm.dir, "identity": arm.identity,
        "root": _short(arm.funcs[arm.root]["name"]),
        "denominators": {"closure_bodies": len(full), "closure_instructions": arm.ninst(full),
                         "pruned_bodies": len(pruned), "pruned_instructions": arm.ninst(pruned),
                         "module_functions": len(arm.funcs)},
        "strata": sr["report"],
        "families": {"closure": family_report(arm, keys, full),
                     "pruned": family_report(arm, keys, pruned),
                     "design_name_seeded_remainder": family_report(arm, keys, sr["seed_both_keep"])},
        "asserts": {"closure": asserts_full["closure"], "pruned": asserts_pruned["closure"],
                    "module_const_false_shape": asserts_full["module_const_false_shape"],
                    "unsited_obligations": asserts_full["unsited_obligations"],
                    "per_function_pruned": asserts_pruned["per_function"]},
        "layout_mixing": mixing,
    }
    metrics = {
        f"{arm.name}.asserts.stand_in": asserts_pruned["closure"]["stand_in"],
        f"{arm.name}.asserts.unclassified": asserts_pruned["closure"]["unclassified"],
        f"{arm.name}.cfg_cut.gating_edges_not_cut": sum(
            1 for r in sr["cfg_rows"] if r["verdict"] in ("havoc", "undominated")),
        f"{arm.name}.layout_mixing.sites": len(mixing["sites"]),
        f"{arm.name}.layout_mixing.objects": len(mixing["objects"]),
        f"{arm.name}.layout_mixing.roots": mixing["mixed_roots"],
    }
    names = {k: tir_symbols.canonical_identity(arm.funcs[k]["name"]) for k in full}
    return rep, metrics, ({names[k]: keys[k] for k in full}, [names[k] for k in full],
                          [names[k] for k in pruned])


def check_dp_anchor(name, rep):
    """The plan's figures must reproduce on the artifact they were measured on, exactly."""
    if name != "dp":
        return None
    ident = rep["identity"]
    if (ident["manifest_sha256"], ident["text_sha256"]) != (DP_ANCHOR["manifest_sha256"],
                                                            DP_ANCHOR["text_sha256"]):
        raise Refusal("arm dp is not the anchored artifact (manifest/text sha256 differ from "
                      "DP_ANCHOR): the plan's denominators cannot be reproduced on it")
    d = rep["denominators"]
    got = (d["closure_bodies"], d["closure_instructions"])
    if got != (DP_ANCHOR["closure_bodies"], DP_ANCHOR["closure_instructions"]):
        raise Refusal(f"arm dp: infer_type's closure is {got[0]} bodies / {got[1]} instructions, "
                      f"the plan's is {DP_ANCHOR['closure_bodies']} / "
                      f"{DP_ANCHOR['closure_instructions']}: NOT REPRODUCED")
    sh = rep["asserts"]["module_const_false_shape"]
    want_next = DP_ANCHOR["module_const_false_next"]
    if sh["asserts"] != DP_ANCHOR["module_const_false_asserts"] or any(
            sh["next"].get(k) != v for k, v in want_next.items()):
        raise Refusal(f"arm dp: the whole-module const-false assert shape is {sh}, D18 measured "
                      f"{DP_ANCHOR['module_const_false_asserts']} with {want_next}: NOT REPRODUCED")
    return {"reproduced": True, **{k: v for k, v in DP_ANCHOR.items() if "sha256" not in k},
            "d18_function_count_quoted": 582,
            "d18_function_count_measured": sh["functions"],
            "note": "D18 quotes 582 functions; no reading of the whole module or the closure "
                    "reproduces it (functions with a const-false assert: module 1,004, closure "
                    "989 -- the judge's 989 bodies). The assert and successor counts reproduce "
                    "exactly and are what is pinned."}


def _script_sha256():
    from pathlib import Path  # noqa: PLC0415
    h = hashlib.sha256(open(os.path.abspath(__file__), "rb").read())
    for rel in tir_symbols.first_party_imports(Path(__file__)):
        h.update(rel.encode())
        h.update(open(os.path.join(REPO_ROOT, rel), "rb").read())
    return h.hexdigest()


def measure(arm_dirs, repo_root=REPO_ROOT):
    sources = read_sources(repo_root)
    per_arm, metrics, fam = {}, {}, {}
    for name, d in arm_dirs:
        if not os.path.isdir(d):
            raise Refusal(f"arm {name}: no artifact directory {d}")
        arm = Arm(name, d)
        rep, m, famrow = measure_arm(arm, sources)
        del arm  # one arm in memory at a time
        anchor = check_dp_anchor(name, rep)
        if anchor:
            rep["dp_anchor"] = anchor
        per_arm[name] = rep
        metrics.update(m)
        fam[name] = famrow
    stability = {
        "closure": family_stability({a: (r[0], r[1]) for a, r in fam.items()}),
        "pruned": family_stability({a: (r[0], r[2]) for a, r in fam.items()}),
    }
    identity = {"arms": {n: per_arm[n]["identity"] for n, _d in arm_dirs},
                "script_sha256": _script_sha256(), "sources_digest": sources["digest"]}
    return {"schema": SCHEMA, "metrics": dict(sorted(metrics.items())), "identity": identity,
            "arms": per_arm, "family_stability": stability,
            "sources": {"expr_kind_variants": sources["expr_kind_variants"],
                        "e4_lean_nodes_and_mode": sources["e4_statement"]}}


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
            type(v) is int and v >= 0 for v in b["metrics"].values()):
        raise Refusal("baseline metrics must be non-negative integers")
    ident = b["identity"]
    if not isinstance(ident, dict) or sorted(ident) != ["arms", "script_sha256", "sources_digest"]:
        raise Refusal("baseline identity is malformed")
    hist = b["history"]
    if not isinstance(hist, list) or not hist or not isinstance(hist[-1], dict) \
            or hist[-1].get("metrics") != b["metrics"] or hist[-1].get("identity") != ident:
        raise Refusal("baseline metrics/identity are not the ones its last history entry "
                      "recorded: moved by hand")
    return b


def write_baseline(path, report, history):
    b = {"schema": BASELINE_SCHEMA,
         "what": "crystal link 4 strata ratchet (M0 W2); every metric is a BAD count per arm, "
                 "derived by scripts/crystal_link4_strata.py from the callee sidecars",
         "metrics": report["metrics"], "identity": report["identity"], "history": history}
    b["payload_sha256"] = _payload_digest(b)
    tmp = path + ".tmp"
    with open(tmp, "w") as fh:
        json.dump(b, fh, indent=2)
        fh.write("\n")
    os.replace(tmp, path)
    return b


def _artifacts_of(ident):
    return {n: (a["manifest_sha256"], a["text_sha256"]) for n, a in ident["arms"].items()}


def compare(base, report, allow_set_change=False):
    got, want = report["metrics"], base["metrics"]
    if set(got) != set(want) and not allow_set_change:
        raise Refusal(f"baseline names metrics {sorted(set(want) ^ set(got))} the measurement "
                      f"does not (or the reverse): the metric set moved, --reseat it")
    lines = []
    common = sorted(set(got) & set(want))
    worse = [k for k in common if got[k] > want[k]]
    better = [k for k in common if got[k] < want[k]]
    for k in common:
        tag = "WORSE" if k in worse else "better" if k in better else "="
        lines.append(f"  {k:44s} baseline={want[k]:>6}  measured={got[k]:>6}  {tag}")
    for k in sorted(set(got) - set(want)):
        lines.append(f"  {k:44s} baseline=   new  measured={got[k]:>6}  NEW METRIC")
    for k in sorted(set(want) - set(got)):
        lines.append(f"  {k:44s} baseline={want[k]:>6}  measured=  gone  DROPPED METRIC")
    if base["identity"] == report["identity"] and (worse or better):
        lines.append("VERDICT=fail  the baseline claims a state its OWN artifacts do not support "
                     "(same arm, script and source digests, different numbers): refused as "
                     "hand-edited or stale")
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
    return {"action": action, "reason": reason, "metrics": report["metrics"],
            "identity": report["identity"]}


def summary_lines(report):
    out = []
    for name, r in report["arms"].items():
        d = r["denominators"]
        st = r["strata"]
        out.append(f"ARM {name}: closure {d['closure_bodies']} bodies / "
                   f"{d['closure_instructions']} instructions; pruned {d['pruned_bodies']} / "
                   f"{d['pruned_instructions']}"
                   + ("  [dp anchor REPRODUCED]" if r.get("dp_anchor") else ""))
        p, c = st["profiler_stratum_C0"], st["cfg_cut"]
        out.append(f"  profiler stratum (C0, kept): {p['bodies']} bodies / {p['instructions']} "
                   f"instructions over {p['gated_edges']} gated edges")
        out.append(f"  cubical/ZFC cut (pruned): {c['bodies']} bodies / {c['instructions']} "
                   f"instructions over {c['gated_edges']} gated edges; if the havoc-read tags "
                   f"were exact: {c['if_havoc_tests_were_exact']['bodies']} bodies")
        for s in ("profiler", "cfg"):
            sv = st["seed_verdicts"][s]
            out.append(f"  {s} gating edges: {sv['entry_edges']} {json.dumps(sv['counts'], sort_keys=True)}")
        fa = r["families"]
        out.append(f"  families: closure {fa['closure']['bodies']} -> shape "
                   f"{fa['closure']['shape_families']} / enc {fa['closure']['enc_families']}; pruned "
                   f"{fa['pruned']['bodies']} -> shape {fa['pruned']['shape_families']} / enc "
                   f"{fa['pruned']['enc_families']}")
        a = r["asserts"]["pruned"]
        out.append(f"  asserts (pruned): {a['asserts']} = genuine {a['genuine']} + stand-in "
                   f"{a['stand_in']} + unclassified {a['unclassified']} + other "
                   f"{a['asserts'] - a['genuine'] - a['stand_in'] - a['unclassified']}")
        m = r["layout_mixing"]
        out.append(f"  layout mixing (exact byte steps, pruned): {len(m['sites'])} sites "
                   f"({m['sites_local']} local, {m['sites_via_call']} via a caller; "
                   f"{m['neon_group_probe_sites']} NEON group probe), {len(m['objects'])} object "
                   f"types, {m['mixed_roots']} roots; havoc-offset {m['havoc_offset']['sites']} sites")
    for pair, row in report["family_stability"]["closure"].items():
        out.append(f"STABILITY {pair}: joined {row['joined_bodies']}; shape stable "
                   f"{row['shape']['stable_families']}/{row['shape']['families']}, enc stable "
                   f"{row['enc']['stable_families']}/{row['enc']['families']} "
                   f"(byte-equal enc keys {row['enc']['byte_equal_keys']})")
    return out


def arm_dirs_of(args):
    root = args.artifact_root
    if not os.path.isabs(root):
        root = os.path.join(args.repo_root, root)
    dirs = [(n, os.path.join(root, d)) for n, d in ARMS]
    over = {}
    for spec in args.arm or ():
        n, sep, d = spec.partition("=")
        if not sep or not n or not d:
            raise Refusal(f"--arm wants NAME=DIR, got {spec!r}")
        over[n] = d
    if set(over) - {n for n, _d in dirs} and not args.only_arms:
        raise Refusal(f"--arm names {sorted(set(over) - {n for n, _d in dirs})}, not an arm of "
                      f"{[n for n, _d in ARMS]} (use --only-arms to measure others)")
    if args.only_arms:
        return [(n, d) for n, d in over.items()]
    return [(n, over.get(n, d)) for n, d in dirs]


BRIEF_CAPS = {"gated": 25, "havoc_gated": 25, "sites": 20, "objects": 30, "site_examples": 5,
              "per_function_pruned": 40, "largest_enc_families": 5}


def brief(report):
    """The report with its long lists capped (each capped list says how long it was)."""
    def walk(x):
        if isinstance(x, dict):
            out = {}
            for k, v in x.items():
                if k in BRIEF_CAPS and isinstance(v, list) and len(v) > BRIEF_CAPS[k]:
                    out[k] = [walk(y) for y in v[:BRIEF_CAPS[k]]]
                    out[k + "_total"] = len(v)
                else:
                    out[k] = walk(v)
            return out
        if isinstance(x, list):
            return [walk(y) for y in x]
        return x
    return walk(report)


def run(args):
    if args.pinned_inputs:
        from pathlib import Path  # noqa: PLC0415
        print("\n".join(tir_symbols.first_party_imports(Path(__file__))))
        return EXIT_PASS
    if args.self_test:
        return self_test()
    modes = sum(bool(x) for x in (args.rebase, args.init, args.reseat))
    if modes > 1:
        raise Refusal("--init, --rebase and --reseat are exclusive")
    if modes and not (args.reason or "").strip():
        raise Refusal("--init/--rebase/--reseat need a non-empty --reason")
    report = measure(arm_dirs_of(args), args.repo_root)
    for path, doc in ((args.report, brief(report)), (args.report_full, report)):
        if not path:
            continue
        rp = path if os.path.isabs(path) else os.path.join(args.repo_root, path)
        os.makedirs(os.path.dirname(rp) or ".", exist_ok=True)
        with open(rp, "w") as fh:
            json.dump(doc, fh, indent=1, default=sorted)
            fh.write("\n")
    print("\n".join(summary_lines(report)))
    if not (args.check or modes):
        return EXIT_PASS
    baseline_path = args.baseline if os.path.isabs(args.baseline) \
        else os.path.join(args.repo_root, args.baseline)
    if args.init:
        if os.path.exists(baseline_path):
            raise Refusal(f"{baseline_path} exists; --init creates, it never overwrites")
        write_baseline(baseline_path, report, [_history_entry("init", args.reason, report)])
        print(f"BASELINE=written {baseline_path}")
        return EXIT_PASS
    base = load_baseline(baseline_path)
    code, lines = compare(base, report, allow_set_change=bool(args.reseat))
    print("\n".join(lines))
    got, want = report["metrics"], base["metrics"]
    if args.rebase:
        if code != EXIT_PASS or any(got[k] > want.get(k, got[k]) for k in got):
            print("REBASE=refused  a baseline is lowered only when no metric is worse")
            return EXIT_FAIL
        if _artifacts_of(base["identity"]) == _artifacts_of(report["identity"]):
            print("REBASE=refused  no arm's artifact changed: a different count on the SAME "
                  "artifacts comes from the instrument, and moves only through --reseat")
            return EXIT_FAIL
        write_baseline(baseline_path, report,
                       base["history"] + [_history_entry("rebase", args.reason, report)])
        print(f"REBASE=written {baseline_path}")
        return EXIT_PASS
    if args.reseat:
        if _artifacts_of(base["identity"]) != _artifacts_of(report["identity"]):
            print("RESEAT=refused  an arm's artifact changed; a reseat re-measures the SAME "
                  "artifacts after an instrument change and nothing else")
            return EXIT_FAIL
        bi, ri = base["identity"], report["identity"]
        if (bi["script_sha256"], bi["sources_digest"]) == (ri["script_sha256"], ri["sources_digest"]):
            print("RESEAT=refused  the instrument did not change")
            return EXIT_FAIL
        write_baseline(baseline_path, report,
                       base["history"] + [_history_entry("reseat", args.reason, report)])
        print(f"RESEAT=written {baseline_path}")
        return EXIT_PASS
    return code


def build_parser():
    ap = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    ap.add_argument("--artifact-root", default=DEFAULT_ARTIFACT_ROOT,
                    help="directory holding the arms (default: <repo>/target/crystal-lane)")
    ap.add_argument("--arm", action="append", help="NAME=DIR: measure arm NAME from DIR")
    ap.add_argument("--only-arms", action="store_true",
                    help="measure exactly the --arm arms (reports; never against the baseline)")
    ap.add_argument("--repo-root", default=REPO_ROOT)
    ap.add_argument("--baseline", default=DEFAULT_BASELINE)
    ap.add_argument("--report", help="write the report JSON here (long lists capped)")
    ap.add_argument("--report-full", help="write the uncapped report JSON here")
    ap.add_argument("--check", action="store_true", help="gate against the baseline")
    ap.add_argument("--init", action="store_true")
    ap.add_argument("--rebase", action="store_true")
    ap.add_argument("--reseat", action="store_true")
    ap.add_argument("--reason")
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--pinned-inputs", action="store_true")
    return ap


def main(argv=None):
    args = build_parser().parse_args(argv)
    if args.only_arms and (args.check or args.init or args.rebase or args.reseat):
        print("REFUSED: --only-arms measures a different arm set; it never touches the baseline")
        return EXIT_REFUSED
    try:
        return run(args)
    except (Refusal, ex.Refusal) as exc:
        print(f"REFUSED: {exc}")
        return EXIT_REFUSED



# ---------------------------------------------------------------------------
# Self-test: synthetic sidecars through the SHARED reader, the real kind.rs and E4 inventory.
# ---------------------------------------------------------------------------
SYN_ROWS = [
    "enum @clean_kernel::mode::CleanMode repr(u8) { Constructive = 0, Impredicative = 1, "
    "Cubical = 2, Directed = 3, Classical = 4, SetTheoretic = 5 } id=1",
    "struct @clean_kernel::tc::heartbeat_profiler::profiler::HeartbeatProfiler { u64 } size=8 align=8 id=9",
    "struct @core::cell::RefCell { isize, struct.9 } size=16 align=8 id=8",
    "enum @core::option::Option repr(u64) { None = 0, Some(struct.8) = 1 } id=7",
    "struct @clean_kernel::tc::TypeChecker { enum.1, enum.7 } size=32 align=8 id=70",
    "struct @__trust_native_enum_view::clean_kernel::expr::kind::ExprKind { isize, u32 } size=16 align=8 id=98",
    "struct @core::core_arch::arm_shared::neon::uint8x8_t { [ty.0 x 8] } size=8 align=8 id=239",
    "struct @core::ptr::Packed { struct.239 } size=8 align=1 repr=packed(1) id=325",
    "struct @S { u64, u64 } size=16 align=8 id=40",
    "struct @S { u64, u32 } size=16 align=8 id=41",
    "struct @S { u64, u64 } size=16 align=8 id=42",
]
MODE_TEST = """    %1 = load struct.70, ptr %0
    %2 = extractfield enum.1 %1, 0
    %3 = extractfield u8 %2, 0"""
SYN = [
    ("root", ex.P + "infer_type::<__trust_args@0>", None),  # body built from the list below
    ("fast", ex.P + "infer_type_fast::<__trust_args@0>", "bb0(%0: ptr):\n    ret %0"),
    ("tick", ex.TARGET_PREFIX + "heartbeat::<impl clean_kernel::tc::TypeChecker<'_>>::"
             "tick_heartbeat::<__trust_args@0>", "bb0(%0: ptr):\n    ret %0"),
    ("gate_mode", "clean_kernel::tc::whnf::gate_mode", f"""bb0(%0: ptr):
{MODE_TEST}
    switch %3 [ 2: bb1 3: bb1 default: bb2 ]
bb1:
    %4 = call {{cubical_only}}(%0)
    br bb2
bb2:
    ret %0"""),
    ("cubical_only", "clean_kernel::tc::infer_cubical::cubical_only",
     "bb0(%0: ptr):\n    %1 = call {inner}(%0)\n    ret %0"),
    ("inner", "helper::inner_of_cubical", "bb0(%0: ptr):\n    %1 = call {deep}(%0)\n    ret %0"),
    ("deep", "clean_kernel::tc::infer_cubical::deep", "bb0(%0: ptr):\n    ret %0"),
    ("gate_havoc", "clean_kernel::tc::whnf::gate_havoc", """bb0(%0: ptr):
    %1 = undef struct.98  ; #proof: fresh_symbolic_havoc
    %2 = extractfield isize %1, 0
    switch %2 [ 14: bb1 default: bb2 ]
bb1:
    %3 = call {zfc_only}(%0)
    br bb2
bb2:
    ret %0"""),
    ("zfc_only", "clean_kernel::tc::infer_zfc::zfc_only", "bb0(%0: ptr):\n    ret %0"),
    ("gate_join", "clean_kernel::tc::whnf::gate_join", f"""bb0(%0: ptr):
{MODE_TEST}
    switch %3 [ 2: bb1 default: bb2 ]
bb1:
    br bb2
bb2:
    %4 = call {{directed_only}}(%0)
    ret %0"""),
    ("directed_only", "clean_kernel::tc::reduction::directed::directed_only", "bb0(%0: ptr):\n    ret %0"),
    ("prof_gate", "clean_kernel::tc::heartbeat::prof_gate", """bb0(%0: ptr):
    %1 = load struct.70, ptr %0
    %2 = extractfield enum.7 %1, 1
    %3 = extractfield u64 %2, 0
    %4 = bitcast u64 %3 to isize
    switch %4 [ 1: bb1 0: bb2 default: bb3 ]
bb1:
    %5 = call {prof_tick}(%0)
    br bb2
bb2:
    ret %0
bb3:
    unreachable"""),
    ("prof_tick", "clean_kernel::tc::heartbeat_profiler::profiler::HeartbeatProfiler::tick",
     "bb0(%0: ptr):\n    ret %0"),
    ("has_cubical", "clean_kernel::mode::CleanMode::has_cubical_layer", """bb0(%0: ptr):
    %1 = alloca bool
    %2 = load enum.1, ptr %0
    %3 = extractfield u8 %2, 0
    switch %3 [ 2: bb1 3: bb2 default: bb3 ]
bb1:
    %4 = const bool true
    store bool %4, ptr %1
    br bb4
bb2:
    %5 = const bool true
    store bool %5, ptr %1
    br bb4
bb3:
    %6 = const bool false
    store bool %6, ptr %1
    br bb4
bb4:
    %7 = load bool, ptr %1
    ret %7"""),
    ("gate_pred", "clean_kernel::tc::whnf::gate_pred", """bb0(%0: ptr):
    %1 = const i64 0
    %2 = gep inbounds i8, ptr %0, %1
    %3 = call {has_cubical}(%2)
    %4 = const bool false
    %5 = const bool true
    %6 = select bool %3, %4, %5
    condbr %6, bb1, bb2
bb1:
    ret %0
bb2:
    %7 = call {kan_only}(%0)
    ret %0"""),
    ("kan_only", "clean_kernel::tc::reduction::kan::kan_only", "bb0(%0: ptr):\n    ret %0"),
    ("gate_node", "clean_kernel::tc::whnf::gate_node", """bb0(%0: ptr):
    %1 = load struct.98, ptr %0
    %2 = extractfield isize %1, 0
    switch %2 [ 14: bb1 default: bb2 ]
bb1:
    %3 = call {node_only}(%0)
    br bb2
bb2:
    ret %0"""),
    ("node_only", "clean_kernel::tc::infer_cubical::node_only", "bb0(%0: ptr):\n    ret %0"),
    ("asserts", "helper::asserts", """bb0(%0: ptr):
    %1 = const bool false
    assert %1  ; #proof: no_panic
    br bb1
bb1:
    %2 = load u32, ptr %0
    %3 = const u32 1
    %4, %5 = add.overflow u32 %2, %3  ; #proof: no_overflow
    %6 = const bool false
    %7 = const bool true
    %8 = select bool %5, %6, %7
    assert %8  ; #proof: no_overflow
    br bb2
bb2:
    %9 = const bool true
    assert %9  ; #proof: no_panic
    br bb3
bb3:
    %10 = const bool false
    assert %10  ; #proof: no_panic
    unreachable"""),
    ("mix_local", "helper::mix_local", """bb0(%0: ptr):
    %1 = load struct.40, ptr %0
    %2 = const i64 8
    %3 = gep inbounds i8, ptr %0, %2
    %4 = load u64, ptr %3
    ret %0"""),
    ("mix_caller", "helper::mix_caller", """bb0(%0: ptr):
    %1 = const i64 8
    %2 = gep u8, ptr %0, %1
    %3 = call {vld}(%2)
    ret %0"""),
    ("vld", "core::ptr::read_unaligned::<core::core_arch::arm_shared::neon::uint8x8_t>",
     "bb0(%0: ptr):\n    %1 = load struct.325, ptr %0\n    ret %0"),
    ("clean_agg", "helper::clean_agg", "bb0(%0: ptr):\n    %1 = load struct.40, ptr %0\n    ret %0"),
    ("clean_byte", "helper::clean_byte", """bb0(%0: ptr):
    %1 = const i64 8
    %2 = gep inbounds i8, ptr %0, %1
    %3 = load u64, ptr %2
    ret %0"""),
    ("havoc_mix", "helper::havoc_mix", """bb0(%0: ptr):
    %1 = undef u64  ; #proof: fresh_symbolic_havoc
    %2 = gep u8, ptr %0, %1
    %3 = load struct.40, ptr %2
    ret %0"""),
    ("fam_a", "helper::fam_a", "bb0(%0: ptr):\n    %1 = call {fast}(%0)\n    ret %1"),
    ("fam_b", "helper::fam_b", "bb0(%0: ptr):\n    %1 = call {tick}(%0)\n    ret %1"),
    ("fam_c", "helper::fam_c", "bb0(%0: ptr):\n    %2 = load struct.40, ptr %0\n    ret %0"),
    ("fam_d", "helper::fam_d", "bb0(%0: ptr):\n    %2 = load struct.41, ptr %0\n    ret %0"),
    ("fam_e", "helper::fam_e", "bb0(%0: ptr):\n    %2 = load struct.42, ptr %0\n    ret %0"),
]
# infer_type calls each of these, every layout helper on an object of its own.
ROOT_CALLS = ("fast", "tick", "gate_mode", "gate_havoc", "gate_join", "prof_gate", "gate_pred",
              "gate_node", "asserts", "mix_local", "mix_caller", "clean_agg", "clean_byte",
              "havoc_mix", "fam_a", "fam_b", "fam_c", "fam_d", "fam_e")


def synth_obligations(idx, blocks):
    """The sited obligations of `helper::asserts`: a panic call at bb3#1 and an overflow check
    at the `select` feeding bb1's assert."""
    k = idx["asserts"]
    return [f'obligation 900 panic_freedom pending "panic call `core::panicking::panic` must be '
            f'unreachable" function {k} site f{k}/bb3#1',
            f'obligation 901 arithmetic_safety pending "overflow on Add" function {k} '
            f'site f{k}/bb1#{blocks}']


def synth_module(root, edit=None, extra=()):
    """Write a synthetic callee sidecar under `root`; `edit(name, body) -> body` mutates bodies,
    `extra` appends (key, name, body) functions that infer_type also calls."""
    syn = list(SYN) + list(extra)
    idx = {key: i for i, (key, _n, _b) in enumerate(syn)}
    calls = [c for c in ROOT_CALLS] + [key for key, _n, _b in extra]
    lines = ["bb0(%0: ptr):"]
    for j, c in enumerate(calls):
        if c in ("mix_local", "mix_caller", "clean_agg", "clean_byte", "havoc_mix"):
            lines.append(f"    %{100 + j} = alloca struct.40")
            lines.append(f"    %{200 + j} = call @func.{idx[c]}(%{100 + j})")
        else:
            lines.append(f"    %{200 + j} = call @func.{idx[c]}(%0)")
    lines.append("    ret %0")
    funcs = []
    for key, name, body in syn:
        b = "\n".join(lines) if key == "root" else body
        if edit:
            b = edit(key, b)
        b = re.sub(r"\{([a-z_]+)\}", lambda m: f"@func.{idx[m.group(1)]}", b)
        funcs.append((name, b))
    edges = {}
    for i, (_n, b) in enumerate(funcs):
        edges[i] = sorted({int(x) for x in re.findall(r"call @func\.(\d+)\(", b)})

    def mut(text):
        head, sep, rest = text.partition('module "clean_kernel::callees"\n')
        text = head + sep + "\n".join(SYN_ROWS) + "\n" + rest
        return text + "\n".join(synth_obligations(idx, 5)) + "\n"

    return ex.synth_artifact(root, funcs=funcs, edges=edges, mutate_text=mut)


def _measure_synth(tmp, name="s1", edit=None, extra=()):
    d = synth_module(os.path.join(tmp, name), edit=edit, extra=extra)
    return measure([(name, d)], REPO_ROOT)


def _edge_verdict(rep, arm, stratum, callee_part):
    rows = rep["arms"][arm]["strata"]["seed_verdicts"][stratum]["edges"]
    hit = [r["verdict"] for r in rows if callee_part in r["callee"]]
    return hit[0] if len(hit) == 1 else f"<{len(hit)} rows>"


def self_test():
    results = []

    def arm(label, fn):
        try:
            fn()
            results.append((label, None))
        except AssertionError as exc:
            results.append((label, f"FAILED: {exc}"))
        except (Refusal, ex.Refusal) as exc:
            results.append((label, f"REFUSED unexpectedly: {exc}"))

    tmp = tempfile.mkdtemp(prefix="strata-selftest-")
    try:
        base = _measure_synth(tmp)
        r = base["arms"]["s1"]

        def verdicts():
            assert _edge_verdict(base, "s1", "cfg", "cubical_only") == "dominated"
            assert _edge_verdict(base, "s1", "cfg", "kan_only") == "dominated"
            assert _edge_verdict(base, "s1", "cfg", "node_only") == "dominated"
            assert _edge_verdict(base, "s1", "cfg", "deep") == "entry_gated"
            assert _edge_verdict(base, "s1", "cfg", "zfc_only") == "havoc"
            assert base["metrics"]["s1.cfg_cut.gating_edges_not_cut"] == 2, base["metrics"]
        arm("01 verdicts: dominated (switch, predicate call, exact node tag), entry_gated, havoc",
            verdicts)

        def undominated():
            assert _edge_verdict(base, "s1", "cfg", "directed_only") == "undominated"
            pr = r["strata"]["cfg_cut"]
            assert not any("directed_only" in g["callee"] for g in pr["gated"]), pr["gated"]
            assert r["denominators"]["pruned_bodies"] == r["denominators"]["closure_bodies"] - 5, \
                r["denominators"]
        arm("02 RED: a planted UNDOMINATED call (in the join block) is NOT cut", undominated)

        def undominated_control():
            rep = _measure_synth(tmp, "c2", edit=lambda k, b: b.replace(
                "bb1:\n    br bb2\nbb2:\n    %4 = call {directed_only}(%0)\n    ret %0",
                "bb1:\n    %4 = call {directed_only}(%0)\n    br bb2\nbb2:\n    ret %0")
                if k == "gate_join" else b)
            assert _edge_verdict(rep, "c2", "cfg", "directed_only") == "dominated"
            assert rep["metrics"]["c2.cfg_cut.gating_edges_not_cut"] == 1
        arm("03 control: the same call moved under the Cubical arm IS cut", undominated_control)

        def havoc_control():
            rep = _measure_synth(tmp, "c3", edit=lambda k, b: b.replace(
                "%1 = undef struct.98  ; #proof: fresh_symbolic_havoc",
                "%1 = load struct.98, ptr %0") if k == "gate_havoc" else b)
            assert _edge_verdict(rep, "c3", "cfg", "zfc_only") == "dominated"
        arm("04 control: the havoc-read tag made exact makes the ZFC edge a cut", havoc_control)

        def pred_red():
            rep = _measure_synth(tmp, "c4", edit=lambda k, b: b.replace(
                "switch %3 [ 2: bb1 3: bb2 default: bb3 ]",
                "switch %3 [ 2: bb1 4: bb2 default: bb3 ]") if k == "has_cubical" else b)
            v = _edge_verdict(rep, "c4", "cfg", "kan_only")
            assert v == "undominated", v
            summ = rep["arms"]["c4"]["strata"]["predicate_summaries"]
            assert summ and summ[0]["true_for"] == ["Classical", "Cubical"], summ
        arm("05 RED: a predicate true for Classical too is no Cubical/Directed gate", pred_red)

        def prof():
            assert _edge_verdict(base, "s1", "profiler", "HeartbeatProfiler::tick") == "dominated"
            p = r["strata"]["profiler_stratum_C0"]
            assert p["bodies"] == 1 and p["gated_edges"] == 1, p
            assert r["denominators"]["pruned_bodies"] == r["denominators"]["closure_bodies"] - 5
        arm("06 the profiler stratum is gated and reported C0, never pruned", prof)

        def asserts():
            c = r["asserts"]["closure"]["classes"]
            want = {"stand_in.unkeyed_br": 1, "genuine.check": 1, "trivial.true": 1,
                    "genuine.panic_call": 1}
            assert c == want, c
            assert base["metrics"]["s1.asserts.stand_in"] == 1
        arm("07 RED: a planted const-false assert + br is a STAND-IN; a panic call is genuine",
            asserts)

        def assert_control():
            rep = _measure_synth(tmp, "c5", edit=lambda k, b: b.replace(
                "bb3:\n    %10 = const bool false\n    assert %10  ; #proof: no_panic\n    unreachable",
                "bb3:\n    %10 = const bool false\n    assert %10  ; #proof: no_panic\n    br bb4\n"
                "bb4:\n    unreachable") if k == "asserts" else b)
            c = rep["arms"]["c5"]["asserts"]["closure"]["classes"]
            assert c.get("genuine.panic_call") == 1, c
            rep2 = _measure_synth(tmp, "c6", edit=lambda k, b: b.replace(
                "    %9 = const bool true\n    assert %9", "    %9 = const bool false\n    assert %9")
                if k == "asserts" else b)
            c2 = rep2["arms"]["c6"]["asserts"]["closure"]["classes"]
            assert c2.get("stand_in.unkeyed_br") == 2 and "trivial.true" not in c2, c2
        arm("08 keyed per SITE: the panic obligation follows its assert; a const-true made false "
            "is a stand-in", assert_control)

        def families():
            keys = {}
            a = Arm("k", os.path.join(tmp, "s1"))
            names = {a.funcs[k]["name"]: k for k in range(len(a.funcs))}
            fk = family_keys(a, set(range(len(a.funcs))))
            for key in ("fam_a", "fam_b", "fam_c", "fam_d", "fam_e"):
                keys[key] = fk[names[f"helper::{key}"]]
            assert keys["fam_a"] == keys["fam_b"], "callee ids must be abstracted"
            assert keys["fam_c"][0] == keys["fam_d"][0], "type ids must be abstracted in shape"
            assert keys["fam_c"][1] != keys["fam_d"][1], \
                "two instances whose rows (hence encoding rows) differ share an enc key"
            assert keys["fam_c"][1] == keys["fam_e"][1], "identical rows under two ids split"
        arm("09 RED: instances differing only in type rows get different enc keys", families)

        def mixing():
            m = r["layout_mixing"]
            assert m["sites"] and m["sites"][0]["neon_group_probe"], m["sites"][:1]
            assert m["sites"][0]["byte_step_in"].endswith("mix_caller"), m["sites"][0]
            objs = {o["object_type"]: o for o in m["objects"]}
            assert "S" in objs and objs["S"]["functions"] >= 1, objs
            assert not any("clean_agg" in o["example"] or "clean_byte" in o["example"]
                           for o in m["objects"]), m["objects"]
            assert m["havoc_offset"]["sites"] == 1, m["havoc_offset"]
            assert not any("havoc_mix" in x["function"] for x in m["sites"])
        arm("10 mixing: the NEON probe first, a local mixed object, clean controls and a havoc "
            "offset kept apart", mixing)

        def mixing_red():
            rep = _measure_synth(tmp, "c7", edit=lambda k, b: b.replace(
                "%1 = load struct.40, ptr %0\n    ret %0",
                "%1 = load struct.40, ptr %0\n    %2 = const i64 8\n    %3 = gep inbounds i8, "
                "ptr %0, %2\n    %4 = load u64, ptr %3\n    ret %0") if k == "clean_agg" else b)
            assert rep["metrics"]["c7.layout_mixing.roots"] > base["metrics"]["s1.layout_mixing.roots"]
        arm("11 RED: a byte-offset access added to the clean aggregate object is mixing", mixing_red)

        def ratchet():
            bp = os.path.join(tmp, "baseline.json")
            write_baseline(bp, base, [_history_entry("init", "self-test", base)])
            b = load_baseline(bp)
            code, _l = compare(b, base)
            assert code == EXIT_PASS, "a baseline fails against its own measurement"
            planted = _measure_synth(tmp, "s1", extra=[(
                "planted", "helper::planted_standin",
                "bb0(%0: ptr):\n    %1 = const bool false\n    assert %1\n    br bb1\nbb1:\n    ret %0")])
            code, lines = compare(b, planted)
            assert code == EXIT_FAIL and any("asserts.stand_in" in x and "WORSE" in x for x in lines), lines
            gate = _measure_synth(tmp, "s1", extra=[(
                "planted_gate", "clean_kernel::tc::infer_zfc::planted", "bb0(%0: ptr):\n    ret %0")])
            code, lines = compare(b, gate)
            assert code == EXIT_FAIL and any("gating_edges_not_cut" in x and "WORSE" in x
                                             for x in lines), lines
            # hand edits: payload, then a re-sealed lowered metric
            doc = json.load(open(bp))
            doc["metrics"]["s1.asserts.stand_in"] = 0
            json.dump(doc, open(bp, "w"))
            try:
                load_baseline(bp)
                raise AssertionError("a hand-edited baseline was accepted")
            except Refusal:
                pass
            doc["history"][-1]["metrics"] = dict(doc["metrics"])
            json.dump(doc, open(bp, "w"))
            try:
                load_baseline(bp)
                raise AssertionError("a baseline edited consistently but not re-digested was accepted")
            except Refusal as exc:
                assert "payload digest" in str(exc), exc
            doc["history"][-1]["metrics"] = dict(base["metrics"])
            doc["payload_sha256"] = _payload_digest(doc)
            json.dump(doc, open(bp, "w"))
            try:
                load_baseline(bp)
                raise AssertionError("a baseline whose history disagrees was accepted")
            except Refusal:
                pass
            doc["history"][-1]["metrics"] = doc["metrics"]
            doc["payload_sha256"] = _payload_digest(doc)
            json.dump(doc, open(bp, "w"))
            code, lines = compare(load_baseline(bp), base)
            assert code == EXIT_FAIL and "OWN artifacts" in lines[-1], lines[-1]
        arm("12 ratchet: at baseline passes; a planted stand-in and a planted undominated gate "
            "FAIL; hand edits refused; a better-than-its-artifact baseline FAILS", ratchet)

        def anchors():
            rep = {"identity": {"manifest_sha256": "0" * 64, "text_sha256": "0" * 64},
                   "denominators": {}, "asserts": {}}
            try:
                check_dp_anchor("dp", rep)
                raise AssertionError("a dp arm that is not the anchor was accepted")
            except Refusal:
                pass
            rep["identity"] = {"manifest_sha256": DP_ANCHOR["manifest_sha256"],
                               "text_sha256": DP_ANCHOR["text_sha256"]}
            rep["denominators"] = {"closure_bodies": 2507, "closure_instructions": 249535}
            try:
                check_dp_anchor("dp", rep)
                raise AssertionError("an unreproduced denominator was accepted")
            except Refusal as exc:
                assert "NOT REPRODUCED" in str(exc)
        arm("13 REFUSED: a dp arm off the anchor, or one whose closure is not 2,508 / 249,535",
            anchors)

        def sources_red():
            src = open(os.path.join(REPO_ROOT, KIND_RS), encoding="utf-8").read()
            assert expr_kind_variants(src)[11:13] == ["SProp", "Squash"]
            for bad in (src.replace("    SProp,", "    #[cfg(feature = \"x\")]\n    SProp,", 1),
                        src.replace("    SProp,", "    SProp = 40,", 1)):
                try:
                    expr_kind_variants(bad)
                    raise AssertionError("a variant list whose order is not the tag was read")
                except Refusal:
                    pass
            fake = os.path.join(tmp, "repo")
            os.makedirs(os.path.join(fake, "data"), exist_ok=True)
            inv = json.load(open(os.path.join(REPO_ROOT, E4_INVENTORY)))
            inv["exclusion_preconditions"][E4_PRECONDITION]["statement"] = "mode is Lean"
            json.dump(inv, open(os.path.join(fake, E4_INVENTORY), "w"))
            try:
                check_e4_anchor(fake)
                raise AssertionError("E4 no longer stating the predicate was accepted")
            except Refusal:
                pass
        arm("14 REFUSED: a cfg-gated or explicitly numbered ExprKind variant; E4's statement moved",
            sources_red)

        def range_red():
            try:
                _measure_synth(tmp, "c8", edit=lambda k, b: b.replace("[ 14: bb1", "[ 99: bb1")
                               if k == "gate_node" else b)
                raise AssertionError("a switch naming no ExprKind variant was accepted")
            except Refusal as exc:
                assert "outside its" in str(exc), exc
        arm("15 REFUSED: a switch on an ExprKind tag with a case outside the enum", range_red)

        def ws43():
            d = os.path.join(tmp, "q1")
            synth_module(d)
            for fn in ("clean_kernel.callees.trust-ir.txt",):
                p = os.path.join(d, "callees", fn)
                t = tir_symbols.respell_ws43(open(p).read())
                open(p, "w").write(t)
                mp = os.path.join(d, "callees", "clean_kernel.callees.manifest.json")
                man = json.load(open(mp))
                man["artifacts"]["text_bytes"] = len(t.encode())
                json.dump(man, open(mp, "w"))
            rep = measure([("q1", d)], REPO_ROOT)
            strip = {k.split(".", 1)[1]: v for k, v in rep["metrics"].items()}
            want = {k.split(".", 1)[1]: v for k, v in base["metrics"].items()}
            assert strip == want, (strip, want)
        arm("16 a WS4.3 (quoted-symbol) printing of the same module measures the same", ws43)

        def obligations():
            long = "x" * 200000 + '\\"' + "y" * 10
            lines = [f'obligation 1 panic_freedom pending "panic call {long} must" function 0 '
                     f'site f0/bb0#0', 'obligation 2 panic_freedom pending "[trust-drop-glue-'
                     'assumption] drop glue" function 0 site f0/bb1#2']
            sited, _u = read_obligations(lines)
            assert sited[(0, "bb0", 0)] == ["panic_call"] and \
                sited[(0, "bb1", 2)] == ["assume.drop_glue"], dict(sited)
        arm("17 obligations: a long escaped description is read linearly and classed", obligations)

        def loop_havoc():
            body = """bb0(%0: ptr):
    %1 = load struct.98, ptr %0
    br bb1(%1)
bb1(%2: struct.98):
    %3 = extractfield isize %2, 0
    %4 = const bool true
    condbr %4, bb2, bb4
bb2:
    br bb3(%2)
bb3(%6: struct.98):
    %7 = copy struct.98 %6
    br bb1(%7)
bb4:
    %9 = undef struct.98  ; #proof: fresh_symbolic_havoc
    br bb3(%9)"""
            d = synth_module(os.path.join(tmp, "lp"), extra=[("loop", "helper::loop", body)])
            a = Arm("lp", d)
            k = next(i for i, f in enumerate(a.funcs) if f["name"] == "helper::loop")
            return_summaries(a, a.reach())
            fv = FuncView(a, k)
            assert fv.havoc(7) and fv.havoc(2) and fv.havoc(3), \
                "an undef reaching a loop's block parameter round the back edge was lost"
        arm("18 havoc provenance is a fixpoint: an undef entering a loop late still reaches the "
            "header's parameter", loop_havoc)
    except (Refusal, ex.Refusal) as exc:
        results.append(("synthetic base measurement", f"REFUSED: {exc}"))
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    failed = [(label, why) for label, why in results if why]
    for label, why in results:
        print(f"  {'ok  ' if not why else 'FAIL'} {label}" + (f"\n       {why}" if why else ""))
    print(f"SELFTEST={'ok' if not failed else 'FAIL'} arms={len(results)} failed={len(failed)}")
    return EXIT_PASS if not failed else EXIT_FAIL


if __name__ == "__main__":
    sys.exit(main())
