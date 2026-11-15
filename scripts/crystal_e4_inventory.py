#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0

"""Crystal E4 / R0: the deployed conversion+inference inventory, as a ratchet.

    python3.14 scripts/crystal_e4_inventory.py                  # check (exit 0/1/2)
    python3.14 scripts/crystal_e4_inventory.py --summary        # counts by class
    python3.14 scripts/crystal_e4_inventory.py --refresh-lines  # rewrite drifted line numbers only
    python3.14 scripts/crystal_e4_inventory.py --self-test

WHAT IT GUARDS. `data/crystal_e4_conversion_inventory.json` maps every deployed
reduction / conversion / inference FAMILY reachable from the release
`TypeChecker::infer_type` to exactly one class:

  covered   a named constructor (or registered declaration) of the env-indexed
            target family DefEqIn / DefEqCDPIn / KernelInfersIn / TypingCtxConvIn,
            or of their successors KernelAcceptsIn / TypingCDPCtxConvIn / TypingProjIn
            and the typed-conversion KernelAcceptsTcIn / TypingTcIn
  excluded  a named exclusion precondition (configuration the represented state
            can pin, or an obligation that is stated but not discharged)
  MISSING   no constructor carries it

Each row cites file:line on BOTH sides. A row carrying `path` records whether the
deployed infer_type path TAKES the branch (`taken`), why, and its `rank`: a MISSING
row must carry one, must be taken (a branch the path does not take is `excluded`
with its reason, never MISSING), and ranks are unique. Link 4 (decision memo 2026-09-23 §5 D5,
§7, §11 item 5) must prove that a deployed Ok answer implies a derivation in a
relation that over-approximates deployed acceptance; this inventory is the list
of what that relation still lacks, keyed to source, so the list cannot rot.

WHAT IT RE-DERIVES, every run (nothing below is read back from the JSON):

 1. The FUNCTION CENSUS of every watched kernel file. Source is LEXED first
    (`blank_noncode`: comments and string/char literals blanked, line geometry
    kept), so prose naming a function never counts. Every non-`#[cfg(test)]`
    `fn` must be SCANNED (it has a site map) or UNSCANNED with a reason.
 2. The SITE SET of every scanned function: each `self.m(..)`, `self.field`,
    `self.env.m(..)`, `Self::m(..)`, `path::f(..)`, bare `f(..)`,
    `Level::X` / `Literal::X` and `ExprKind::X` token in its lexed body. The set
    must EQUAL the inventory's site map: a new token is a deployed family (or a
    new plumbing edge) that no row maps -- FAIL; a vanished token is a stale map
    -- FAIL.
 3. The CONSTRUCTOR SET of every target relation, parsed out of the Lean source
    carried inside the spec's Rust string literals. A gained constructor FAILS
    (a MISSING row may have just become coverable, or a covered row's meaning
    moved); a lost or renamed constructor that a row maps FAILS.
 4. Every CITATION: kernel anchors must sit on the cited line of the lexed file,
    inside the cited function; spec anchors (`ctor` Rel.c / `def` / `decl` /
    `absent` / `text`) must sit on the cited line. Drift FAILS and names the new
    line; `--refresh-lines` rewrites only LINE NUMBERS -- where the anchor is
    found exactly once, or (for a repeated `text` / `decl` anchor, the same
    words wherever they sit) at the nearest hit -- never a class or an anchor.

Exit 0 = inventory agrees with source; 1 = a ratchet failure (each printed);
2 = the inventory is missing or malformed, or a usage error.
"""

import argparse
import copy
import json
import os
import re
import shutil
import sys
import tempfile

INVENTORY_REL = "data/crystal_e4_conversion_inventory.json"
CLASSES = ("covered", "excluded", "MISSING")
TARGET_RELATIONS = ("DefEqIn", "DefEqCDPIn", "KernelInfersIn", "TypingCtxConvIn",
                    "KernelAcceptsIn", "TypingCDPCtxConvIn", "TypingProjIn",
                    "KernelAcceptsTcIn", "TypingTcIn")
PLUMBING = {
    "call": "a call into another SCANNED function, whose own sites carry the semantics",
    "context": "local-context bookkeeping (push/pop/open/length); no decision",
    "heartbeat": "budget ticks; exhaustion only yields false / Err / an unchanged term",
    "stats": "feature-gated instrumentation",
    "location": "error-location bookkeeping",
    "construction": "term / level / container construction or std helpers with no decision",
    "narrowing": "can only make a step decline, stay stuck, recompute, or reject -- never accept",
    "rejects": "an Err / false return path; not an acceptance",
    "config": "a configuration or cache-key field read that decides nothing by itself",
}

# Rust non-code spans (house lexer; scripts/check_add_decl_ratchet.py NONCODE_RE).
NONCODE_RE = re.compile(
    r"/\*.*?\*/"                    # block comment (non-nested)
    r"|//[^\n]*"                    # line comment
    r'|(?:b?r)(#*)"(?:.|\n)*?"\1'   # raw string   r"..."  r#"..."#
    r'|b?"(?:\\.|[^"\\])*"'         # string literal
    r"|'(?:\\.|[^\\'])'",           # char literal
    re.DOTALL,
)


def blank_noncode(text):
    """Blank comments and string/char literals, preserving every newline."""
    return NONCODE_RE.sub(lambda m: "".join("\n" if c == "\n" else " " for c in m.group(0)), text)


def string_literals(text):
    """(start_offset, content, content_offset) for every string literal, in order."""
    out = []
    for m in NONCODE_RE.finditer(text):
        s = m.group(0)
        if s.startswith(("//", "/*", "'")):
            continue
        q = s.index('"')
        close = len(s) - 1 - len(m.group(1) or "")
        out.append((m.start(), s[q + 1:close], m.start() + q + 1))
    return out


def line_of(text, off):
    return text.count("\n", 0, off) + 1


class Inventory(Exception):
    """Missing/malformed inventory or unreadable source: exit 2."""


def read(repo_root, rel):
    path = os.path.join(repo_root, rel)
    try:
        with open(path, encoding="utf-8") as fh:
            return fh.read()
    except OSError as err:
        raise Inventory(f"cannot read {rel}: {err}") from err


# ── kernel side: functions and sites ────────────────────────────────────────
FN_RE = re.compile(r"\bfn\s+([A-Za-z_][A-Za-z0-9_]*)")
ATTR_CFG_RE = re.compile(r"#\[cfg\((.*)\)\]")
QUALIFIER_RE = re.compile(r"^((pub(\([^)]*\))?|const|async|unsafe|extern|default)\s*)*$")


def _cfg_of(code, fn_start):
    """The cfg tags on the attribute run directly above `fn` ('' if none)."""
    line_start = code.rfind("\n", 0, fn_start) + 1
    head = code[line_start:fn_start].strip()
    if head and not QUALIFIER_RE.match(re.sub(r"\s+", " ", head)):
        return None  # `fn` inside an expression position (a closure type etc.)
    tags = []
    end = line_start - 1
    while end > 0:
        start = code.rfind("\n", 0, end) + 1
        ln = code[start:end].strip()
        if ln.startswith("#["):
            m = ATTR_CFG_RE.search(ln)
            if m:
                tags.append(m.group(1).replace(" ", ""))
        elif ln:
            break
        end = start - 1
    return tags


def rust_functions(code):
    """[{name, def_line, end_line, body, cfg}] for every fn item with a body."""
    out = []
    for m in FN_RE.finditer(code):
        tags = _cfg_of(code, m.start())
        if tags is None:
            continue
        brace, semi = code.find("{", m.end()), code.find(";", m.end())
        if brace < 0 or 0 <= semi < brace:
            continue
        depth, j = 0, brace
        while j < len(code):
            if code[j] == "{":
                depth += 1
            elif code[j] == "}":
                depth -= 1
                if depth == 0:
                    break
            j += 1
        out.append({"name": m.group(1), "def_line": line_of(code, m.start()),
                    "end_line": line_of(code, j), "body": code[brace:j + 1],
                    "body_line": line_of(code, brace), "cfg": tags})
    return out


def _cfg_split(body):
    parts, depth, cur = [], 0, ""
    for ch in body:
        if ch == "," and depth == 0:
            parts.append(cur)
            cur = ""
            continue
        depth += ch == "("
        depth -= ch == ")"
        cur += ch
    return parts + ([cur] if cur else [])


def _cfg_eval(expr, debug):
    """A cfg predicate under a non-test, non-kani, default-feature build."""
    for op, fold in (("not(", None), ("any(", any), ("all(", all)):
        if expr.startswith(op) and expr.endswith(")"):
            inner = expr[len(op):-1]
            if fold is None:
                return not _cfg_eval(inner, debug)
            return fold(_cfg_eval(x, debug) for x in _cfg_split(inner))
    if expr == "debug_assertions":
        return debug
    if expr in ("test", "kani") or expr.startswith("feature"):
        return False
    return True  # an unknown predicate is kept: over-including costs a census entry only


def is_test_only(tags):
    """Not compiled into any non-test build, debug or release."""
    return not any(all(_cfg_eval(t, dbg) for t in tags) for dbg in (False, True))


def function_keys(fns):
    """Key each deployed fn by name; a name defined twice gets @debug/@release."""
    names = {}
    for f in fns:
        names.setdefault(f["name"], []).append(f)
    keyed = {}
    for name, group in names.items():
        for f in group:
            if len(group) == 1:
                keyed[name] = f
            elif "debug_assertions" in f["cfg"]:
                keyed[name + "@debug"] = f
            elif "not(debug_assertions)" in f["cfg"]:
                keyed[name + "@release"] = f
            else:
                keyed[f"{name}@{f['def_line']}"] = f
    return keyed


SITE_RE = re.compile(
    r"(?<![A-Za-z0-9_])self\s*\.\s*env\s*\.\s*([a-z_][a-z0-9_]*)\s*\("
    r"|(?<![A-Za-z0-9_])self\s*\.\s*([a-z_][a-z0-9_]*)(\s*\()?"
    r"|(?<![A-Za-z0-9_])Self::([a-z_][a-z0-9_]*)\s*\("
    r"|(?<![A-Za-z0-9_:])((?:[a-z_][a-z0-9_]*::)+[a-z_][a-z0-9_]*)\s*\("
    r"|(?<![A-Za-z0-9_:])((?:Level|Literal)::[A-Za-z_][A-Za-z0-9_]*)"
    r"|(?<![A-Za-z0-9_:])ExprKind::([A-Z][A-Za-z0-9]*)"
    r"|(?<![A-Za-z0-9_:.!'])([a-z_][a-z0-9_]*)\s*\("
)
KEYWORDS = {"if", "while", "match", "for", "return", "in", "let", "fn", "move", "loop",
            "as", "else", "where", "impl", "mut", "ref", "unsafe", "cfg"}


def sites_of(body):
    toks = set()
    for m in SITE_RE.finditer(body):
        if m.group(1):
            toks.add(f"env.{m.group(1)}()")
        elif m.group(2):
            toks.add(f"self.{m.group(2)}" + ("()" if m.group(3) else ""))
        elif m.group(4):
            toks.add(f"Self::{m.group(4)}()")
        elif m.group(5):
            toks.add(m.group(5) + "()")
        elif m.group(6):
            toks.add(m.group(6))
        elif m.group(7):
            toks.add("ExprKind::" + m.group(7))
        elif m.group(8) and m.group(8) not in KEYWORDS:
            toks.add(m.group(8) + "()")
    return toks


class KernelSource:
    """Lexed kernel files, their deployed functions keyed per `function_keys`."""

    def __init__(self, repo_root):
        self.repo_root = repo_root
        self.files = {}

    def get(self, rel):
        if rel not in self.files:
            code = blank_noncode(read(self.repo_root, rel))
            fns = [f for f in rust_functions(code) if not is_test_only(f["cfg"])]
            self.files[rel] = (code, code.split("\n"), function_keys(fns))
        return self.files[rel]


# ── spec side: relations inside Rust string literals ────────────────────────
CTOR_LINE_RE = re.compile(r"^\s*\|\s*([A-Za-z_][A-Za-z0-9_']*)\s*:")


def relation_ctors(text, rel):
    """(header_line, {ctor: line}) of `inductive <rel>` in a spec file, or None."""
    lits = string_literals(text)
    head_re = re.compile(r"\binductive\s+" + re.escape(rel) + r"\b(?!')")
    for i, (_, content, coff) in enumerate(lits):
        m = head_re.search(content)
        if not m:
            continue
        ctors, chunk = {}, [(content, coff)]
        for _, nxt, noff in lits[i + 1:]:
            if not nxt.lstrip().startswith("|"):
                break
            chunk.append((nxt, noff))
        for piece, poff in chunk:
            pos = 0
            for ln in piece.split("\n"):
                cm = CTOR_LINE_RE.match(ln)
                if cm:
                    ctors.setdefault(cm.group(1), line_of(text, poff + pos))
                pos += len(ln) + 1
        return line_of(text, coff + m.start()), ctors
    return None


def spec_anchor_lines(text, kind, anchor):
    """Every line where a spec anchor of `kind` sits (empty if it does not exist)."""
    if kind in ("ctor", "absent"):
        rel, _, ctor = anchor.partition(".")
        found = relation_ctors(text, rel)
        if found is None:
            return []
        if kind == "absent":
            return [found[0]]
        return [found[1][ctor]] if ctor in found[1] else []
    if kind == "def":
        pat = re.compile(r"\bdef\s+" + re.escape(anchor) + r"\b(?!')")
        out = []
        for _, content, coff in string_literals(text):
            out.extend(line_of(text, coff + m.start()) for m in pat.finditer(content))
        return out
    if kind == "decl":
        return [line_of(text, coff) for _, content, coff in string_literals(text)
                if content.strip() == anchor]
    if kind == "text":
        return [i + 1 for i, ln in enumerate(text.split("\n")) if anchor in ln]
    raise Inventory(f"unknown spec citation kind {kind!r}")


# ── the check ───────────────────────────────────────────────────────────────
def load_inventory(repo_root):
    try:
        inv = json.loads(read(repo_root, INVENTORY_REL))
    except json.JSONDecodeError as err:
        raise Inventory(f"{INVENTORY_REL} is not JSON: {err}") from err
    for key in ("rows", "sites", "unscanned", "watched_files", "targets",
                "exclusion_preconditions"):
        if key not in inv:
            raise Inventory(f"{INVENTORY_REL} has no `{key}`")
    return inv


def _cite_ok(c, fields):
    return isinstance(c, dict) and all(
        (isinstance(c.get(f), int) and c[f] > 0) if f == "line" else bool(c.get(f))
        for f in fields)


def check(repo_root, inv, refresh=False):
    """Return (problems, fixes). `fixes` are (json-path, new_line) when refresh."""
    problems, fixes = [], []
    ks = KernelSource(repo_root)
    spec_cache = {}

    def spec_text(rel):
        if rel not in spec_cache:
            spec_cache[rel] = read(repo_root, rel)
        return spec_cache[rel]

    rows = inv["rows"]
    ids = [r.get("id") for r in rows]
    for dup in sorted({i for i in ids if ids.count(i) > 1}):
        problems.append(f"ROW: duplicate id {dup!r}")
    row_ids = set(ids)
    pre = inv["exclusion_preconditions"]

    # 3. target relation constructor sets, re-derived and compared exactly.
    for rel, t in sorted(inv["targets"].items()):
        found = relation_ctors(spec_text(t["file"]), rel)
        if found is None:
            problems.append(f"TARGET: inductive {rel} not found in {t['file']}")
            continue
        head, ctors = found
        if head != t["line"]:
            problems.append(f"TARGET: {rel} header drifted {t['file']}:{t['line']} -> {head}")
            fixes.append((("targets", rel, "line"), head))
        want = t["constructors"]
        for c in sorted(set(ctors) - set(want)):
            problems.append(f"TARGET: {rel} GAINED constructor `{c}` ({t['file']}:{ctors[c]}); "
                            f"re-review every row mapped to or MISSING from {rel}")
        for c in sorted(set(want) - set(ctors)):
            problems.append(f"TARGET: {rel} LOST constructor `{c}` (was {t['file']}:{want[c]})")
        for c in sorted(set(want) & set(ctors)):
            if want[c] != ctors[c]:
                problems.append(f"TARGET: {rel}.{c} drifted {want[c]} -> {ctors[c]}")
                fixes.append((("targets", rel, "constructors", c), ctors[c]))

    def check_spec_cite(where, c, path):
        if not _cite_ok(c, ("file", "line", "anchor", "kind")):
            problems.append(f"CITATION: {where} lost its spec citation (file/line/anchor/kind)")
            return
        lines = spec_anchor_lines(spec_text(c["file"]), c["kind"], c["anchor"])
        if not lines:
            problems.append(f"SPEC: {where}: {c['kind']} `{c['anchor']}` no longer exists in "
                            f"{c['file']}")
        elif c["line"] not in lines:
            problems.append(f"CITATION: {where}: `{c['anchor']}` is not at {c['file']}:{c['line']} "
                            f"(now {lines})")
            if len(lines) == 1 or c["kind"] in ("text", "decl"):
                # a repeated text/decl anchor is the same words wherever it sits: take the nearest
                fixes.append((path + ("line",), min(lines, key=lambda n: abs(n - c["line"]))))

    def check_kernel_cite(where, c, path):
        if not _cite_ok(c, ("file", "line", "anchor", "fn")):
            problems.append(f"CITATION: {where} lost its deployed citation (file/fn/line/anchor)")
            return
        code, lines, fns = ks.get(c["file"])
        f = fns.get(c["fn"])
        if f is None:
            problems.append(f"DEPLOYED: {where}: fn {c['fn']} not found in {c['file']}")
            return
        span = range(f["def_line"], f["end_line"] + 1)
        hits = [n for n in span if c["anchor"] in lines[n - 1]]
        if not hits:
            problems.append(f"DEPLOYED: {where}: `{c['anchor']}` no longer in lexed fn {c['fn']} "
                            f"({c['file']})")
        elif c["line"] not in hits:
            problems.append(f"CITATION: {where}: `{c['anchor']}` is not at {c['file']}:{c['line']} "
                            f"(in {c['fn']} now {hits})")
            if len(hits) == 1:
                fixes.append((path + ("line",), hits[0]))

    # rows: shape, class, citations on both sides.
    referenced = set()
    for i, r in enumerate(rows):
        rid = r.get("id", f"<row {i}>")
        cls = r.get("class")
        if cls not in CLASSES:
            problems.append(f"ROW: {rid} class {cls!r} is not one of {CLASSES}")
        check_kernel_cite(rid, r.get("deployed"), ("rows", i, "deployed"))
        spec = r.get("spec")
        check_spec_cite(rid, spec, ("rows", i, "spec"))
        for j, v in enumerate(r.get("via", [])):
            check_spec_cite(f"{rid} via[{j}]", v, ("rows", i, "via", j))
        for j, v in enumerate(r.get("evidence", [])):
            check_spec_cite(f"{rid} evidence[{j}]", v, ("rows", i, "evidence", j))
        rel = (spec or {}).get("relation")
        if (spec or {}).get("kind") in ("ctor", "absent") and \
                str(spec.get("anchor")).partition(".")[0] != rel:
            problems.append(f"ROW: {rid} cites `{spec.get('anchor')}` under relation {rel!r}")
        if cls == "covered":
            if rel not in TARGET_RELATIONS:
                problems.append(f"ROW: {rid} is covered but its relation {rel!r} is not one of "
                                f"{TARGET_RELATIONS}")
            if (spec or {}).get("kind") in ("absent", "text"):
                problems.append(f"ROW: {rid} is covered by a `{spec['kind']}` citation")
            if r.get("exclusion"):
                problems.append(f"ROW: {rid} is covered and names an exclusion")
        elif cls == "excluded":
            if r.get("exclusion") not in pre:
                problems.append(f"ROW: {rid} names unknown exclusion precondition "
                                f"{r.get('exclusion')!r}")
        elif cls == "MISSING":
            if (spec or {}).get("kind") != "absent" or rel not in TARGET_RELATIONS:
                problems.append(f"ROW: {rid} is MISSING and must cite the target relation it is "
                                f"absent from (kind `absent`, relation in {TARGET_RELATIONS})")
            if r.get("exclusion"):
                problems.append(f"ROW: {rid} is MISSING and names an exclusion")

    # path verdicts: every MISSING row is ranked and TAKEN; ranks are unique.
    ranks = {}
    for i, r in enumerate(rows):
        rid, path = r.get("id", f"<row {i}>"), r.get("path")
        if path is None:
            if r.get("class") == "MISSING":
                problems.append(f"PATH: {rid} is MISSING and carries no path verdict (taken/rank/why)")
            continue
        if not (isinstance(path, dict) and isinstance(path.get("taken"), bool)
                and isinstance(path.get("rank"), int) and path["rank"] > 0
                and isinstance(path.get("why"), str) and path["why"].strip()):
            problems.append(f"PATH: {rid} path verdict is malformed (taken bool, rank int > 0, why)")
            continue
        if r.get("class") == "MISSING" and not path["taken"]:
            problems.append(f"PATH: {rid} is MISSING but the path does not take it: exclude it "
                            f"with the reason instead")
        if r.get("class") == "covered" and not path["taken"]:
            problems.append(f"PATH: {rid} is covered but recorded as not taken")
        if path["rank"] in ranks:
            problems.append(f"PATH: {rid} and {ranks[path['rank']]} share rank {path['rank']}")
        ranks.setdefault(path["rank"], rid)

    for name, p in sorted(pre.items()):
        if p.get("kind") not in ("configuration", "obligation", "scope"):
            problems.append(f"PRECONDITION: {name} kind {p.get('kind')!r} not configuration|"
                            f"obligation|scope")
        check_spec_cite(f"precondition {name}", p.get("cite"),
                        ("exclusion_preconditions", name, "cite"))

    for j, c in enumerate(inv.get("precondition_answer", {}).get("citations", [])):
        check_spec_cite(f"precondition_answer[{j}]", c, ("precondition_answer", "citations", j))

    # 1. function census of the watched files; 2. site sets of scanned functions.
    scanned = inv["sites"]
    unscanned = inv["unscanned"]
    for rel in inv["watched_files"]:
        _, _, fns = ks.get(rel)
        for key in sorted(fns):
            fk = f"{rel}::{key}"
            if fk not in scanned and fk not in unscanned:
                problems.append(f"CENSUS: deployed fn {fk} (line {fns[key]['def_line']}) is "
                                f"neither scanned nor unscanned-with-reason: a new family?")
    for fk in sorted(set(scanned) | set(unscanned)):
        rel, _, key = fk.partition("::")
        if fk in scanned and fk in unscanned:
            problems.append(f"CENSUS: {fk} is both scanned and unscanned")
        _, _, fns = ks.get(rel)
        if key not in fns:
            problems.append(f"CENSUS: {fk} names a function the source no longer has")
            continue
        if fk in unscanned and not str(unscanned[fk]).strip():
            problems.append(f"CENSUS: unscanned {fk} gives no reason")
        if fk not in scanned:
            continue
        have = sites_of(fns[key]["body"])
        want = scanned[fk]
        for tok in sorted(have - set(want)):
            problems.append(f"SITE: {fk} has an UNMAPPED site `{tok}` -- a deployed family (or "
                            f"plumbing edge) no row maps")
        for tok in sorted(set(want) - have):
            problems.append(f"SITE: {fk} maps `{tok}`, which the lexed source no longer has")
        for tok, val in sorted(want.items()):
            vals = val if isinstance(val, list) else [val]
            if not vals:
                problems.append(f"SITE: {fk} `{tok}` maps to nothing")
            for v in vals:
                if isinstance(v, str) and v.startswith("plumbing:"):
                    if v[len("plumbing:"):] not in PLUMBING:
                        problems.append(f"SITE: {fk} `{tok}` unknown plumbing class {v!r}")
                elif v in row_ids:
                    referenced.add(v)
                else:
                    problems.append(f"SITE: {fk} `{tok}` maps to unknown row {v!r}")
    for rid in sorted(row_ids - referenced):
        problems.append(f"ROW: {rid} is referenced by no site: it is tied to no live code")
    return problems, (fixes if refresh else [])


def apply_fixes(inv, fixes):
    for path, value in fixes:
        node = inv
        for k in path[:-1]:
            node = node[k]
        node[path[-1]] = value


def dump_json(obj):
    return json.dumps(obj, indent=2, ensure_ascii=True) + "\n"


def summary(inv):
    counts = {c: 0 for c in CLASSES}
    for r in inv["rows"]:
        counts[r.get("class")] = counts.get(r.get("class"), 0) + 1
    missing = [r["id"] for r in inv["rows"] if r.get("class") == "MISSING"]
    return counts, missing


def run(repo_root, refresh=False, show_summary=False):
    try:
        inv = load_inventory(repo_root)
        problems, fixes = check(repo_root, inv, refresh)
        if refresh and fixes:
            apply_fixes(inv, fixes)
            with open(os.path.join(repo_root, INVENTORY_REL), "w", encoding="utf-8") as fh:
                fh.write(dump_json(inv))
            print(f"E4_INVENTORY: refreshed {len(fixes)} line number(s)")
            problems, _ = check(repo_root, inv)
    except Inventory as err:
        print(f"E4_INVENTORY=REFUSED {err}")
        return 2
    counts, missing = summary(inv)
    for p in problems:
        print(f"  FAIL {p}")
    verdict = "FAIL" if problems else "OK"
    print(f"E4_INVENTORY={verdict} rows={len(inv['rows'])} covered={counts['covered']} "
          f"excluded={counts['excluded']} MISSING={counts['MISSING']} "
          f"scanned_fns={len(inv['sites'])} problems={len(problems)}")
    if show_summary:
        print("MISSING: " + ", ".join(missing))
    return 1 if problems else 0


# ── self-test: mutation arms over a scratch copy of the inputs ──────────────
def _inputs(repo_root, inv):
    files = set(inv["watched_files"]) | {INVENTORY_REL}
    files |= {fk.partition("::")[0] for fk in list(inv["sites"]) + list(inv["unscanned"])}
    files |= {t["file"] for t in inv["targets"].values()}
    files |= {p["cite"]["file"] for p in inv["exclusion_preconditions"].values()}
    files |= {c["file"] for c in inv.get("precondition_answer", {}).get("citations", [])}
    for r in inv["rows"]:
        for c in [r.get("deployed"), r.get("spec")] + r.get("via", []) + r.get("evidence", []):
            if isinstance(c, dict) and c.get("file"):
                files.add(c["file"])
    return sorted(files)


def self_test(repo_root):
    inv0 = load_inventory(repo_root)
    files = _inputs(repo_root, inv0)
    work = tempfile.mkdtemp(prefix="e4inv-")
    arms, failed = [], []

    def fresh():
        root = tempfile.mkdtemp(dir=work)
        for rel in files:
            os.makedirs(os.path.dirname(os.path.join(root, rel)), exist_ok=True)
            shutil.copyfile(os.path.join(repo_root, rel), os.path.join(root, rel))
        return root

    def edit(root, rel, fn):
        path = os.path.join(root, rel)
        with open(path, encoding="utf-8") as fh:
            text = fh.read()
        new = fn(text)
        assert new != text, f"self-test mutation of {rel} changed nothing"
        with open(path, "w", encoding="utf-8") as fh:
            fh.write(new)

    def edit_inv(root, fn):
        path = os.path.join(root, INVENTORY_REL)
        with open(path, encoding="utf-8") as fh:
            inv = json.load(fh)
        fn(inv)
        with open(path, "w", encoding="utf-8") as fh:
            fh.write(dump_json(inv))

    def plant_ctor(rel_file, rel, before, planted):
        """Insert the constructor line `planted` ahead of `before` in `rel`'s block.

        The planted name must be one `rel` does NOT already have: `relation_ctors` keys
        constructors by name, so a colliding name merges into the real constructor and the arm
        stops planting a GAIN at all -- it then sees only line drift. That is how the
        TypingTcIn arm went stale when E4d gave the relation a real `k_like` (the arm's old
        planted name). Refused here, loudly, instead of passing or failing for the wrong reason.
        """
        name = CTOR_LINE_RE.match(planted).group(1)

        def mutate(root):
            with open(os.path.join(root, rel_file), encoding="utf-8") as fh:
                have = relation_ctors(fh.read(), rel)
            assert have is not None, f"self-test: inductive {rel} not found in {rel_file}"
            assert name not in have[1], (
                f"self-test: the planted constructor `{name}` is already a constructor of "
                f"{rel} ({rel_file}:{have[1].get(name)}); plant a name the relation does not have")
            edit(root, rel_file, lambda t: t.replace(before, planted + "\n" + before, 1))
        return mutate

    def arm(name, want, mutate=None, needle=None, refresh=False):
        root = fresh()
        if mutate:
            mutate(root)
        out_path = os.path.join(root, "out.txt")
        saved = sys.stdout
        with open(out_path, "w", encoding="utf-8") as fh:
            sys.stdout = fh
            try:
                got = run(root, refresh=refresh)
            finally:
                sys.stdout = saved
        with open(out_path, encoding="utf-8") as fh:
            text = fh.read()
        ok = got == want and (needle is None or needle in text)
        arms.append(name)
        if not ok:
            failed.append(f"{name}: exit {got} (want {want}); needle {needle!r}; output:\n{text}")

    core = "crates/clean-kernel/src/tc/def_eq/mod.rs"
    host = "        let a_n = self.whnf_core_no_delta(a, true);"
    defeq = "crates/clean-verify/src/spec/core_spec/acceptance_in.rs"
    wh3 = "crates/clean-verify/src/spec/core_spec/semantic_wh3_soundness_in.rs"
    accepts = "crates/clean-verify/src/spec/core_spec/acceptance_cdp_in/inference.rs"

    # Arms that must PASS edit in place (same line) or append after the last item, so
    # no citation moves: line drift is itself a failure, and is armed separately below.
    def on_host_line(tail):
        return lambda root: edit(root, core, lambda t: t.replace(host, host + tail, 1))

    def append_to(rel, tail):
        return lambda root: edit(root, rel, lambda t: t + tail)

    arm("baseline: the real inventory agrees with the real tree", 0)
    arm("a new self.method call in is_def_eq_core is an UNMAPPED site", 1,
        on_host_line(" if self.try_new_family(a, b) { return true; }"),
        "UNMAPPED site `self.try_new_family()`")
    arm("the same call inside a // comment is prose, not a site", 0,
        on_host_line(" // if self.try_new_family(a, b) { return true; }"))
    arm("the same call inside a block comment is prose", 0,
        on_host_line(" /* self.try_new_family(a, b) */"))
    arm("the same call inside a string literal is data, not a site", 0,
        on_host_line(' let _probe = "self.try_new_family(a, b)";'))
    arm("a new ExprKind arm token is an UNMAPPED site", 1,
        on_host_line(" if matches!(a.kind(), ExprKind::NewNode) { return true; }"),
        "UNMAPPED site `ExprKind::NewNode`")
    arm("a new bare helper call is an UNMAPPED site", 1,
        on_host_line(" if new_free_rule(a, b) { return true; }"),
        "UNMAPPED site `new_free_rule()`")
    arm("a removed call leaves a STALE site map", 1,
        lambda root: edit(root, core, lambda t: t.replace(
            "if self.is_def_eq_unit_like(&t_n, &s_n) {", "if false {", 1)),
        "no longer has")
    arm("a new deployed fn in a watched file fails the census", 1,
        append_to(core, "\nimpl<'env> TypeChecker<'env> {\n    fn fresh_family(&self) -> bool { true }\n}\n"),
        "fresh_family")
    arm("a #[cfg(test)] fn is not deployed and needs no row", 0,
        append_to(core, "\nimpl<'env> TypeChecker<'env> {\n    #[cfg(test)]\n    fn test_only_probe(&self) -> bool { true }\n}\n"))
    arm("a fn under cfg(any(debug_assertions, test)) IS deployed (debug) and needs a row", 1,
        append_to(core, "\nimpl<'env> TypeChecker<'env> {\n    #[cfg(any(debug_assertions, test))]\n    fn debug_probe(&self) -> bool { true }\n}\n"),
        "debug_probe")
    arm("a fn mentioned only in a comment is not a fn", 0,
        append_to(core, "\n// fn fresh_family(&self) -> bool { true }\n"))
    arm("a renamed target constructor is caught", 1,
        lambda root: edit(root, defeq, lambda t: t.replace("| levels : forall", "| levels2 : forall", 1)),
        "LOST constructor `levels`")
    arm("a renamed constructor of the successor KernelAcceptsIn is caught", 1,
        lambda root: edit(root, accepts, lambda t: t.replace("| app : forall", "| app2 : forall", 1)),
        "LOST constructor `app`")
    arm("a GAINED constructor of the declarative TypingProjIn forces re-review", 1,
        plant_ctor(accepts, "TypingProjIn",
                   "| lit_nat : forall (G : ListType KExpr) (n : Nat), TypingProjIn",
                   "| eta : forall (G : ListType KExpr) (n : Nat), TypingProjIn R tenv G (literal_nat n) literal_nat_type"),
        "GAINED constructor `eta`")
    arm("a removed KernelAcceptsIn soundness declaration a row cites is caught", 1,
        lambda root: edit(root, accepts, lambda t: t.replace(
            '"kernel_accepts_in_sound"', '"kernel_accepts_in_sound_renamed"', 1)),
        "no longer exists")
    arm("a GAINED target constructor forces re-review", 1,
        plant_ctor(defeq, "DefEqIn",
                   "| raw : forall (e : KExpr) (e' : KExpr), par_reduces_cd R e e' -> DefEqIn R e e'",
                   "| eta : forall (e : KExpr), DefEqIn R e e"),
        "GAINED constructor `eta`")
    arm("a removed registered declaration a row cites is caught", 1,
        lambda root: edit(root, wh3, lambda t: t.replace(
            '"whnf_fuel_red_wh3_sound_in"', '"whnf_fuel_red_wh3_sound_in_renamed"')),
        "no longer exists")
    arm("a row that loses its deployed line loses its citation", 1,
        lambda root: edit_inv(root, lambda inv: inv["rows"][0]["deployed"].pop("line")),
        "lost its deployed citation")
    arm("a row that loses its spec anchor loses its citation", 1,
        lambda root: edit_inv(root, lambda inv: inv["rows"][0]["spec"].pop("anchor")),
        "lost its spec citation")
    arm("an invalid class is refused", 1,
        lambda root: edit_inv(root, lambda inv: inv["rows"][0].update({"class": "covered-ish"})),
        "is not one of")
    arm("a covered row must map into a target relation", 1,
        lambda root: edit_inv(root, lambda inv: next(
            r for r in inv["rows"] if r["class"] == "covered")["spec"].update(
                {"relation": "DefEq"})),
        "is not one of")
    arm("an excluded row must name a known precondition", 1,
        lambda root: edit_inv(root, lambda inv: next(
            r for r in inv["rows"] if r["class"] == "excluded").update({"exclusion": "nope"})),
        "unknown exclusion precondition")
    arm("a MISSING row cannot be quietly relabelled covered by a text citation", 1,
        lambda root: edit_inv(root, lambda inv: next(
            r for r in inv["rows"] if r["class"] == "MISSING").update({"class": "covered"})),
        "is covered by a `absent` citation")
    typed = "crates/clean-verify/src/spec/core_spec/acceptance_cdp_in/typed_relations.rs"
    arm("a renamed constructor of the typed-conversion KernelAcceptsTcIn is caught", 1,
        lambda root: edit(root, typed, lambda t: t.replace("| proof_irrel : forall", "| proof_irrel2 : forall", 1)),
        "LOST constructor `proof_irrel`")
    # The planted name was `k_like` until E4d made `k_like` a REAL constructor of TypingTcIn;
    # the arm then planted a duplicate, saw only line drift, and failed for the wrong reason.
    arm("a GAINED constructor of the typed-conversion TypingTcIn forces re-review", 1,
        plant_ctor(typed, "TypingTcIn",
                   "| lit_zero : forall (G : ListType CtxEntryIn), TypingTcIn",
                   "| gained_probe : forall (G : ListType CtxEntryIn), TypingTcIn R tenv Bool.false G (literal_nat Nat.zero) (literal_nat Nat.zero)"),
        "GAINED constructor `gained_probe`")
    arm("a MISSING row without a path verdict is refused", 1,
        lambda root: edit_inv(root, lambda inv: next(
            r for r in inv["rows"] if r["class"] == "MISSING").pop("path")),
        "carries no path verdict")
    arm("a MISSING row the path does not take is refused (exclude it instead)", 1,
        lambda root: edit_inv(root, lambda inv: next(
            r for r in inv["rows"] if r["class"] == "MISSING")["path"].update({"taken": False})),
        "the path does not take it")

    def dup_rank(inv):
        ranked = [r for r in inv["rows"] if r.get("path")]
        ranked[1]["path"]["rank"] = ranked[0]["path"]["rank"]
    arm("two rows sharing a rank are refused", 1,
        lambda root: edit_inv(root, dup_rank), "share rank")
    arm("a duplicate row id is refused", 1,
        lambda root: edit_inv(root, lambda inv: inv["rows"].append(copy.deepcopy(inv["rows"][0]))),
        "duplicate id")
    def unknown_row(inv):
        site_map = next(iter(inv["sites"].values()))
        site_map[next(iter(site_map))] = "no-such-row"
    arm("a site mapped to an unknown row is refused", 1,
        lambda root: edit_inv(root, unknown_row), "unknown row")

    def orphan(inv):
        inv["rows"].append(dict(copy.deepcopy(inv["rows"][0]), id="orphan-row"))
    arm("a row no site references is tied to no live code", 1,
        lambda root: edit_inv(root, orphan), "referenced by no site")
    arm("line drift in a kernel file is caught", 1,
        lambda root: edit(root, core, lambda t: "\n" + t), "is not at")

    def drift_then_refresh(root):
        edit(root, core, lambda t: "\n" + t)
    arm("--refresh-lines repairs pure drift and the check then passes", 0,
        drift_then_refresh, "refreshed", refresh=True)
    arm("a malformed inventory is REFUSED (exit 2)", 2,
        lambda root: edit(root, INVENTORY_REL, lambda t: t[: len(t) // 2]), "REFUSED")
    arm("a missing inventory is REFUSED (exit 2)", 2,
        lambda root: os.remove(os.path.join(root, INVENTORY_REL)), "REFUSED")
    shutil.rmtree(work, ignore_errors=True)
    for f in failed:
        print(f"  ARM FAILED {f}")
    print(f"E4_INVENTORY_SELFTEST={'FAIL' if failed else 'OK'} arms={len(arms)} "
          f"failed={len(failed)}")
    return 1 if failed else 0


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--repo-root", default=os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--refresh-lines", action="store_true")
    ap.add_argument("--summary", action="store_true")
    args = ap.parse_args()
    if args.self_test:
        try:
            return self_test(args.repo_root)
        except Inventory as err:
            print(f"E4_INVENTORY_SELFTEST=REFUSED {err}")
            return 2
    return run(args.repo_root, refresh=args.refresh_lines, show_summary=args.summary)


if __name__ == "__main__":
    sys.exit(main())
