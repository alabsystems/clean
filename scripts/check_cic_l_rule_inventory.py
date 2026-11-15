#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""CIC_L rule inventory: every rule family of pinned Lean's kernel, mapped to the
specification item that states it, or recorded as not yet specified.

WHY THIS EXISTS
---------------
The proven-core plan's KR2 acceptance asks for a generator that maps each rule
family in pinned Lean 4's `src/kernel/{type_checker,inductive,quot,level}.cpp`
to a spec constructor and exits non-zero on an unmapped row. It is unit S7 of
`docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md`, and it is what "the
CIC_L specification is complete" means: an empty ratchet below.

WHAT IS DERIVED AND WHAT IS DECLARED
------------------------------------
Derived, by a parse of the pinned C++ with comments, string and character
literals and preprocessor lines blanked (a mention in prose is not a rule):

  * every function DEFINITION in the pinned files (free functions and members
    of the classes defined there), with its line span and the sha256 of those
    lines;
  * every `case` arm of every `switch` in those functions;
  * every use of a hardcoded Lean constant, resolved to the Lean name: the
    `g_*` globals the kernel builds in its `initialize_*` functions (in any
    pinned file), and a name written at its use (`mk_constant("Eq", ...)`,
    `env.get("Eq")`).

Derived, by a parse of `theories/cic_l/CICL/**/*.lean` with comments and string
literals blanked: every inductive and its constructors, every structure and
its fields, every def/abbrev and theorem, by qualified name.

Declared, in `data/cic_l_rule_inventory.json`: the FAMILIES. A row groups
upstream anchors (file, function, line range, digest) under one rule family,
names the CIC_L items that specify it and states `specified`, `partial` (with
the missing part named) or `unspecified`. Two kinds of row claim code that
states no rule, and each says why: `strategy` (the order in which rules are
tried: the whnf and definitional-equality drivers, lazy unfolding; it names the
rule rows whose steps it sequences) and `infrastructure` (caches, printers,
constructors of the C++ objects). A row is a `rule` when deleting its code
would change WHICH judgments the kernel accepts as instances of a rule, not
only how fast or in what order it finds them. Whether a named item really
specifies a family is a reading recorded by whoever wrote the row; this gate
checks that the item exists, never that it is adequate.

WHAT FAILS (exit 1)
-------------------
  (a) UNMAPPED  a function, a `case` arm, a code line of a function that rows
                split by line range, or a hardcoded-constant use that no row
                claims -- so a rule cannot be skipped silently;
  (b) ANCHOR    a pinned file is not the pinned bytes, the theory's
                `lean-toolchain` is not the pinned tag, an anchor names a
                function that is not there, or its lines or digest moved --
                so a Lean bump forces a re-map;
      SPEC      a row names a CIC_L item that does not exist with that kind in
                that file, or a constructor of a rule-carrier inductive is
                cited by no row;
      CONTROL   a cited rule-carrier constructor names no negative control
                (plan unit E6: `control: {theorem, file}`, or `{none: reason}`
                where no single deleted premise is refutable), its control is
                not a theorem `<constructor>_control` of that file stating
                `Refutes .<constructor> ...`, or a theorem of the theory
                refutes a rule whose cited constructor does not name it --
                so a rule added without a control, or a control that stops
                refuting its rule, fails;
  (c) RATCHET   the non-`specified` rule families are not exactly the set in
                `data/cic_l_rule_ratchet.json`, status for status, in either
                direction.

A missing pinned source, or a tree without the theory, is UNKNOWN (exit 3),
never green.

USAGE
-----
  scripts/check_cic_l_rule_inventory.py              self-test, then the gate
  scripts/check_cic_l_rule_inventory.py --selftest   the planted failures only
  scripts/check_cic_l_rule_inventory.py --list       one line per family
  scripts/check_cic_l_rule_inventory.py --inventory  the derived units as JSON
  scripts/check_cic_l_rule_inventory.py --anchor FILE FUNCTION [START END]
                                                     print one anchor to paste
  scripts/check_cic_l_rule_inventory.py --update     lock in a ratchet that shrank
  scripts/check_cic_l_rule_inventory.py --require-complete
                                                     also fail while the ratchet is not empty

Pure standard library; needs neither Lean nor a C++ compiler.
"""
from __future__ import annotations

import hashlib
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
MAPPING = "data/cic_l_rule_inventory.json"
RATCHET = "data/cic_l_rule_ratchet.json"
TAG = "CIC_L_RULE_INVENTORY"

STATUSES = ("specified", "partial", "unspecified")
ROW_KINDS = ("rule", "strategy", "infrastructure")
ITEM_KINDS = ("inductive", "constructor", "structure", "field", "def", "theorem")


# ── lexing ───────────────────────────────────────────────────────────────────

def _spaces(text: str) -> str:
    return "".join("\n" if ch == "\n" else " " for ch in text)


_CPP_CHAR = re.compile(r"'(?:\\.[^']*|[^'\\\n])'")


def blank_noncode_cpp(text: str) -> str:
    """C++ with comments, string/char literal bodies and preprocessor lines
    blanked, every offset and line kept."""
    out: list[str] = []
    i, n = 0, len(text)
    while i < n:
        ch = text[i]
        if text.startswith("//", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
        elif text.startswith("/*", i):
            j = text.find("*/", i + 2)
            j = n if j < 0 else j + 2
            out.append(_spaces(text[i:j]))
            i = j
        elif ch == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            end = min(j + 1, n)
            out.append('"' + _spaces(text[i + 1:end - 1]) + '"' if end - i >= 2 else _spaces(text[i:end]))
            i = end
        elif ch == "'" and (m := _CPP_CHAR.match(text, i)):
            out.append("'" + " " * (m.end() - i - 2) + "'")
            i = m.end()
        else:
            out.append(ch)
            i += 1
    lines = "".join(out).split("\n")
    continued = False
    for k, line in enumerate(lines):
        if continued or line.lstrip().startswith("#"):
            continued = line.rstrip().endswith("\\")
            lines[k] = " " * len(line)
    return "\n".join(lines)


def blank_noncode_lean(text: str) -> str:
    """Lean with `--` comments, nested `/- -/` comments and string literals
    blanked, every offset and line kept."""
    out: list[str] = []
    i, n, depth = 0, len(text), 0
    while i < n:
        if text.startswith("/-", i):
            depth, i = depth + 1, i + 2
            out.append("  ")
        elif depth:
            if text.startswith("-/", i):
                depth, i = depth - 1, i + 2
                out.append("  ")
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            end = min(j + 1, n)
            out.append(_spaces(text[i:end]))
            i = end
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


# ── the pinned C++: functions, case arms, hardcoded constants ────────────────

class ParseError(RuntimeError):
    pass


@dataclass
class Arm:
    name: str          # switch<k>/<label>+<label>
    line: int          # line of its first label


@dataclass
class Function:
    name: str          # qualified, `#k` when overloaded in its file
    start: int         # 1-based, inclusive
    end: int
    sha256: str
    arms: list[Arm] = field(default_factory=list)
    code_lines: list[int] = field(default_factory=list)
    constants: list[tuple[int, str]] = field(default_factory=list)  # (line, Lean name)


_FN_NAME = re.compile(
    r"((?:[A-Za-z_]\w*\s*::\s*)*(?:operator\s*(?:\(\s*\)|\[\s*\]|[^\s\w(]+)|~?[A-Za-z_]\w*))\s*\(")
_ACCESS = re.compile(r"\s*(?:public|private|protected)\s*:")
_CLASS = re.compile(r"(?:template\s*<[^{}]*>\s*)?(?:class|struct|union)\s+(\w+)")
_NAMESPACE = re.compile(r"(?:inline\s+)?namespace\b\s*(\w*)")
_CASE = re.compile(r"(?:case\s+((?:\w+\s*::\s*)*\w+)\s*:(?!:)|(default)\s*:(?!:))")
_SWITCH = re.compile(r"\bswitch\b")
_GLOBAL_USE = re.compile(r"\b(?:\w+\s*::\s*)?(g_\w+)\b")
_GLOBAL_INIT = re.compile(r"\b(?:\w+\s*::\s*)?(g_\w+)\s*=\s*new(?:_persistent_expr_const)?\b")
# A constant named by a literal at its use: `mk_constant("Eq", ...)`, `env.get("Eq")`.
_LITERAL_CONST = re.compile(r"\b(?:mk_constant|get|find)\s*\(\s*(name\s*[({]\s*)?(?=\")")
_STRING_AT = re.compile(r'\s*"((?:[^"\\\n]|\\.)*)"\s*(,)?')
_STRING = re.compile(r'"((?:[^"\\\n]|\\.)*)"')
CONTROL = {"if", "for", "while", "switch", "return", "catch", "sizeof"}


def _line_of(starts: list[int], offset: int) -> int:
    lo, hi = 0, len(starts) - 1
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if starts[mid] <= offset:
            lo = mid
        else:
            hi = mid - 1
    return lo + 1


def _sha_lines(raw_lines: list[str], start: int, end: int) -> str:
    return hashlib.sha256("".join(raw_lines[start - 1:end]).encode()).hexdigest()


def _match_brace(code: str, open_at: int) -> int:
    depth = 0
    for i in range(open_at, len(code)):
        if code[i] == "{":
            depth += 1
        elif code[i] == "}":
            depth -= 1
            if depth == 0:
                return i
    raise ParseError("unbalanced braces")


def _arms(code: str, starts: list[int], lo: int, hi: int) -> list[Arm]:
    arms: list[Arm] = []
    for k, m in enumerate(_SWITCH.finditer(code, lo, hi), 1):
        open_at = code.find("{", m.end())
        if open_at < 0 or open_at >= hi:
            raise ParseError(f"switch without a body at line {_line_of(starts, m.start())}")
        close_at = _match_brace(code, open_at)
        depth, i, labels, prev_end = 0, open_at + 1, [], -1
        runs: list[tuple[int, list[str]]] = []
        while i < close_at:
            ch = code[i]
            if ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
            elif depth == 0 and (lm := _CASE.match(code, i)) and (i == 0 or not (code[i - 1].isalnum() or code[i - 1] == "_")):
                label = (lm.group(1) or lm.group(2)).replace(" ", "").split("::")[-1]
                if labels and code[prev_end:i].strip() == "":
                    labels.append(label)
                else:
                    labels = [label]
                    runs.append((i, labels))
                prev_end = i = lm.end()
                continue
            i += 1
        for at, names in runs:
            arms.append(Arm(f"switch{k}/{'+'.join(names)}", _line_of(starts, at)))
    return arms


def scan_cpp(name: str, raw: str, shared: dict[str, str] | None = None) -> list[Function]:
    """Every function definition in one pinned file. `shared` resolves a global
    this file uses and another pinned file initialises."""
    code = blank_noncode_cpp(raw)
    if code.count("{") != code.count("}") or code.count("(") != code.count(")"):
        raise ParseError(f"{name}: braces or parentheses do not balance after blanking")
    raw_lines = raw.splitlines(keepends=True)
    code_lines = code.split("\n")
    starts = [0]
    for line in code_lines[:-1]:
        starts.append(starts[-1] + len(line) + 1)
    found: list[tuple[str, int, int]] = []   # (qualified name, start offset, end offset)
    stack: list[dict] = []
    stmt = paren = 0
    for i, ch in enumerate(code):
        scope = stack[-1]["kind"] if stack else "file"
        if ch == "(":
            paren += 1
        elif ch == ")":
            paren -= 1
        elif ch == "{":
            if scope in ("function", "block") or paren > 0:
                stack.append({"kind": "block"})
                continue
            header_at = stmt
            while (am := _ACCESS.match(code, header_at)):
                header_at = am.end()
            header = code[header_at:i]
            text = header.strip()
            entry = {"kind": "block"}
            if _NAMESPACE.match(text):
                entry = {"kind": "namespace"}
            elif re.fullmatch(r'extern\s*"\s*"', text):
                entry = {"kind": "namespace"}
            elif "(" not in text:
                cm = _CLASS.match(text)
                entry = {"kind": "class", "name": cm.group(1)} if cm else {"kind": "block"}
            elif not text.endswith("="):
                fm = _FN_NAME.search(text)
                if fm is None or fm.group(1) in CONTROL:
                    raise ParseError(f"{name}: cannot name the definition at line {_line_of(starts, i)}")
                classes = [e["name"] for e in stack if e["kind"] == "class"]
                qual = "::".join([*classes, re.sub(r"\s+", "", fm.group(1))])
                entry = {"kind": "function", "name": qual,
                         "start": header_at + len(header) - len(header.lstrip())}
            stack.append(entry)
        elif ch == "}":
            if not stack:
                raise ParseError(f"{name}: stray closing brace at line {_line_of(starts, i)}")
            entry = stack.pop()
            if entry["kind"] == "function":
                found.append((entry["name"], entry["start"], i))
            if not stack or stack[-1]["kind"] in ("namespace", "class"):
                stmt = i + 1
        elif ch == ";" and paren == 0 and scope in ("file", "namespace", "class"):
            stmt = i + 1
    table = {**(shared or {}), **_global_table(code, raw)}
    seen: dict[str, int] = {}
    total = {q: sum(1 for f in found if f[0] == q) for q, _, _ in found}
    functions: list[Function] = []
    for qual, lo, hi in sorted(found, key=lambda f: f[1]):
        seen[qual] = seen.get(qual, 0) + 1
        fname = qual if total[qual] == 1 else f"{qual}#{seen[qual]}"
        start, end = _line_of(starts, lo), _line_of(starts, hi)
        fn = Function(fname, start, end, _sha_lines(raw_lines, start, end))
        fn.arms = _arms(code, starts, lo, hi + 1)
        fn.code_lines = [ln for ln in range(start, end + 1) if code_lines[ln - 1].strip()]
        base = qual.split("::")[-1]
        if not base.startswith(("initialize_", "finalize_")):
            for gm in _GLOBAL_USE.finditer(code, lo, hi + 1):
                fn.constants.append((_line_of(starts, gm.start(1)), table.get(gm.group(1), gm.group(1))))
            for lm in _LITERAL_CONST.finditer(code, lo, hi + 1):
                parts, at = [], lm.end()
                while (sm := _STRING_AT.match(raw, at)):
                    parts.append(sm.group(1))
                    at = sm.end()
                    if not (lm.group(1) and sm.group(2)):
                        break
                fn.constants.append((_line_of(starts, lm.start()), ".".join(parts)))
            fn.constants.sort()
        functions.append(fn)
    return functions


def _global_table(code: str, raw: str) -> dict[str, str]:
    """`g_x = new ...("A", "B")` -> {"g_x": "A.B"}; a table entry built from no
    string literal keeps its identifier."""
    table: dict[str, str] = {}
    for m in _GLOBAL_INIT.finditer(code):
        end = code.find(";", m.end())
        parts = [s.group(1) for s in _STRING.finditer(raw, m.end(), end if end > 0 else len(raw))]
        table[m.group(1)] = ".".join(parts) if parts else m.group(1)
    return table


# ── the CIC_L theory: declarations by qualified name ────────────────────────

_LEAN_DECL = re.compile(
    r"\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*"
    r"(inductive|structure|class|def|abbrev|theorem|lemma|instance|opaque|axiom)\s+([^\s:({\[⦃]+)")
_LEAN_COMMAND = re.compile(
    r"(?:namespace|end|open|variable|section|universe|set_option|attribute|deriving|macro|syntax|"
    r"notation|import|prelude|mutual|#\w+)\b")
_LEAN_CTOR = re.compile(r"\s*\|\s*([^\s:({\[⦃|]+)")
_LEAN_FIELD = re.compile(r"(\s+)((?:[A-Za-z_][\w']*\s+)*[A-Za-z_][\w']*)\s*:(?!=)")
_KIND = {"inductive": "inductive", "structure": "structure", "class": "structure",
         "def": "def", "abbrev": "def", "instance": "def", "opaque": "def",
         "theorem": "theorem", "lemma": "theorem", "axiom": "axiom"}


def scan_lean(raw: str) -> set[tuple[str, str]]:
    """{(qualified name, kind)} declared in one Lean file."""
    items: set[tuple[str, str]] = set()
    scopes: list[str] = []
    block = None  # (kind, qualified name, seen_where, field_indent)
    for line in blank_noncode_lean(raw).split("\n"):
        stripped = line.strip()
        if not stripped:
            continue
        col0 = line[:1] not in (" ", "\t")
        dm = _LEAN_DECL.match(line)
        if col0 and (cm := re.match(r"(namespace|section|mutual|end)\b\s*(\S*)", line)):
            block = None
            if cm.group(1) == "end":
                if scopes:
                    scopes.pop()
            else:
                scopes.append(cm.group(2) if cm.group(1) == "namespace" else "")
            continue
        if dm and col0:
            kind = _KIND[dm.group(1)]
            qual = ".".join([s for s in scopes if s] + [dm.group(2)])
            items.add((qual, kind))
            block = [kind, qual, "where" in stripped.split() or stripped.endswith(":="), None] \
                if kind in ("inductive", "structure") else None
            continue
        if col0 and _LEAN_COMMAND.match(line):
            block = None
            continue
        if block is None:
            continue
        if block[0] == "inductive":
            if (km := _LEAN_CTOR.match(line)):
                items.add((f"{block[1]}.{km.group(1)}", "constructor"))
        elif not block[2]:
            block[2] = "where" in stripped.split()
        elif (fm := _LEAN_FIELD.match(line)):
            if block[3] is None:
                block[3] = fm.group(1)
            if fm.group(1) == block[3]:
                for fname in fm.group(2).split():
                    items.add((f"{block[1]}.{fname}", "field"))
    return items


def _statement(code: str, at: int) -> str:
    """The type of the declaration whose name ends at `at`: from the first `:`
    outside brackets to the first `:=` outside brackets, whitespace collapsed,
    prefixed with any binders before `:` so a parameterized helper never passes
    for a ground control theorem."""
    depth, start, i = 0, None, at
    while i < len(code):
        ch = code[i]
        if ch in "([{⦃⟨":
            depth += 1
        elif ch in ")]}⦄⟩":
            depth -= 1
        elif depth == 0 and code.startswith(":=", i):
            break
        elif depth == 0 and ch == ":" and start is None:
            start = i + 1
        i += 1
    if start is None:
        return ""
    binders = " ".join(code[at:start - 1].split())
    body = " ".join(code[start:i].split())
    return f"{binders} : {body}" if binders else body


def lean_theorem_statements(raw: str) -> dict[str, str]:
    """{qualified theorem name: its statement} in one Lean file."""
    code = blank_noncode_lean(raw)
    out: dict[str, str] = {}
    scopes: list[str] = []
    offset = 0
    for line in code.split("\n"):
        start, offset = offset, offset + len(line) + 1
        if not line.strip() or line[:1] in (" ", "\t"):
            continue
        if (cm := re.match(r"(namespace|section|mutual|end)\b\s*(\S*)", line)):
            if cm.group(1) != "end":
                scopes.append(cm.group(2) if cm.group(1) == "namespace" else "")
            elif scopes:
                scopes.pop()
            continue
        if (dm := _LEAN_DECL.match(line)) and _KIND[dm.group(1)] == "theorem":
            qual = ".".join([s for s in scopes if s] + [dm.group(2)])
            out[qual] = _statement(code, start + dm.end())
    return out


_REFUTES = re.compile(
    r"(?:CICL\.NegativeControls\.)?Refutes\s+"
    r"(?:\.|(?:CICL\.NegativeControls\.)?Rule\.)([A-Za-z_][\w']*)(?![\w'.])"
)


def control_problems(mapping: dict, theory: dict[str, str],
                     spec_items: dict[str, set[tuple[str, str]]]) -> list[str]:
    """Plan unit E6: each cited rule-carrier constructor names its negative
    control, or the reason it has none. An item that names no existing
    constructor is the SPEC check's problem and is not judged here."""
    problems: list[str] = []
    carriers = set(mapping["spec"].get("rule_carriers", []))
    statements = {rel: lean_theorem_statements(text) for rel, text in theory.items()}
    recorded: dict[str, dict] = {}
    for row in mapping.get("rows", []):
        rid = row.get("id", "<no id>")
        for item in row.get("cic_l") or []:
            name, ifile = item.get("item", ""), item.get("file")
            carrier, _, ctor = name.rpartition(".")
            if carrier not in carriers or item.get("kind") != "constructor":
                if "control" in item:
                    problems.append(f"SHAPE: {rid} gives {name} a control, and only a "
                                    f"rule-carrier constructor has one")
                continue
            if (name, "constructor") not in spec_items.get(ifile, set()):
                continue
            control = item.get("control")
            if (not isinstance(control, dict)
                    or ("theorem" in control) == ("none" in control)):
                problems.append(f"(b) CONTROL: {rid} cites {name} and names no negative control "
                                f"-- give it control {{theorem, file}}, or {{none: reason}} where "
                                f"no single deleted premise is refutable")
                continue
            recorded[ctor] = control
            if "none" in control:
                if not str(control["none"]).strip():
                    problems.append(f"(b) CONTROL: {name} records no control and no reason")
                continue
            theorem, cfile = control.get("theorem", ""), control.get("file", "")
            if theorem.rpartition(".")[2] != f"{ctor}_control":
                problems.append(f"(b) CONTROL: {name}'s control {theorem} is not named "
                                f"{ctor}_control")
            stated = statements.get(cfile, {}).get(theorem)
            if stated is None:
                problems.append(f"(b) CONTROL: {name}'s control {theorem} is no theorem of {cfile}")
            elif not (m := _REFUTES.match(stated)) or m.group(1) != ctor:
                problems.append(f"(b) CONTROL: {name}'s control {theorem} states {stated[:80]!r}, "
                                f"not `Refutes .{ctor} ...` -- a control that stops refuting its "
                                f"rule is no control")
    for rel, stmts in sorted(statements.items()):
        for theorem, stated in sorted(stmts.items()):
            if not (m := _REFUTES.match(stated)) or m.group(1) not in recorded:
                continue
            control = recorded[m.group(1)]
            if control.get("theorem") != theorem:
                problems.append(f"(b) CONTROL: {rel} theorem {theorem} refutes rule {m.group(1)}, "
                                f"whose inventory item names "
                                + (f"{control['theorem']}" if "theorem" in control
                                   else "no control"))
    return problems


# ── inputs ───────────────────────────────────────────────────────────────────

@dataclass
class Inputs:
    mapping: dict
    ratchet: dict
    sources: dict[str, str]        # pinned-file path (relative to upstream.root) -> text
    theory: dict[str, str]         # Lean path (relative to spec.root) -> text
    toolchain: str
    upstream_record: dict | None   # the fixture directory's UPSTREAM.json
    missing_sources: list[str] = field(default_factory=list)
    extra_controls: dict[str, str] = field(default_factory=dict)


def load_inputs(root: Path) -> Inputs:
    mapping = json.loads((root / MAPPING).read_text())
    ratchet = json.loads((root / RATCHET).read_text())
    up = mapping["upstream"]
    src_root = root / up["root"]
    sources, missing = {}, []
    for rel in up["files"]:
        path = src_root / rel
        if path.is_file():
            sources[rel] = path.read_bytes().decode("utf-8")
        else:
            missing.append(f"{up['root']}/{rel}")
    record_path = src_root / "UPSTREAM.json"
    record = json.loads(record_path.read_text()) if record_path.is_file() else None
    spec_root = root / mapping["spec"]["root"]
    if not spec_root.is_dir():
        missing.append(mapping["spec"]["root"])
    theory = {p.relative_to(spec_root).as_posix(): p.read_text()
              for p in sorted(spec_root.rglob("*.lean")) if ".lake" not in p.parts} \
        if spec_root.is_dir() else {}
    extra_controls: dict[str, str] = {}
    for prefix, croot_rel in (mapping["spec"].get("control_roots") or {}).items():
        if croot_rel == mapping["spec"]["root"]:
            continue
        croot = root / croot_rel
        if not croot.is_dir():
            if croot_rel not in missing:
                missing.append(croot_rel)
            continue
        for p in sorted(croot.rglob("*.lean")):
            if ".lake" in p.parts:
                continue
            rel = p.relative_to(croot).as_posix()
            if not prefix or rel.startswith(prefix):
                extra_controls[rel] = p.read_text()
    toolchain_path = root / up["toolchain_file"]
    toolchain = toolchain_path.read_text().strip() if toolchain_path.is_file() else ""
    return Inputs(mapping, ratchet, sources, theory, toolchain, record, missing, extra_controls)


# ── the check ────────────────────────────────────────────────────────────────

@dataclass
class Result:
    problems: list[str] = field(default_factory=list)
    counts: dict[str, int] = field(default_factory=dict)
    not_specified: dict[str, str] = field(default_factory=dict)
    functions: int = 0
    arms: int = 0
    constants: int = 0
    infrastructure: int = 0
    strategy: int = 0


def derive_units(inp: Inputs) -> dict[str, list[Function]]:
    shared: dict[str, str] = {}
    for text in inp.sources.values():
        shared.update(_global_table(blank_noncode_cpp(text), text))
    return {rel: scan_cpp(rel, text, shared) for rel, text in inp.sources.items()}


def check(inp: Inputs) -> Result:
    res = Result(counts={s: 0 for s in STATUSES})
    bad = res.problems.append
    mapping, up = inp.mapping, inp.mapping["upstream"]

    # (b) the pinned bytes and the pinned tag.
    for rel, pin in up["files"].items():
        if rel not in inp.sources:
            continue
        digest = hashlib.sha256(inp.sources[rel].encode()).hexdigest()
        if digest != pin.get("sha256"):
            bad(f"(b) ANCHOR: {up['root']}/{rel} is not the pinned file (sha256 {digest[:12]}, "
                f"pinned {str(pin.get('sha256'))[:12]}) -- a changed kernel source needs every "
                f"anchor in it re-read, then re-pinned")
    if inp.toolchain != f"leanprover/lean4:{up['tag']}":
        bad(f"(b) ANCHOR: {up['toolchain_file']} says {inp.toolchain!r}, and this inventory is "
            f"of tag {up['tag']} -- a Lean bump forces a re-map against the new kernel sources")
    if inp.upstream_record is not None:
        rec = inp.upstream_record
        rec_files = {f["path"]: f.get("sha256") for f in rec.get("files", [])}
        if rec.get("revision") != up.get("commit") or any(
                rec_files.get(rel) != pin.get("sha256") for rel, pin in up["files"].items()):
            bad(f"(b) ANCHOR: {up['root']}/UPSTREAM.json and {MAPPING} disagree on the pinned "
                f"commit or a file digest")

    try:
        units = derive_units(inp)
    except ParseError as exc:
        bad(f"(b) ANCHOR: the pinned source no longer parses: {exc}")
        return res
    by_name = {(rel, fn.name): fn for rel, fns in units.items() for fn in fns}
    res.functions = len(by_name)
    res.arms = sum(len(fn.arms) for fn in by_name.values())
    res.constants = sum(len(fn.constants) for fn in by_name.values())

    spec_items: dict[str, set[tuple[str, str]]] = {rel: scan_lean(text) for rel, text in inp.theory.items()}

    # Rows: shape, anchors, CIC_L items.
    covered: dict[tuple[str, str], list[tuple[int, int, dict]]] = {}
    whole: set[tuple[str, str]] = set()
    cited: set[str] = set()
    ids: set[str] = set()
    for row in mapping.get("rows", []):
        rid = row.get("id", "<no id>")
        if rid in ids:
            bad(f"SHAPE: duplicate row id {rid}")
        ids.add(rid)
        kind = row.get("kind")
        if kind not in ROW_KINDS:
            bad(f"SHAPE: {rid} kind={kind!r} is not one of {ROW_KINDS}")
            continue
        if not row.get("anchors"):
            bad(f"SHAPE: {rid} names no upstream anchor")
        for anchor in row.get("anchors", []):
            key = (anchor.get("file", ""), anchor.get("function", ""))
            fn = by_name.get(key)
            if fn is None:
                if key[0] in inp.sources or key[0] not in up["files"]:
                    bad(f"(b) ANCHOR: {rid} anchors {key[0]}:{key[1]}, which the pinned source "
                        f"does not define")
                continue
            lines = anchor.get("lines")
            if (not isinstance(lines, list) or len(lines) != 2
                    or not all(isinstance(x, int) for x in lines)
                    or not fn.start <= lines[0] <= lines[1] <= fn.end):
                bad(f"(b) ANCHOR: {rid} anchors {key[0]}:{key[1]} at lines {lines}, outside the "
                    f"function's span {fn.start}-{fn.end}")
                continue
            raw_lines = inp.sources[key[0]].splitlines(keepends=True)
            digest = _sha_lines(raw_lines, lines[0], lines[1])
            if digest != anchor.get("sha256"):
                bad(f"(b) ANCHOR: {rid} anchors {key[0]}:{key[1]} lines {lines[0]}-{lines[1]} at "
                    f"sha256 {str(anchor.get('sha256'))[:12]}, and those lines are {digest[:12]}")
            # A stale anchor still claims its lines: one cause, one message.
            covered.setdefault(key, []).append((lines[0], lines[1], row))
            if lines == [fn.start, fn.end]:
                whole.add(key)
        if kind != "rule":
            if kind == "strategy":
                res.strategy += 1
            else:
                res.infrastructure += 1
            if not str(row.get("reason", "")).strip():
                bad(f"SHAPE: {rid} is {kind} with no reason -- say why it states no rule")
            if row.get("status") is not None or row.get("cic_l"):
                bad(f"SHAPE: {rid} is {kind} and carries a status or CIC_L items")
            if (kind == "strategy") != bool(row.get("uses_rules")):
                bad(f"SHAPE: {rid} is {kind}: `uses_rules` names the rule rows whose steps a "
                    f"strategy row sequences, and belongs to no other kind")
            continue
        status = row.get("status")
        if status not in STATUSES:
            bad(f"SHAPE: {rid} status={status!r} is not one of {STATUSES}")
            continue
        res.counts[status] += 1
        if status != "specified":
            res.not_specified[rid] = status
        items = row.get("cic_l") or []
        missing = str(row.get("missing", "")).strip()
        if status == "unspecified" and items:
            bad(f"SHAPE: {rid} is unspecified and names CIC_L items -- it is partial, or the "
                f"items are `groundwork`")
        if status != "unspecified" and not items:
            bad(f"SHAPE: {rid} is {status} and names no CIC_L item")
        if (status == "partial") != bool(missing):
            bad(f"SHAPE: {rid} is {status}: `missing` names the unspecified part of a partial "
                f"row and of no other")
        ext = row.get("extension")
        if ext is not None and not isinstance((ext or {}).get("plan_requires_derived_rule"), bool):
            bad(f"SHAPE: {rid} is a kernel extension and does not say whether the plan requires "
                f"it as a derived rule")
        for item in [*items, *(row.get("groundwork") or [])]:
            name, ikind, ifile = item.get("item"), item.get("kind"), item.get("file")
            if ikind not in ITEM_KINDS:
                bad(f"SHAPE: {rid} item {name} kind={ikind!r} is not one of {ITEM_KINDS}")
            elif (name, ikind) not in spec_items.get(ifile, set()):
                bad(f"(b) SPEC: {rid} names {ikind} {name} in {ifile}, and the theory declares "
                    f"no such {ikind} there")
        cited.update(item.get("item", "") for item in items)

    # A strategy row sequences steps of rule rows that are there.
    rule_ids = {row.get("id") for row in mapping.get("rows", []) if row.get("kind") == "rule"}
    for row in mapping.get("rows", []):
        for rid in row.get("uses_rules") or []:
            if rid not in rule_ids:
                bad(f"SHAPE: {row.get('id')} says it sequences steps of {rid}, and the inventory "
                    f"has no such rule family")

    # (b) every constructor of a rule-carrier inductive is cited by a row.
    all_items = set().union(*spec_items.values()) if spec_items else set()
    for carrier in mapping["spec"].get("rule_carriers", []):
        if (carrier, "inductive") not in all_items:
            bad(f"(b) SPEC: rule carrier {carrier} is not an inductive of the theory")
        for name, ikind in sorted(all_items):
            if ikind == "constructor" and name.rsplit(".", 1)[0] == carrier and name not in cited:
                bad(f"(b) SPEC: constructor {name} of the rule carrier is cited by no row -- "
                    f"a new specification rule must be mapped to the kernel family it states")

    # (b) every cited rule-carrier constructor names its negative control.
    for problem in control_problems(mapping, {**inp.theory, **inp.extra_controls}, spec_items):
        bad(problem)

    # (a) every function, case arm, split line and hardcoded constant is claimed.
    for key, fn in sorted(by_name.items()):
        spans = covered.get(key, [])
        where = f"{key[0]}:{fn.name}"
        if not spans:
            bad(f"(a) UNMAPPED: function {where} (lines {fn.start}-{fn.end}) is claimed by no row")
            continue
        if key not in whole:
            for arm in fn.arms:
                if not any(lo <= arm.line <= hi for lo, hi, _ in spans):
                    bad(f"(a) UNMAPPED: case arm {where}/{arm.name} (line {arm.line}) is claimed "
                        f"by no row")
            loose = [ln for ln in fn.code_lines if not any(lo <= ln <= hi for lo, hi, _ in spans)]
            arm_lines = {arm.line for arm in fn.arms}
            loose = [ln for ln in loose if ln not in arm_lines]
            if loose:
                bad(f"(a) UNMAPPED: {where} is split by line range and lines "
                    f"{_ranges(loose)} are claimed by no row")
        for line, const in fn.constants:
            if not any(lo <= line <= hi and const in (row.get("constants") or [])
                       for lo, hi, row in spans):
                bad(f"(a) UNMAPPED: hardcoded constant {const} at {where} line {line} is named "
                    f"by no row anchored there")
    for row in mapping.get("rows", []):
        used = {const for anchor in row.get("anchors", [])
                for fn in [by_name.get((anchor.get("file", ""), anchor.get("function", "")))] if fn
                for line, const in fn.constants
                if isinstance(anchor.get("lines"), list) and len(anchor["lines"]) == 2
                and anchor["lines"][0] <= line <= anchor["lines"][1]}
        for const in row.get("constants") or []:
            if const not in used:
                bad(f"(b) ANCHOR: {row.get('id')} names hardcoded constant {const}, which its "
                    f"anchors do not use")

    # (c) the ratchet: exactly the non-specified families, status for status.
    pinned = inp.ratchet.get("not_specified", {})
    for rid in sorted(set(pinned) - set(res.not_specified)):
        bad(f"(c) RATCHET: {rid} is in {RATCHET} as {pinned[rid]} and "
            + ("the inventory has no such rule family" if rid not in ids else
               "the inventory now calls it specified -- remove it from the ratchet in the same "
               "change (--update)"))
    for rid in sorted(set(res.not_specified) - set(pinned)):
        bad(f"(c) RATCHET: {rid} is {res.not_specified[rid]} and is not in {RATCHET} -- the "
            f"ratchet only shrinks; a family that stopped being specified, or a new one, is "
            f"added by hand with its reason")
    for rid in sorted(set(pinned) & set(res.not_specified)):
        if pinned[rid] != res.not_specified[rid]:
            bad(f"(c) RATCHET: {rid} is {res.not_specified[rid]} and {RATCHET} records "
                f"{pinned[rid]}")
    return res


def _ranges(lines: list[int]) -> str:
    out, start, prev = [], lines[0], lines[0]
    for ln in lines[1:] + [None]:
        if ln is not None and ln == prev + 1:
            prev = ln
            continue
        out.append(str(start) if start == prev else f"{start}-{prev}")
        if ln is not None:
            start = prev = ln
    return ", ".join(out)


def summary(res: Result, unknown: str = "") -> str:
    total = sum(res.counts.values())
    verdict = "unknown" if unknown else ("fail" if res.problems else "ok")
    return (f"{TAG}={verdict} families={total} specified={res.counts['specified']} "
            f"partial={res.counts['partial']} unspecified={res.counts['unspecified']} "
            f"(upstream functions={res.functions} case_arms={res.arms} "
            f"hardcoded_constant_uses={res.constants} strategy_rows={res.strategy} "
            f"infrastructure_rows={res.infrastructure})"
            + (f" problems={len(res.problems)}" if res.problems else ""))


def completeness(res: Result) -> str:
    total, open_ = sum(res.counts.values()), len(res.not_specified)
    if open_ == 0:
        return ("KR2's inventory acceptance holds: every rule family of the pinned kernel "
                "sources maps to a CIC_L item and the ratchet is empty.")
    return (f"The CIC_L specification is INCOMPLETE: {open_} of {total} rule families are not "
            f"specified ({res.counts['partial']} partial, {res.counts['unspecified']} "
            f"unspecified). KR2's inventory acceptance does not hold.")


# ── self-test: planted failures on a synthetic kernel and theory ────────────

_ST_CPP = '''/* A comment that names a function: void ghost(int x) { switch (x) { case 9: break; } } */
namespace lean {
static name * g_nat_add = nullptr;
// case expr_kind::Ghost: is prose, never an arm
expr checker::infer(expr const & e) {
    switch (e.kind()) {
    case expr_kind::Sort:
        return mk_sort("{ case expr_kind::InString: }");
    case expr_kind::Pi: case expr_kind::Lambda:
        return infer_binding(e);
    }
    return e;
}
bool checker::is_add(expr const & f) {
    return f == *g_nat_add;
}
class helper {
    unsigned m_next{1};
public:
    helper(int x):
        m_x(x) {}
    bool cached(int a) { return a == '}'; }
};
void initialize_checker() {
    g_nat_add = new expr(mk_const({"Nat", "add"}));
}
}
'''

_ST_LEAN = '''/- A doc comment naming a constructor:
  | ghost : Judgment
-/
namespace Spec
inductive Judgment : Prop where
  | sort : Judgment
  -- | commented : Judgment
  | pi : Judgment
structure Admission where
  typed : Prop
theorem sort_ok : True := trivial
end Spec
'''

_ST_CONTROLS = '''namespace Spec
inductive Rule where
  | sort
  | pi
def Refutes (r : Rule) (s : Prop) : Prop := s
/- theorem pi_control : Refutes .pi True := trivial -/
theorem sort_control :
    Refutes .sort True := trivial
end Spec
'''


def _st_inputs() -> Inputs:
    cpp = {"k/checker.cpp": _ST_CPP}
    fns = {fn.name: fn for fn in scan_cpp("k/checker.cpp", _ST_CPP)}
    raw_lines = _ST_CPP.splitlines(keepends=True)

    def anchor(fname: str, lo: int | None = None, hi: int | None = None) -> dict:
        fn = fns[fname]
        lo, hi = lo or fn.start, hi or fn.end
        return {"file": "k/checker.cpp", "function": fname, "lines": [lo, hi],
                "sha256": _sha_lines(raw_lines, lo, hi)}

    infer = fns["checker::infer"]
    sort_line = next(a.line for a in infer.arms if a.name == "switch1/Sort")
    pi_line = next(a.line for a in infer.arms if a.name == "switch1/Pi+Lambda")
    mapping = {
        "upstream": {"tag": "v0", "commit": "c0", "root": "fx", "toolchain_file": "tc",
                     "files": {"k/checker.cpp": {"sha256": hashlib.sha256(_ST_CPP.encode()).hexdigest()}}},
        "spec": {"root": "th", "rule_carriers": ["Spec.Judgment"]},
        "rows": [
            {"id": "sort", "kind": "rule", "status": "specified",
             "anchors": [anchor("checker::infer", infer.start, pi_line - 1)],
             "cic_l": [{"item": "Spec.Judgment.sort", "kind": "constructor", "file": "S.lean",
                        "control": {"theorem": "Spec.sort_control", "file": "C.lean"}}]},
            {"id": "binding", "kind": "rule", "status": "partial", "missing": "lambda",
             "anchors": [anchor("checker::infer", pi_line, infer.end)],
             "cic_l": [{"item": "Spec.Judgment.pi", "kind": "constructor", "file": "S.lean",
                        "control": {"none": "sound without any one premise"}}]},
            {"id": "nat-add", "kind": "rule", "status": "unspecified", "constants": ["Nat.add"],
             "extension": {"class": "nat-literal", "plan_requires_derived_rule": True},
             "anchors": [anchor("checker::is_add")]},
            {"id": "search", "kind": "strategy", "reason": "decides which rule is tried first",
             "uses_rules": ["sort", "binding"], "anchors": [anchor("helper::cached")]},
            {"id": "objects", "kind": "infrastructure", "reason": "C++ object plumbing",
             "anchors": [anchor("helper::helper"), anchor("initialize_checker")]},
        ],
    }
    if not sort_line < pi_line:
        raise ParseError("self-test fixture: the Sort arm must precede the Pi arm")
    ratchet = {"not_specified": {"binding": "partial", "nat-add": "unspecified"}}
    return Inputs(mapping, ratchet, cpp, {"S.lean": _ST_LEAN, "C.lean": _ST_CONTROLS},
                  "leanprover/lean4:v0", None)


def selftest(out=sys.stdout) -> int:
    failures: list[str] = []
    arms = 0

    def arm(label: str, expect: str, mutate) -> None:
        nonlocal arms
        arms += 1
        inp = _st_inputs()
        mutate(inp)
        problems = check(inp).problems
        if expect == "":
            if problems:
                failures.append(f"{label}: expected GREEN, got {problems}")
        elif not problems:
            failures.append(f"{label}: stayed GREEN under its own mutation")
        elif not all(expect in p for p in problems):
            failures.append(f"{label}: expected only {expect!r}, got {problems}")

    def repin(inp: Inputs) -> None:
        text = inp.sources["k/checker.cpp"]
        inp.mapping["upstream"]["files"]["k/checker.cpp"]["sha256"] = hashlib.sha256(text.encode()).hexdigest()

    def rows(inp: Inputs) -> dict:
        return {row["id"]: row for row in inp.mapping["rows"]}

    def drop_row(rid: str):
        def go(inp: Inputs) -> None:
            inp.mapping["rows"] = [r for r in inp.mapping["rows"] if r["id"] != rid]
            inp.ratchet["not_specified"].pop(rid, None)
        return go

    def new_function(inp: Inputs) -> None:
        inp.sources["k/checker.cpp"] += "bool lean_new_rule(int a) {\n    return a > 0;\n}\n"
        repin(inp)

    def drop_arm(inp: Inputs) -> None:
        row = rows(inp)["binding"]
        fn = next(f for f in scan_cpp("k/checker.cpp", _ST_CPP) if f.name == "checker::infer")
        lo = row["anchors"][0]["lines"][0] + 1
        row["anchors"][0]["lines"] = [lo, fn.end]
        row["anchors"][0]["sha256"] = _sha_lines(_ST_CPP.splitlines(keepends=True), lo, fn.end)

    def edit_body(inp: Inputs) -> None:
        inp.sources["k/checker.cpp"] = inp.sources["k/checker.cpp"].replace(
            "return f == *g_nat_add;", "return f != *g_nat_add;")
        repin(inp)

    def comment_out_constructor(inp: Inputs) -> None:
        inp.theory["S.lean"] = inp.theory["S.lean"].replace("  | pi : Judgment", "  -- | pi : Judgment")

    def new_constructor(inp: Inputs) -> None:
        inp.theory["S.lean"] = inp.theory["S.lean"].replace(
            "  | pi : Judgment", "  | pi : Judgment\n  | proj : Judgment")

    def set_status(rid: str, status: str, also_ratchet: bool = False):
        def go(inp: Inputs) -> None:
            row = rows(inp)[rid]
            row["status"] = status
            if status != "partial":
                row.pop("missing", None)
            if also_ratchet:
                if status == "specified":
                    inp.ratchet["not_specified"].pop(rid, None)
                else:
                    inp.ratchet["not_specified"][rid] = status
        return go

    arm("00 control: the synthetic inventory is green", "", lambda inp: None)
    # (a) a family has no row
    arm("01 (a) a row is deleted and its function is unclaimed", "(a) UNMAPPED: function",
        drop_row("nat-add"))
    arm("02 (a) the pinned source gains a function no row claims", "(a) UNMAPPED: function",
        new_function)
    arm("03 (a) a case arm falls outside every anchor", "(a) UNMAPPED: case arm", drop_arm)
    arm("04 (a) a hardcoded constant no row names", "(a) UNMAPPED: hardcoded constant",
        lambda inp: rows(inp)["nat-add"].pop("constants"))
    # (b) a missing CIC_L item, a missing or changed upstream anchor
    arm("05 (b) a row names a constructor that is not there", "(b) SPEC",
        lambda inp: rows(inp)["sort"]["cic_l"][0].update(item="Spec.Judgment.ghost"))
    arm("06 (b) the constructor survives only in a comment", "(b) SPEC", comment_out_constructor)
    arm("07 (b) a new rule-carrier constructor is cited by no row", "(b) SPEC: constructor",
        new_constructor)
    arm("08 (b) an anchor names a function that is not there", "(b) ANCHOR",
        lambda inp: rows(inp)["objects"]["anchors"].append(
            {"file": "k/checker.cpp", "function": "helper::ghost", "lines": [1, 1], "sha256": ""}))
    arm("09 (b) an anchored function's body changed", "(b) ANCHOR", edit_body)
    arm("10 (b) a pinned file is not the pinned bytes", "(b) ANCHOR",
        lambda inp: inp.sources.update({"k/checker.cpp": _ST_CPP + "\n"}))
    arm("11 (b) the theory's toolchain is another tag", "(b) ANCHOR",
        lambda inp: setattr(inp, "toolchain", "leanprover/lean4:v1"))
    # (c) the ratchet, in both directions
    arm("12 (c) a family became specified and stayed in the ratchet", "(c) RATCHET",
        set_status("binding", "specified"))
    arm("13 (c) the same change with the ratchet shrunk is green", "",
        set_status("binding", "specified", also_ratchet=True))
    arm("14 (c) a specified family regressed outside the ratchet", "(c) RATCHET",
        lambda inp: rows(inp)["sort"].update(status="partial", missing="x"))
    arm("15 (c) a recorded status disagrees", "(c) RATCHET",
        lambda inp: inp.ratchet["not_specified"].update({"binding": "unspecified"}))
    # shape
    arm("16 a partial row that names no missing part", "SHAPE",
        lambda inp: rows(inp)["binding"].pop("missing"))
    arm("17 an extension row silent on the derived-rule requirement", "SHAPE",
        lambda inp: rows(inp)["nat-add"].update(extension={"class": "nat-literal"}))
    arm("17b a strategy row that sequences a rule family that is not there", "SHAPE",
        lambda inp: rows(inp)["search"].update(uses_rules=["sort", "ghost"]))
    arm("17c an infrastructure row with no reason", "SHAPE",
        lambda inp: rows(inp)["objects"].pop("reason"))
    # (b) negative controls (plan unit E6)
    arm("23 (b) a rule-carrier constructor names no negative control", "(b) CONTROL",
        lambda inp: rows(inp)["sort"]["cic_l"][0].pop("control"))
    arm("24 (b) a control that stops refuting its rule", "(b) CONTROL",
        lambda inp: inp.theory.update({"C.lean": _ST_CONTROLS.replace("Refutes .sort True", "True")}))
    arm("25 (b) a control refuting a rule recorded as having none", "(b) CONTROL",
        lambda inp: inp.theory.update({"C.lean": _ST_CONTROLS.replace(
            "end Spec", "theorem pi_control : Refutes Rule.pi True := trivial\nend Spec")}))
    arm("26 (b) a rule recorded without a control and without a reason", "(b) CONTROL",
        lambda inp: rows(inp)["binding"]["cic_l"][0].update(control={"none": " "}))
    arm("27 (b) a control named for another rule", "(b) CONTROL",
        lambda inp: inp.theory.update({"C.lean": _ST_CONTROLS.replace("sort_control", "pi_control")})
        or rows(inp)["sort"]["cic_l"][0]["control"].update(theorem="Spec.pi_control"))
    arm("28 control: a cross-package set-model Refutes theorem is green", "",
        lambda inp: inp.extra_controls.update({
            "CICLModel/M.lean": (
                "namespace CICL.Model\n"
                "theorem helper (h : False) : CICL.NegativeControls.Refutes .pi True := False.elim h\n"
                "theorem pi_control : CICL.NegativeControls.Refutes .pi True := trivial\n"
                "end CICL.Model\n"
            )
        }) or rows(inp)["binding"]["cic_l"][0].update(
            control={"theorem": "CICL.Model.pi_control", "file": "CICLModel/M.lean"}))
    arm("29 (b) a parameterized control theorem with binders is refused", "(b) CONTROL",
        lambda inp: inp.theory.update({"C.lean": _ST_CONTROLS.replace(
            "theorem sort_control :", "theorem sort_control (h : False) :")}))
    arm("30 (b) an unrecorded cross-package Refutes theorem is refused", "(b) CONTROL",
        lambda inp: inp.extra_controls.update({
            "CICLModel/M.lean": (
                "namespace CICL.Model\n"
                "theorem pi_control : CICL.NegativeControls.Refutes CICL.NegativeControls.Rule.pi True := trivial\n"
                "end CICL.Model\n"
            )
        }))

    # The lexers and the scanner, directly: prose is not code.
    units = {fn.name: fn for fn in scan_cpp("k/checker.cpp", _ST_CPP)}
    arms += 1
    if sorted(units) != ["checker::infer", "checker::is_add", "helper::cached", "helper::helper",
                         "initialize_checker"]:
        failures.append(f"18 scanner: functions are {sorted(units)}")
    arms += 1
    if [a.name for a in units["checker::infer"].arms] != ["switch1/Sort", "switch1/Pi+Lambda"]:
        failures.append(f"19 scanner: arms are {[a.name for a in units['checker::infer'].arms]}")
    arms += 1
    if [c for _, c in units["checker::is_add"].constants] != ["Nat.add"]:
        failures.append(f"20 scanner: constants are {units['checker::is_add'].constants}")
    arms += 1
    lean = scan_lean(_ST_LEAN)
    want = {("Spec.Judgment", "inductive"), ("Spec.Judgment.sort", "constructor"),
            ("Spec.Judgment.pi", "constructor"), ("Spec.Admission", "structure"),
            ("Spec.Admission.typed", "field"), ("Spec.sort_ok", "theorem")}
    if lean != want:
        failures.append(f"21 scanner: Lean items are {sorted(lean)}")
    arms += 1
    spelled = ('bool f(expr const & e) {\n'
               '    return e == *g_succ || e == *other::g_lift || e == mk_constant("Eq", {u})'
               ' || env.get(name{"Nat", "zero"}) || "g_text mk_constant(\\"No\\")";\n}\n'
               'void initialize_f() {\n    g_succ = new_persistent_expr_const({"Nat", "succ"});\n}\n')
    got = [c for _, c in scan_cpp("k/f.cpp", spelled, {"g_lift": "Quot.lift"})[0].constants]
    if sorted(got) != ["Eq", "Nat.succ", "Nat.zero", "Quot.lift"]:
        failures.append(f"22 scanner: every spelling of a hardcoded constant resolves, got {got}")
    for failure in failures:
        print(f"  SELFTEST FAIL {failure}", file=sys.stderr)
    print(f"{TAG}_SELFTEST={'fail' if failures else 'ok'} arms={arms} failed={len(failures)}",
          file=out)
    return 1 if failures else 0


# ── command line ─────────────────────────────────────────────────────────────

def _update(root: Path, inp: Inputs, res: Result) -> int:
    pinned = inp.ratchet.get("not_specified", {})
    order = {"unspecified": 0, "partial": 1, "specified": 2}
    worse = [rid for rid, st in res.not_specified.items()
             if rid not in pinned or order[st] < order[pinned[rid]]]
    other = [p for p in res.problems if not p.startswith("(c) RATCHET")]
    if worse or other:
        print(f"--update refused: it only locks in a ratchet that SHRANK. "
              + (f"New or regressed: {', '.join(sorted(worse))}. " if worse else "")
              + (f"{len(other)} other problem(s) stand." if other else ""), file=sys.stderr)
        return 1
    doc = dict(inp.ratchet)
    doc["not_specified"] = dict(sorted(res.not_specified.items()))
    (root / RATCHET).write_text(json.dumps(doc, indent=2, ensure_ascii=False) + "\n")
    print(f"UPDATED {RATCHET}: {len(pinned)} -> {len(res.not_specified)} families not specified")
    return 0


def main(argv: list[str]) -> int:
    known = {"--selftest", "--list", "--inventory", "--anchor", "--update", "--require-complete"}
    flags = [a for a in argv if a.startswith("--")]
    if any(f not in known for f in flags):
        print(__doc__.split("USAGE")[1].split("Pure standard")[0], file=sys.stderr)
        return 2
    # The data modes print JSON on stdout; the self-test line goes to stderr there.
    rc = selftest(sys.stderr if {"--inventory", "--anchor"} & set(argv) else sys.stdout)
    if rc or "--selftest" in argv:
        return rc
    try:
        inp = load_inputs(REPO_ROOT)
    except (OSError, KeyError, json.JSONDecodeError, UnicodeDecodeError) as exc:
        print(f"{TAG}=fail cannot read the inventory's inputs: {exc}", file=sys.stderr)
        return 1
    if inp.missing_sources:
        print(f"{TAG}=unknown an input of the inventory is not in this tree "
              f"({', '.join(inp.missing_sources)}); nothing is measured and nothing is green. "
              f"The pinned kernel sources are leanprover/lean4 {inp.mapping['upstream']['tag']} "
              f"at {inp.mapping['upstream']['commit']}; the theory is {inp.mapping['spec']['root']}.",
              file=sys.stderr)
        return 3
    if "--anchor" in argv:
        args = argv[argv.index("--anchor") + 1:]
        if len(args) not in (2, 4):
            print("usage: --anchor FILE FUNCTION [START END]", file=sys.stderr)
            return 2
        fn = next((f for f in scan_cpp(args[0], inp.sources[args[0]]) if f.name == args[1]), None) \
            if args[0] in inp.sources else None
        if fn is None:
            print(f"no function {args[1]} in pinned file {args[0]}", file=sys.stderr)
            return 1
        lo, hi = (int(args[2]), int(args[3])) if len(args) == 4 else (fn.start, fn.end)
        raw_lines = inp.sources[args[0]].splitlines(keepends=True)
        print(json.dumps({"file": args[0], "function": fn.name, "lines": [lo, hi],
                          "sha256": _sha_lines(raw_lines, lo, hi)}))
        return 0
    if "--inventory" in argv:
        units = derive_units(inp)
        print(json.dumps({rel: [{"function": fn.name, "lines": [fn.start, fn.end],
                                 "sha256": fn.sha256,
                                 "case_arms": [{"arm": a.name, "line": a.line} for a in fn.arms],
                                 "hardcoded_constants": [{"line": ln, "constant": c}
                                                         for ln, c in fn.constants]}
                                for fn in fns] for rel, fns in units.items()}, indent=2))
        return 0
    res = check(inp)
    if "--update" in argv:
        return _update(REPO_ROOT, inp, res)
    if "--list" in argv:
        for row in inp.mapping["rows"]:
            if row.get("kind") == "rule":
                print(f"{row.get('status', '?'):12} {row['id']:44} {row.get('title', '')}")
    for problem in res.problems:
        print(f"  {problem}", file=sys.stderr)
    print(summary(res))
    print(completeness(res))
    if res.problems:
        return 1
    if "--require-complete" in argv and res.not_specified:
        print(f"--require-complete: {len(res.not_specified)} rule families are in the ratchet",
              file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
