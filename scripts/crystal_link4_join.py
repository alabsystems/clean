#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Crystal link 4 join: is the object link 4 proves the object that ships?

WHAT IT ANSWERS, OFFLINE (no build, no trustc, no cargo)

Link 4's spec modules are MINTED from trust-ir dumps. Each minted module has a
provenance record `crates/clean-verify/src/spec/core_spec/generated/*.prov.json`
naming the dump it was read from (`dump`, a `.trust-ir.bin`), that dump's
`dump_sha256`, the proved `function_name` and its `artifact_func_index`, and --
for a chain module -- `chain_functions` and any `merged_artifacts`. The callee
sidecar extracts `optimized_mir`, which is also what codegen reads, so the
decision of record (D7) is: link 4 is proved over the sidecar extraction of the
codegen input, JOINED BY CONTENT to the build that ships. Nothing joined them.
A proof pinned to an old dump kept reading GREEN while the shipped extraction of
the same function moved under it (infer_type's Err arm now threads the payload
where the pinned dump havocs it).

For every prov record this script:
  1. verifies the PINNED side: the `.bin` exists and hashes to `dump_sha256`
     (every merged artifact too), its `.trust-ir.txt` companion parses, a
     callee-sidecar manifest beside it (when present) agrees with both byte
     counts, and the function at `artifact_func_index` (each chain function at
     its `artifact_func_id`, over the primary artifact followed by the merged
     ones) carries the recorded name.  Any failure: that module is REFUSED.
  2. locates each proved function BY NAME in the CANDIDATE dump (`--dump`):
     `callees/clean_kernel.callees.trust-ir.txt` + its manifest for a function
     pinned in a callee-sidecar module, `clean_kernel.trust-ir.txt` for one
     pinned in the main module.  Absent or ambiguous: RED.
  3. compares the two function texts line by line with the classifier of
     `scripts/crystal_fixture_freshness.py` (imported, not copied): STRUCTURAL
     vs the index-only classes (functy-index, type-table-index, callee-index,
     global-index, loc-file-index).  Two adapters, both stated:
       * callee-sidecar headers print as `fn @...` (ccc); the classifier keys
         its functy normaliser on `rustcc fn @`, so when BOTH headers are
         `fn @` both are shown to it with the `rustcc ` prefix.  A header whose
         calling-convention word DIFFERS is left alone, and reads STRUCTURAL.
       * the classifier's `loc-file-index` covers every `; #` comment.  A
         `; #producer:` difference is escalated to STRUCTURAL here (another
         producer lowered the body); any other non-`#loc:` comment difference
         is additionally labelled `annotation` (still index-class, AMBER: the
         minted core form carries no comment).
  4. RE-DERIVES THE REFERENTS of every index the two texts carry -- the lane
     the text comparison cannot do.  An identical line `load struct.2` says
     nothing if struct.2 means something else in the candidate.  Every index
     token (`@func.N`, `@global.N`, `functy.N`, `struct.N`, `enum.N`, `ty.N`,
     `tuple.N`, `array.N`) is paired positionally; the pairing must be a
     BIJECTION per function (one pinned index, one candidate index, both ways);
     a `@func.N` pair must name the same function; a table pair's rows
     (`struct/enum ... id=N`, `functy.N = ...` with its `closure_ty`,
     `type ty.N = ...`, the N-th `global` row) must agree up to index
     numbering, recursively.  Any violation is STRUCTURAL.  A token with no
     table row on either side is STRUCTURAL too (fail closed).  Each problem
     names the path it was reached by (`line 5 > enum.2 > struct.12 ...`), and
     the report keeps the classifier-alone verdict beside the joined one as
     `text_verdict` ("text alone: AMBER" in the printed line).  STATED LIMIT:
     this lane is STRICTER than the minted core form, which carries no type
     table (a type is a canonical `(enum 0)`); only the encodings reader A
     derives (`encodings_derived` in the prov) read row contents.  So a RED
     reached through a nested row can be a change the proof never reads.  It
     stays RED here on purpose: deciding that it is irrelevant is a review,
     not a default.
  5. with `--flip-log`, the INSTANCE RULE: a proved function the compile log
     reports as `trust-ir-instance-flip: INSTANCE INSTALLED` is RED, because
     the instance seam installs MIR at codegen that the sidecar never sees.
     The log names a DEF (`def_path=`, crate-relative) and its `args=[...]`;
     a sidecar member is mapped to its def through the candidate manifest's
     `def_path` (trimmed), a main-module function through its own name.  Two
     def paths match when one's `::` segment list is a suffix of the other's
     after qualifiers inside `<...>` segments and lifetimes are normalised.
     A def match is RED whether or not the args also match (a spelling gap in
     the args must never read GREEN); the report says which.  The log is
     BOUND to the candidate: every INSTANCE INSTALLED line's DefId must be a
     body of the candidate's `clean_kernel.coverage.json` with the same
     `lineage`, or the run is REFUSED.  (Lineage is per SOURCE body, so this
     binds the log to a build of the same source, not to one exact build.)

VERDICT per module: GREEN identical (text and referents); AMBER index-class
differences only; RED any STRUCTURAL difference, a function absent from the
candidate, or the instance rule; REFUSED the pinned side (or the candidate
artifact it needs) is missing or malformed.  A chain module takes the worst of
its functions.  OVERALL: RED if any module is RED, else REFUSED if any is, else
AMBER if any is, else GREEN.  RED outranks REFUSED on purpose: a module known
to have moved is the answer, and the refused modules are still printed and
counted.

Exit: 0 GREEN (or AMBER without --strict); 1 RED, or AMBER under --strict;
2 REFUSED (a module refused with no RED, or the inputs are unusable).

    scripts/crystal_link4_join.py --dump <dump-dir> [--flip-log F] [--strict] [--json OUT]
    scripts/crystal_link4_join.py --self-test

Reads no Rust or Lean source: its inputs are JSON records and trust-ir text.

SYMBOLS (M2, 2026-09-27). Every definition-site symbol -- a `fn` header's name, a `struct`/
`enum`/`record` row's and a `global` row's -- is read by the shared reader
`scripts/crystal_trust_ir_symbols.py` (`ModuleSymbols`), which decodes trust-ir WS4.3's QUOTED
spelling (`fn @"k::f::<..>"`), refuses what the printer cannot write, and holds each module to one
grammar. A function is located by its DECODED name, and the texts the join compares carry every
such symbol in the legacy (raw) spelling, so a pinned pre-WS4.3 dump and a WS4.3 candidate of the
same program compare as the program, not as two printers. `--pinned-inputs` prints the
first-party modules this script runs besides itself, for its registry row to pin.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import crystal_fixture_freshness as ff  # noqa: E402  (the classifier, reused)
# The ONE reader of trust-ir's definition-site symbols (quoted since WS4.3), shared with links 3/4.
import crystal_trust_ir_symbols as tir_symbols  # noqa: E402

# Read by check_gate_registry.py (PINNED_INPUTS_MARKER): `--pinned-inputs` prints the first-party
# modules this script executes besides itself (derived from its imports), and its registry row
# pins them, so a change to the shared symbol reader is R7-stale until the arms replay over it.
ANSWERS_PINNED_INPUTS = True

REPO = ff.REPO
PROV_DIR = REPO / "crates" / "clean-verify" / "src" / "spec" / "core_spec" / "generated"
MAIN_TEXT = Path("clean_kernel.trust-ir.txt")
CALLEES_TEXT = Path("callees") / "clean_kernel.callees.trust-ir.txt"
CALLEES_MANIFEST = Path("callees") / "clean_kernel.callees.manifest.json"
MODULE_MAIN, MODULE_CALLEES = "clean_kernel", "clean_kernel::callees"
SCHEMA = "clean.crystal.link4_join/v1"
RANK = {"GREEN": 0, "AMBER": 1, "REFUSED": 2, "RED": 3}  # module worst-of order


class Refused(Exception):
    """An input this gate cannot read soundly. Never a verdict of drift."""


# ── artifacts ────────────────────────────────────────────────────────────────

_HEADER = re.compile(r"^(?:[a-z_]+ )?fn @")
# What may stand before `fn @`: one lower-case word (`rustcc`), as `_HEADER` admits -- and only
# when `fn @` follows it, since the reader does not backtrack into `fn ` itself.
_FN_PREFIX = re.compile(r"(?:[a-z_]+ (?=fn @))?")
_ROW_ID = re.compile(r"\s+id=(\d+)$")
_FUNCTY = re.compile(r"^functy\.(\d+) = (.*)$")
_CLOSURE = re.compile(r"^closure_ty functy\.(\d+) (.*)$")
_TYPE = re.compile(r"^type ty\.(\d+) = (.*)$")
_TOKEN = re.compile(r"@func\.(\d+)|@global\.(\d+)|\b(functy|struct|enum|tuple|array|ty)\.(\d+)")
_OWN_GLOBAL = re.compile(r"@__trust_(promoted|bytes)_\d+")


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


class Artifact:
    """One trust-ir TEXT module: function order, wanted bodies, type tables."""

    def __init__(self, path: Path, wanted: set[str]):
        self.path = path
        self.module: str | None = None
        self.names: list[str] = []
        self.index_by_name: dict[str, list[int]] = {}
        self.bodies: dict[int, str] = {}
        self.rows: dict[tuple[str, int], str] = {}
        self.globals: list[str] = []
        closures: dict[int, str] = {}
        try:
            text = path.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError) as exc:
            raise Refused(f"{path}: unreadable trust-ir text ({exc})") from exc
        lines = text.split("\n")
        if not lines or not lines[0].startswith("; TrustIr text format"):
            raise Refused(f"{path}: not a trust-ir text module (first line {lines[0][:40]!r})")
        cur: list[str] | None = None
        cur_idx = -1
        syms = tir_symbols.ModuleSymbols(_FN_PREFIX)
        for ln, line in enumerate(lines, 1):
            if cur is not None:
                cur.append(line)
                if line == "}":
                    if self.names[cur_idx] in wanted:
                        self.bodies[cur_idx] = "\n".join(cur) + "\n"
                    cur = None
                continue
            try:
                fh = syms.fn_header(line, f"line {ln}")
                tr = None if fh is not None else syms.type_row(line, f"line {ln}")
                gr = None if fh is not None or tr is not None else syms.global_row(line, f"line {ln}")
            except tir_symbols.SymbolRefusal as exc:
                raise Refused(f"{path}: line {ln}: {exc}") from exc
            if fh is None and _HEADER.match(line):
                raise Refused(f"{path}: malformed function header {line[:80]!r}")
            if fh is not None:
                name = fh[0]
                cur_idx = len(self.names)
                self.names.append(name)
                self.index_by_name.setdefault(name, []).append(cur_idx)
                # The header in the LEGACY spelling (the decoded name, raw), so the text a body is
                # compared by does not depend on which printer wrote it.
                pre = line[:line.index("fn @")]
                cur = [f"{pre}fn @{name}(functy.{fh[1]}) {{"]
            elif line.startswith("module "):
                self.module = line[len("module "):].strip().strip('"')
            elif tr is not None and tr[0] in ("struct", "enum"):
                line = tir_symbols.legacy_spelling(line, tr[2], tr[3], tr[1])
                m = _ROW_ID.search(line)
                if not m:
                    raise Refused(f"{path}: table row without id= {line[:80]!r}")
                self._row((tr[0], int(m.group(1))), line[: m.start()])
            elif m := _FUNCTY.match(line):
                self._row(("functy", int(m.group(1))), m.group(2))
            elif m := _CLOSURE.match(line):
                closures[int(m.group(1))] = m.group(2)
            elif m := _TYPE.match(line):
                self._row(("ty", int(m.group(1))), m.group(2))
            elif gr is not None:
                line = tir_symbols.legacy_spelling(line, gr[1], gr[2], gr[0])
                self.globals.append(_OWN_GLOBAL.sub(r"@__trust_\1_X", line))
        if cur is not None:
            raise Refused(f"{path}: truncated inside function {self.names[cur_idx][:80]!r}")
        for n, rest in closures.items():
            key = ("functy", n)
            self.rows[key] = self.rows.get(key, "") + " || closure_ty " + rest
        for i, g in enumerate(self.globals):
            self.rows[("global", i)] = g

    def _row(self, key: tuple[str, int], text: str) -> None:
        if key in self.rows:
            raise Refused(f"{self.path}: duplicate table row {key[0]}.{key[1]}")
        self.rows[key] = text


def check_manifest(manifest: Path, text: Path) -> dict:
    """A callee-sidecar manifest must name, and byte-count, the text and binary."""
    try:
        doc = json.loads(manifest.read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        raise Refused(f"{manifest}: unreadable manifest ({exc})") from exc
    arts = doc.get("artifacts") if isinstance(doc, dict) else None
    if not isinstance(arts, dict) or not isinstance(doc.get("members"), list):
        raise Refused(f"{manifest}: no `artifacts`/`members` -- not a callee-sidecar manifest")
    if arts.get("text") != text.name or arts.get("text_bytes") != text.stat().st_size:
        raise Refused(
            f"{manifest}: names text {arts.get('text')!r} of {arts.get('text_bytes')} bytes, "
            f"the artifact is {text.name} of {text.stat().st_size} bytes")
    binary = text.parent / str(arts.get("binary", ""))
    if "binary" in arts and (not binary.is_file() or binary.stat().st_size != arts.get("binary_bytes")):
        raise Refused(f"{manifest}: binary {binary.name} missing or not {arts.get('binary_bytes')} bytes")
    return doc


def sibling_manifest(text: Path) -> Path | None:
    if text.name != CALLEES_TEXT.name:
        return None
    return text.parent / CALLEES_MANIFEST.name


# ── the per-function join ────────────────────────────────────────────────────


def _code(line: str) -> str:
    if _HEADER.match(line):
        return line[line.rfind("(functy."):]
    return ff._strip_loc(line)  # the classifier's own comment rule


def _tokens(code: str) -> list[tuple[str, int]]:
    out = []
    for m in _TOKEN.finditer(code):
        if m.group(1) is not None:
            out.append(("func", int(m.group(1))))
        elif m.group(2) is not None:
            out.append(("global", int(m.group(2))))
        else:
            out.append((m.group(3), int(m.group(4))))
    return out


def _comment(line: str) -> str:
    at = line.find("; #")
    return line[at:].strip() if at >= 0 else ""


def _producer(body: str) -> str | None:
    m = re.search(r"^\s*; #producer: (\S+)", body, re.M)
    return m.group(1) if m else None


class ReferentJoin:
    """Pair index tokens pinned->candidate; the pairing must be a bijection whose
    referents agree up to numbering, recursively."""

    def __init__(self, pin: Artifact, cand: Artifact):
        self.pin, self.cand = pin, cand
        self.fwd: dict[tuple[str, int], int] = {}
        self.bwd: dict[tuple[str, int], int] = {}
        self.work: list[tuple[str, int, int, str]] = []
        self.problems: list[str] = []

    def pair_codes(self, a: str, b: str, where: str) -> None:
        ta, tb = _tokens(a), _tokens(b)
        if [c for c, _ in ta] != [c for c, _ in tb]:
            self.problems.append(f"referent tokens differ in kind at {where}: {a.strip()!r} -> {b.strip()!r}")
            return
        for (cls, np), (_c, nc) in zip(ta, tb):
            self.pair(cls, np, nc, where)

    def pair(self, cls: str, np: int, nc: int, where: str) -> None:
        f, b = self.fwd.get((cls, np)), self.bwd.get((cls, nc))
        if f is None and b is None:
            self.fwd[(cls, np)], self.bwd[(cls, nc)] = nc, np
            self.work.append((cls, np, nc, where))
        elif f != nc or b != np:
            self.problems.append(
                f"inconsistent renumbering (via {where}): pinned {cls}.{np} -> candidate {cls}.{nc}, "
                f"but pinned {cls}.{np} already -> {f} and candidate {cls}.{nc} already <- {b}")

    def run(self) -> None:
        while self.work:
            cls, np, nc, where = self.work.pop()
            if cls == "func":
                p = self.pin.names[np] if np < len(self.pin.names) else None
                c = self.cand.names[nc] if nc < len(self.cand.names) else None
                if p is None or c is None:
                    self.problems.append(f"unresolvable callee: pinned @func.{np}={p!r}, candidate @func.{nc}={c!r}")
                elif p != c:
                    self.problems.append(f"callee-name: @func.{np}={p!r} but @func.{nc}={c!r}")
                continue
            rp, rc = self.pin.rows.get((cls, np)), self.cand.rows.get((cls, nc))
            if rp is None or rc is None:
                self.problems.append(f"unresolvable referent: no table row for pinned {cls}.{np} "
                                     f"({'found' if rp else 'absent'}) / candidate {cls}.{nc} "
                                     f"({'found' if rc else 'absent'})")
                continue
            if rp != rc and "STRUCTURAL" in ff.classify(rp, rc):
                self.problems.append(f"referent {cls}.{np} -> {cls}.{nc} changed (via {where}): "
                                     f"{rp!r} -> {rc!r}")
                continue
            self.pair_codes(rp, rc, f"{where} > {cls}.{np}")


def join_function(pin: Artifact, pidx: int, cand: Artifact, cidx: int) -> tuple[dict, list[str]]:
    """(text classes, referent problems) of one function, pinned body vs candidate body."""
    a, b = pin.bodies[pidx], cand.bodies[cidx]
    if a.startswith("fn @") and b.startswith("fn @"):
        a, b = "rustcc " + a, "rustcc " + b
    classes: dict[str, list[str]] = {} if a == b else ff.drift_classes(a, b)
    al, bl = a.splitlines(), b.splitlines()
    if len(al) == len(bl):
        for x, y in zip(al, bl):
            if x != y and "loc-file-index" in ff.classify(x, y):
                cx, cy = _comment(x), _comment(y)
                if cx != cy and not (cx.startswith("; #loc:") and cy.startswith("; #loc:")):
                    classes.setdefault("annotation", []).append(f"{cx}  ->  {cy}")
    pp, cp = _producer(a), _producer(b)
    if pp != cp:
        classes.setdefault("STRUCTURAL", []).append(f"producer {pp} -> {cp}")
    problems: list[str] = []
    if len(al) == len(bl):
        rj = ReferentJoin(pin, cand)
        for i, (x, y) in enumerate(zip(al, bl)):
            rj.pair_codes(_code(x), _code(y), f"line {i + 1}")
        rj.run()
        problems = rj.problems
    return classes, problems


# ── the instance rule ────────────────────────────────────────────────────────

_INSTANCE = re.compile(
    r"trust-ir-instance-flip: INSTANCE INSTALLED, def=DefId\((\d+):(\d+) ~ .*?\), "
    r"def_path=(.*?), asserts=.*?lineage=(sha256:[0-9a-f]{64}),.*?"
    r"args=\[(.*)\], instances_flipped_so_far=\d+\s*$")
_LIFETIME = re.compile(r"'(?:\{erased\}|[A-Za-z_]\w*)")
_QUALIFIER = re.compile(r"(?:[A-Za-z_]\w*::)+(?=[A-Za-z_])")


def _split_top(s: str, sep: str) -> list[str]:
    out, depth, cur, i = [], 0, [], 0
    while i < len(s):
        ch = s[i]
        if ch in "<([{":
            depth += 1
        elif ch in ">)]}" and not (ch == ">" and i > 0 and s[i - 1] == "-"):
            depth -= 1
        if depth == 0 and s.startswith(sep, i):
            out.append("".join(cur))
            cur, i = [], i + len(sep)
            continue
        cur.append(ch)
        i += 1
    out.append("".join(cur))
    return out


def def_key(path: str) -> list[str]:
    segs = []
    for seg in _split_top(_LIFETIME.sub("'_", path.strip()), "::"):
        if seg.startswith("<"):
            if " as " not in seg and not seg.startswith("<impl "):
                continue  # a turbofish `<T>`, not an item segment
            seg = _QUALIFIER.sub("", seg)
        if seg and seg != "clean_kernel":
            segs.append(seg)
    return segs


def def_match(a: str, b: str) -> bool:
    ka, kb = def_key(a), def_key(b)
    n = min(len(ka), len(kb))
    return n > 0 and ka[-n:] == kb[-n:]


def _norm_name(s: str) -> str:
    return _LIFETIME.sub("'_", s).replace("clean_kernel::", "")


def args_match(args: str, name: str) -> bool:
    hay = _norm_name(name)
    for arg in _split_top(_norm_name(args), ", "):
        arg = arg.strip()
        if not arg or arg == "'_":
            continue
        if not re.search(r"(?<![\w:])" + re.escape(arg) + r"(?![\w])", hay):
            return False
    return True


def load_flip_log(flip_log: Path, coverage: Path) -> list[dict]:
    try:
        text = flip_log.read_text(encoding="utf-8", errors="replace")
    except OSError as exc:
        raise Refused(f"{flip_log}: unreadable flip log ({exc})") from exc
    if "trust-ir-flip:" not in text and "trust-ir-instance-flip:" not in text:
        raise Refused(f"{flip_log}: carries no trust-ir-flip line -- not a flip log")
    installed = []
    for ln, line in enumerate(text.splitlines(), 1):
        if "INSTANCE INSTALLED" not in line:
            continue
        m = _INSTANCE.search(line)
        if not m:
            raise Refused(f"{flip_log}:{ln}: an INSTANCE INSTALLED line this gate cannot parse")
        installed.append({"line": ln, "crate": int(m.group(1)), "def_index": int(m.group(2)),
                          "def_path": m.group(3), "lineage": m.group(4), "args": m.group(5)})
    if installed:
        if not coverage.is_file():
            raise Refused(f"{coverage} is missing: the flip log cannot be bound to the candidate")
        try:
            rows = json.loads(coverage.read_text(encoding="utf-8"))["bodies"]
        except (OSError, ValueError, KeyError, TypeError) as exc:
            raise Refused(f"{coverage}: unreadable coverage ({exc})") from exc
        lineage = {r.get("def_index"): r.get("lineage") for r in rows if isinstance(r, dict)}
        for inst in installed:
            if inst["crate"] != 0 or lineage.get(inst["def_index"]) != inst["lineage"]:
                raise Refused(
                    f"{flip_log}:{inst['line']}: INSTANCE INSTALLED DefId({inst['crate']}:"
                    f"{inst['def_index']}) lineage {inst['lineage'][:19]} is not a body of the "
                    f"candidate's coverage ({lineage.get(inst['def_index'])}) -- log and dump disagree")
    return installed


# ── the run ──────────────────────────────────────────────────────────────────


class Pins:
    """Pinned artifacts, verified once per path."""

    def __init__(self) -> None:
        self.sha: dict[Path, str] = {}
        self.art: dict[Path, Artifact] = {}

    def verify(self, bin_path: Path, want: str) -> Path:
        if not str(bin_path).endswith(".trust-ir.bin"):
            raise Refused(f"pinned dump {bin_path} is not a .trust-ir.bin")
        if not bin_path.is_file():
            raise Refused(f"pinned dump {bin_path} is missing")
        if bin_path not in self.sha:
            self.sha[bin_path] = sha256_file(bin_path)
        if self.sha[bin_path] != want:
            raise Refused(f"pinned dump {bin_path} hashes to {self.sha[bin_path][:12]}, "
                          f"the prov records {str(want)[:12]}")
        text = Path(str(bin_path)[: -len(".bin")] + ".txt")
        if not text.is_file():
            raise Refused(f"pinned text {text} is missing")
        return text

    def artifact(self, text: Path, wanted: set[str]) -> Artifact:
        if text not in self.art:
            man = sibling_manifest(text)
            if man is not None and man.is_file():
                check_manifest(man, text)
            self.art[text] = Artifact(text, wanted)
        return self.art[text]


def _load_prov(path: Path) -> dict:
    try:
        prov = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        raise Refused(f"{path.name}: unreadable prov ({exc})") from exc
    need = ("dump", "dump_sha256", "function_name", "artifact_func_index", "module_name")
    missing = [k for k in need if k not in prov] if isinstance(prov, dict) else list(need)
    if missing:
        raise Refused(f"{path.name}: missing field(s) {missing}")
    return prov


def run(prov_dir: Path, cand_dir: Path, flip_log: Path | None, strict: bool) -> tuple[int, dict]:
    ff.selftest_classifier()
    prov_paths = sorted(prov_dir.glob("*.prov.json"))
    if not prov_paths:
        raise Refused(f"{prov_dir}: no *.prov.json -- nothing to join")
    if not cand_dir.is_dir():
        raise Refused(f"candidate dump {cand_dir} is not a directory")
    provs: dict[str, dict | Refused] = {}
    wanted: set[str] = set()
    for p in prov_paths:
        mid = p.name[: -len(".prov.json")]
        try:
            provs[mid] = _load_prov(p)
            wanted.add(provs[mid]["function_name"])  # type: ignore[index]
            wanted.update(c.get("name", "") for c in provs[mid].get("chain_functions") or [])  # type: ignore[union-attr]
        except Refused as exc:
            provs[mid] = exc

    cand_cache: dict[str, Artifact | Refused] = {}
    cand_manifest: dict = {}
    cand_prov: dict[str, dict] = {}

    def candidate(module: str) -> Artifact:
        if module not in cand_cache:
            rel = {MODULE_MAIN: MAIN_TEXT, MODULE_CALLEES: CALLEES_TEXT}.get(module)
            try:
                if rel is None:
                    raise Refused(f"no candidate artifact for pinned module {module!r}")
                text = cand_dir / rel
                if not text.is_file():
                    raise Refused(f"candidate {text} is missing")
                if module == MODULE_CALLEES:
                    cand_manifest.update(check_manifest(cand_dir / CALLEES_MANIFEST, text))
                art = Artifact(text, wanted)
                if art.module != module:
                    raise Refused(f"candidate {text} declares module {art.module!r}, not {module!r}")
                binp = Path(str(text)[: -len(".txt")] + ".bin")
                cand_prov[module] = {"text": str(rel), "text_bytes": text.stat().st_size,
                                     "bin_sha256": sha256_file(binp) if binp.is_file() else None}
                cand_cache[module] = art
            except Refused as exc:
                cand_cache[module] = exc
        got = cand_cache[module]
        if isinstance(got, Refused):
            raise got
        return got

    installed = load_flip_log(flip_log, cand_dir / "clean_kernel.coverage.json") if flip_log else None
    pins = Pins()
    modules: dict[str, dict] = {}
    for mid, prov in provs.items():
        entry: dict = {"verdict": "GREEN", "reasons": [], "functions": []}
        modules[mid] = entry
        if isinstance(prov, Refused):
            entry.update(verdict="REFUSED", reasons=[str(prov)])
            continue
        entry.update(function_name=prov["function_name"], pinned_dump=prov["dump"],
                     pinned_sha256=prov["dump_sha256"], artifact_producer=prov.get("artifact_producer"))
        try:
            texts = [pins.verify(Path(prov["dump"]), prov["dump_sha256"])]
            texts += [pins.verify(Path(m["path"]), m["sha256"]) for m in prov.get("merged_artifacts") or []]
            parsed = [pins.artifact(t, wanted) for t in texts]
            if parsed[0].module != prov["module_name"]:
                raise Refused(f"pinned text declares module {parsed[0].module!r}, the prov "
                              f"records {prov['module_name']!r}")
            flat: list[tuple[Artifact, int]] = [(a, i) for a in parsed for i in range(len(a.names))]
            want = [(prov["function_name"], prov["artifact_func_index"])]
            want += [(c["name"], c["artifact_func_id"]) for c in prov.get("chain_functions") or []
                     if c.get("name") != prov["function_name"]]
            located = []
            for name, gidx in want:
                if not isinstance(gidx, int) or not 0 <= gidx < len(flat) or \
                        flat[gidx][0].names[flat[gidx][1]] != name:
                    raise Refused(f"pinned index {gidx} does not name {name[:80]!r} in the pinned "
                                  f"artifact(s)")
                located.append((name,) + flat[gidx])
            prod = _producer(located[0][1].bodies[located[0][2]])
            if prov.get("artifact_producer") and prod != prov["artifact_producer"]:
                raise Refused(f"pinned body producer {prod!r} is not the prov's "
                              f"{prov['artifact_producer']!r}")
        except Refused as exc:
            entry.update(verdict="REFUSED", reasons=[str(exc)])
            continue
        for name, part, pidx in located:
            fn: dict = {"name": name, "pinned_index": pidx, "pinned_text": str(part.path)}
            entry["functions"].append(fn)
            try:
                cart = candidate(part.module or "")
            except Refused as exc:
                fn.update(verdict="REFUSED", reasons=[str(exc)])
                continue
            hits = cart.index_by_name.get(name, [])
            if len(hits) != 1:
                fn.update(verdict="RED", reasons=[("ABSENT FROM CANDIDATE" if not hits else
                                                   f"AMBIGUOUS IN CANDIDATE ({len(hits)} bodies)")])
                continue
            fn["candidate_index"] = hits[0]
            classes, problems = join_function(part, pidx, cart, hits[0])
            text_verdict = "RED" if "STRUCTURAL" in classes else ("AMBER" if classes else "GREEN")
            fn["text_verdict"] = text_verdict  # the reused classifier alone, before the referent lane
            fn["referent_problems"] = problems[:12]
            if problems:
                classes.setdefault("STRUCTURAL", []).extend(f"[referent lane] {r}" for r in problems)
            fn["classes"] = sorted(classes)
            fn["detail"] = {k: v[:6] for k, v in classes.items()}
            fn["verdict"] = "RED" if "STRUCTURAL" in classes else ("AMBER" if classes else "GREEN")
            fn["reasons"] = [f"STRUCTURAL: {r}" for r in classes.get("STRUCTURAL", [])[:3]]
            if installed is not None:
                if part.module == MODULE_CALLEES:
                    dp = next((m.get("def_path") for m in cand_manifest.get("members", [])
                               if m.get("name") == name), None)
                else:
                    dp = name
                fn["def_path"] = dp
                hit = [i for i in installed if dp is not None and def_match(dp, i["def_path"])]
                if dp is None:
                    fn["instance"] = "UNMAPPED (fail-closed)"
                    fn["verdict"] = "RED"
                    fn["reasons"].append("instance rule: no manifest def_path for this member")
                elif hit:
                    exact = [i for i in hit if args_match(i["args"], name)]
                    fn["instance"] = [dict(line=i["line"], def_path=i["def_path"], args=i["args"][:200],
                                           args_match=i in exact) for i in hit]
                    fn["verdict"] = "RED"
                    fn["reasons"].append(
                        f"INSTANCE-INSTALLED ({'def+args' if exact else 'same def, args not matched: fail-closed'}; "
                        f"flip log line {(exact or hit)[0]['line']}): the instance seam installs MIR the "
                        f"sidecar never sees")
        worst = max((f.get("verdict", "GREEN") for f in entry["functions"]), key=RANK.__getitem__, default="GREEN")
        entry["verdict"] = worst
        entry["reasons"] = [f"{f['name'][:70]}: {r}" for f in entry["functions"] for r in f.get("reasons", [])]
        entry["classes"] = sorted({c for f in entry["functions"] for c in f.get("classes", [])})
        entry["text_verdict"] = max((f.get("text_verdict", f.get("verdict", "GREEN")) for f in entry["functions"]),
                                    key=RANK.__getitem__, default=entry["verdict"])

    members_hit = []
    if installed is not None and cand_manifest:
        for m in cand_manifest.get("members", []):
            hit = [i for i in installed if def_match(str(m.get("def_path", "")), i["def_path"])]
            if hit:
                members_hit.append({"sidecar_func_id": m.get("sidecar_func_id"), "name": m.get("name"),
                                    "args_match": any(args_match(i["args"], m.get("name", "")) for i in hit)})
    counts = {v: sum(1 for e in modules.values() if e["verdict"] == v) for v in RANK}
    overall = ("RED" if counts["RED"] else "REFUSED" if counts["REFUSED"] else
               "AMBER" if counts["AMBER"] else "GREEN")
    code = {"RED": 1, "REFUSED": 2, "AMBER": 1 if strict else 0, "GREEN": 0}[overall]
    report = {
        "schema": SCHEMA, "verdict": overall, "strict": strict, "counts": counts,
        "candidate": {"dump": ff.dump_provenance(cand_dir), "artifacts": cand_prov},
        "flip_log": None if flip_log is None else {
            "name": flip_log.name, "sha256": sha256_file(flip_log),
            "instance_installed_lines": len(installed or []),
            "sidecar_members_instance_installed": members_hit},
        "modules": modules,
    }
    return code, report


def render(report: dict) -> list[str]:
    out = [f"== crystal link-4 join ==  candidate: {report['candidate']['dump']}"]
    for mid, e in report["modules"].items():
        fns = e.get("functions", [])
        pin = e.get("pinned_dump", "?")
        pin = "/".join(Path(pin).parts[-3:-1]) if pin != "?" else pin
        tv = e.get("text_verdict")
        out.append("  %-14s %-8s fns=%d classes=%s%s pin=%s@%s" % (
            mid, e["verdict"], len(fns), ",".join(e.get("classes") or []) or "-",
            f" (text alone: {tv})" if tv and tv != e["verdict"] else "", pin,
            str(e.get("pinned_sha256", "?"))[:12]))
        for r in e.get("reasons", [])[:3]:
            out.append(f"      {r[:300]}")
    fl = report.get("flip_log")
    if fl:
        ids = [f"{m['sidecar_func_id']}{'' if m['args_match'] else '(def-only)'}"
               for m in fl["sidecar_members_instance_installed"]]
        out.append(f"  flip log {fl['name']}: {fl['instance_installed_lines']} INSTANCE INSTALLED "
                   f"line(s); candidate sidecar members under them: {', '.join(ids) or 'none'}")
    c = report["counts"]
    out.append(f"LINK4_JOIN={report['verdict']} green={c['GREEN']} amber={c['AMBER']} "
               f"red={c['RED']} refused={c['REFUSED']}")
    return out


# ── self-test: synthetic arms, tmp files only ────────────────────────────────

_PIN_CALLEES = """; TrustIr text format v1
module "clean_kernel::callees"
struct @S { u64 } size=8 align=8 id=0
struct @T { struct.0, u8 } size=16 align=8 id=1
functy.0 = (ptr) -> (struct.1)
functy.1 = (ptr) -> (u64)
type ty.0 = u8
global internal @__trust_bytes_0 [ty.0 x 3] = array[ 1, 2, 3 ]
fn @k::f::<__trust_args@aa>(functy.0) {
    ; #producer: trust-ir
    ; #proof: pure
bb0(%0: ptr):
    %1 = call @func.1(%0)
    %2 = undef struct.1  ; #proof: fresh_symbolic_havoc
    %3 = insertfield struct.1 %2, 1, %1
    ret %3
}

fn @k::g::<__trust_args@bb>(functy.1) {
    ; #producer: trust-ir
bb0(%0: ptr):
    %1 = load u64, ptr %0
    ret %1
}

fn @<k::S as k::Tr>::m::<__trust_args@cc>(functy.1) {
    ; #producer: trust-ir
bb0(%0: ptr):
    %1 = const u64 7
    ret %1
}
"""
_PIN_MAIN = """; TrustIr text format v1
module "clean_kernel"
enum @L { Zero = 0, Succ(ptr) = 1 } id=0
functy.0 = (ptr) -> (bool)
functy.1 = (ptr) -> (ptr)
rustcc fn @lvl::L::is_zero(functy.0) {
    ; #producer: trust
bb0(%0: ptr):
    %1 = load enum.0, ptr %0  ; #loc: 3 10 4
    %2 = call @func.1(%0)  ; #loc: 3 11 4
    %3 = const bool true  ; #loc: 3 12 4
    ret %3  ; #loc: 3 13 4
}

rustcc fn @<lvl::Arc as std::ops::Deref>::deref(functy.1) {
    ; #producer: trust
bb0(%0: ptr):
    ret %0  ; #loc: 3 20 4
}
"""
_NAMES = {"f": "k::f::<__trust_args@aa>", "g": "k::g::<__trust_args@bb>",
          "m": "<k::S as k::Tr>::m::<__trust_args@cc>", "z": "lvl::L::is_zero",
          "d": "<lvl::Arc as std::ops::Deref>::deref"}
_DEF_PATHS = {"f": "f", "g": "g", "m": "Tr::m"}
_LINEAGE = "sha256:" + "ab" * 32


def _write_dump(root: Path, callees: str, main: str, *, members: list[str] | None = None,
                coverage: bool = True) -> None:
    (root / "callees").mkdir(parents=True, exist_ok=True)
    ct, cb = root / CALLEES_TEXT, root / CALLEES_TEXT.with_suffix(".bin")
    ct.write_text(callees, encoding="utf-8")
    cb.write_bytes(b"callees-bin:" + hashlib.sha256(callees.encode()).digest())
    mains = members if members is not None else [
        n for n in ("f", "g", "m")
        if f"@{_NAMES[n]}(" in callees or f"@{tir_symbols.spell_symbol(_NAMES[n])}(" in callees]
    manifest = {"members": [{"sidecar_func_id": i, "name": _NAMES[n], "def_path": _DEF_PATHS[n]}
                            for i, n in enumerate(mains)],
                "artifacts": {"text": ct.name, "text_bytes": ct.stat().st_size,
                              "binary": cb.name, "binary_bytes": cb.stat().st_size}}
    (root / CALLEES_MANIFEST).write_text(json.dumps(manifest), encoding="utf-8")
    mt = root / MAIN_TEXT
    mt.write_text(main, encoding="utf-8")
    mt.with_suffix(".bin").write_bytes(b"main-bin:" + hashlib.sha256(main.encode()).digest())
    if coverage:
        (root / "clean_kernel.coverage.json").write_text(json.dumps(
            {"bodies": [{"def_index": 100, "def_path": "k::Tr::m", "lineage": _LINEAGE}]}), encoding="utf-8")


def _write_provs(prov_dir: Path, pin: Path, tweak=None) -> None:
    prov_dir.mkdir(parents=True, exist_ok=True)
    cbin, mbin = pin / CALLEES_TEXT.with_suffix(".bin"), pin / MAIN_TEXT.with_suffix(".bin")
    cs, ms = sha256_file(cbin), sha256_file(mbin)
    provs = {
        "t_f.core": {"dump": str(cbin), "dump_sha256": cs, "module_name": MODULE_CALLEES,
                     "function_name": _NAMES["f"], "artifact_func_index": 0, "artifact_producer": "trust-ir",
                     "chain_functions": [{"name": _NAMES["f"], "artifact_func_id": 0},
                                         {"name": _NAMES["g"], "artifact_func_id": 1}]},
        "t_m.core": {"dump": str(cbin), "dump_sha256": cs, "module_name": MODULE_CALLEES,
                     "function_name": _NAMES["m"], "artifact_func_index": 2, "artifact_producer": "trust-ir"},
        "t_z.core": {"dump": str(mbin), "dump_sha256": ms, "module_name": MODULE_MAIN,
                     "function_name": _NAMES["z"], "artifact_func_index": 0, "artifact_producer": "trust",
                     "merged_artifacts": [{"path": str(cbin), "sha256": cs}],
                     "chain_functions": [{"name": _NAMES["z"], "artifact_func_id": 0},
                                         {"name": _NAMES["d"], "artifact_func_id": 1},
                                         {"name": _NAMES["g"], "artifact_func_id": 3}]},
    }
    if tweak:
        tweak(provs)
    for mid, p in provs.items():
        (prov_dir / f"{mid}.prov.json").write_text(json.dumps(p), encoding="utf-8")


def _flip(def_path: str, args: str, lineage: str = _LINEAGE, def_index: int = 100) -> str:
    return ("INFO trust-ir-flip: FALLBACK to built MIR, did=DefId(0:1 ~ x)\n"
            f" INFO rustc_mir_transform::trust_instance_flip trust-ir-instance-flip: INSTANCE INSTALLED, "
            f"def=DefId(0:{def_index} ~ clean_kernel[1]::k::Tr::m), def_path={def_path}, asserts=0, "
            f"markers_exact=true, lineage={lineage}, args_digest=sha256:{'cd' * 32}, "
            f"args=[{args}], instances_flipped_so_far=1\n")


# The AMBER mutation: one new function in front (every @func.N shifts), struct.1
# renumbered to struct.3 with a new struct.2, functy.0 renumbered to functy.7.
def _renumber(text: str) -> str:
    text = text.replace("@func.1(", "@func.2(")
    text = re.sub(r"\bstruct\.1\b", "struct.3", text)
    text = text.replace("id=1\n", "id=3\nstruct @Z { u8 } size=1 align=1 id=2\n")
    text = text.replace("functy.0", "functy.7")
    head, _, rest = text.partition('type ty.0 = u8\n')
    return head + "type ty.0 = u8\n" + "fn @k::zz(functy.1) {\n    ; #producer: trust-ir\nbb0(%0: ptr):\n    ret %0\n}\n\n" + rest


def _renumber_main(text: str) -> str:
    pad = "rustcc fn @lvl::pad(functy.1) {\n    ; #producer: trust\nbb0(%0: ptr):\n    ret %0\n}\n\n"
    text = text.replace("#loc: 3 ", "#loc: 9 ").replace("@func.1(", "@func.2(")
    return text.replace("rustcc fn @<lvl::Arc", pad + "rustcc fn @<lvl::Arc")


def _arms() -> list[tuple[str, dict]]:
    C, M = _PIN_CALLEES, _PIN_MAIN
    G = {"t_f.core": "GREEN", "t_m.core": "GREEN", "t_z.core": "GREEN"}
    arms = [
        ("identical -> GREEN", dict(want=G, code=0)),
        ("index-only renumbering -> AMBER", dict(cand=(_renumber(C), M), want={**G, "t_f.core": "AMBER"}, code=0, cls=("t_f.core", "callee-index"))),
        ("AMBER under --strict exits 1", dict(cand=(_renumber(C), M), strict=True, want={**G, "t_f.core": "AMBER"}, code=1)),
        ("instruction change -> RED", dict(cand=(C.replace("const u64 7", "const u64 8"), M), want={**G, "t_m.core": "RED"}, code=1)),
        ("function missing in candidate -> RED", dict(cand=(C.split("fn @<k::S")[0], M), want={**G, "t_m.core": "RED"}, code=1, why=("t_m.core", "ABSENT"))),
        ("pinned sha mismatch -> REFUSED", dict(tweak=lambda p: p["t_m.core"].update(dump_sha256="0" * 64), want={**G, "t_m.core": "REFUSED"}, code=2)),
        ("instance-installed -> RED", dict(flip=_flip("k::Tr::m", "k::S"), want={**G, "t_m.core": "RED"}, code=1, why=("t_m.core", "def+args"))),
        ("instance other args, same def -> RED fail-closed", dict(flip=_flip("k::Tr::m", "k::Q"), want={**G, "t_m.core": "RED"}, code=1, why=("t_m.core", "fail-closed"))),
        ("instance on another def does not fire", dict(flip=_flip("k::Other::m", "k::S"), want=G, code=0)),
        ("flip log not bound to candidate -> REFUSED", dict(flip=_flip("k::Tr::m", "k::S", lineage="sha256:" + "ee" * 32), refused_run=True)),
        ("unparseable INSTANCE INSTALLED line -> REFUSED", dict(flip="trust-ir-flip: x\ntrust-ir-instance-flip: INSTANCE INSTALLED, def=garbage\n", refused_run=True)),
        ("referent changed, text identical -> RED", dict(cand=(C.replace("{ struct.0, u8 }", "{ struct.0, u16 }"), M), want={**G, "t_f.core": "RED"}, code=1, why=("t_f.core", "referent struct.1"), tv=("t_f.core", "GREEN"))),
        ("callee retargeted to another name -> RED", dict(cand=(C.replace("@func.1(", "@func.2("), M), want={**G, "t_f.core": "RED"}, code=1, why=("t_f.core", "callee-name"))),
        ("inconsistent renumbering -> RED", dict(cand=(C.replace("undef struct.1", "undef struct.0"), M), want={**G, "t_f.core": "RED"}, code=1, why=("t_f.core", "inconsistent"))),
        ("chain function change -> RED", dict(cand=(C.replace("load u64", "load u32"), M), want={**G, "t_f.core": "RED", "t_z.core": "RED"}, code=1)),
        ("calling convention changed -> RED", dict(cand=(C.replace("fn @<k::S", "rustcc fn @<k::S"), M), want={**G, "t_m.core": "RED"}, code=1)),
        ("producer changed -> RED", dict(cand=(C.replace("trust-ir\nbb0(%0: ptr):\n    %1 = const", "trust\nbb0(%0: ptr):\n    %1 = const"), M), want={**G, "t_m.core": "RED"}, code=1, why=("t_m.core", "producer"))),
        ("proof annotation only -> AMBER annotation", dict(cand=(C.replace("; #proof: fresh_symbolic_havoc", "; #proof: other"), M), want={**G, "t_f.core": "AMBER"}, code=0, cls=("t_f.core", "annotation"))),
        ("main-module loc + callee renumber -> AMBER", dict(cand=(C, _renumber_main(M)), want={**G, "t_z.core": "AMBER"}, code=0, cls=("t_z.core", "callee-index"))),
        ("pinned dump missing -> REFUSED", dict(tweak=lambda p: p["t_f.core"].update(dump="/nonexistent/x.trust-ir.bin"), want={**G, "t_f.core": "REFUSED"}, code=2)),
        ("pinned index names another function -> REFUSED", dict(tweak=lambda p: p["t_m.core"].update(artifact_func_index=1), want={**G, "t_m.core": "REFUSED"}, code=2)),
        ("merged chain index out of range -> REFUSED", dict(tweak=lambda p: p["t_z.core"]["chain_functions"][2].update(artifact_func_id=9), want={**G, "t_z.core": "REFUSED"}, code=2)),
        ("candidate truncated mid-function -> REFUSED", dict(cand=(C[: C.index("ret %3")], M), want={"t_f.core": "REFUSED", "t_m.core": "REFUSED", "t_z.core": "REFUSED"}, code=2)),
        ("candidate manifest byte count wrong -> REFUSED", dict(manifest_bytes=1, want={"t_f.core": "REFUSED", "t_m.core": "REFUSED", "t_z.core": "REFUSED"}, code=2)),
        ("RED outranks REFUSED overall", dict(cand=(C.replace("const u64 7", "const u64 8"), M), tweak=lambda p: p["t_f.core"].update(dump_sha256="0" * 64), want={**G, "t_f.core": "REFUSED", "t_m.core": "RED"}, code=1)),
    ]
    # M2 (2026-09-27): trust-ir WS4.3 prints a non-bare symbol QUOTED. The SAME program printed so
    # is the same program: every function is located by its decoded name and every compared text
    # carries the legacy spelling. RED under the `fn @(.*)` reader this replaced (ABSENT: the
    # quotes were part of the name), and the REFUSED arms are what the shared reader adds.
    QC, QM = tir_symbols.respell_ws43(C), tir_symbols.respell_ws43(M)
    assert '"k::f::<__trust_args@aa>"' in QC and '@"lvl::L::is_zero"' in QM, (QC, QM)
    raw_g = f"fn @{_NAMES['g']}(functy.1) {{"
    R = {"t_f.core": "REFUSED", "t_m.core": "REFUSED", "t_z.core": "REFUSED"}
    arms += [
        ("WS4.3 quoted-symbol candidate of the same program -> GREEN", dict(cand=(QC, QM), want=G, code=0)),
        ("WS4.3 pinned AND candidate -> GREEN", dict(pin=(QC, QM), cand=(QC, QM), want=G, code=0)),
        ("WS4.3 pinned, legacy candidate -> GREEN", dict(pin=(QC, QM), want=G, code=0)),
        ("WS4.3 candidate, one instruction changed -> RED", dict(cand=(QC.replace("const u64 7", "const u64 8"), QM), want={**G, "t_m.core": "RED"}, code=1)),
        ("a module mixing quoted and raw symbols -> REFUSED", dict(cand=(QC.replace(f"fn @{tir_symbols.spell_symbol(_NAMES['g'])}(functy.1) {{", raw_g), M), want=R, code=2, why=("t_f.core", "mixes a QUOTED"))),
        ("an escape the printer cannot write -> REFUSED", dict(cand=(QC.replace('"k::f::<__trust_args@aa>"', '"k::f::<__trust\\qargs@aa>"'), M), want=R, code=2, why=("t_f.core", "is not one the trust-ir printer emits"))),
        ("a quoted bare-able name -> REFUSED", dict(cand=(C.replace("struct @S {", 'struct @"S" {'), M), want=R, code=2, why=("t_f.core", "bare alphabet"))),
    ]
    return arms


def self_test() -> int:
    ff.selftest_classifier()
    assert def_match("MemoizedSubst::memo_depth", "expr::subst::MemoizedSubst::memo_depth")
    assert not def_match("<Instantiator<'_> as MemoizedSubst>::memo_depth", "expr::subst::MemoizedSubst::memo_depth")
    assert def_match("infer::<impl TypeChecker<'env>>::infer_type", "tc::infer::<impl tc::TypeChecker<'env>>::infer_type")
    assert args_match("expr::subst::LevelParamSubst<'{erased}>",
                      "<clean_kernel::expr::subst::LevelParamSubst<'_> as clean_kernel::expr::subst::MemoizedSubst>::memo_depth::<__trust_args@f4>")
    assert not args_match("expr::subst::LevelParamSubst<'{erased}>",
                          "<clean_kernel::expr::subst::LevelParamSubstSlice<'_> as clean_kernel::expr::subst::MemoizedSubst>::memo_depth::<__trust_args@44>")
    failed: list[str] = []
    arms = _arms()
    for label, arm in arms:
        with tempfile.TemporaryDirectory(prefix="link4join-") as tmp:
            t = Path(tmp)
            pc, pm = arm.get("pin", (_PIN_CALLEES, _PIN_MAIN))
            _write_dump(t / "pin", pc, pm)
            _write_provs(t / "prov", t / "pin", arm.get("tweak"))
            cc, cm = arm.get("cand", (_PIN_CALLEES, _PIN_MAIN))
            _write_dump(t / "cand", cc, cm)
            if arm.get("manifest_bytes"):
                mp = t / "cand" / CALLEES_MANIFEST
                doc = json.loads(mp.read_text())
                doc["artifacts"]["text_bytes"] += arm["manifest_bytes"]
                mp.write_text(json.dumps(doc))
            flip = None
            if "flip" in arm:
                flip = t / "flip.txt"
                flip.write_text(arm["flip"], encoding="utf-8")
            try:
                code, report = run(t / "prov", t / "cand", flip, arm.get("strict", False))
            except Refused as exc:
                if not arm.get("refused_run"):
                    failed.append(f"{label}: refused unexpectedly: {exc}")
                continue
            except Exception as exc:  # a crash is a failed arm, never a pass
                failed.append(f"{label}: crashed: {type(exc).__name__}: {exc}")
                continue
            if arm.get("refused_run"):
                failed.append(f"{label}: expected a REFUSED run, got {report['verdict']}")
                continue
            got = {k: v["verdict"] for k, v in report["modules"].items()}
            if got != arm["want"] or code != arm["code"]:
                failed.append(f"{label}: want {arm['want']} exit {arm['code']}, got {got} exit {code}")
            if "cls" in arm and arm["cls"][1] not in report["modules"][arm["cls"][0]].get("classes", []):
                failed.append(f"{label}: class {arm['cls'][1]} missing: {report['modules'][arm['cls'][0]]}")
            if "tv" in arm and report["modules"][arm["tv"][0]].get("text_verdict") != arm["tv"][1]:
                failed.append(f"{label}: text-alone verdict is not {arm['tv'][1]}: {report['modules'][arm['tv'][0]]}")
            if "why" in arm and not any(arm["why"][1] in r for r in report["modules"][arm["why"][0]]["reasons"]):
                failed.append(f"{label}: no reason mentions {arm['why'][1]!r}: {report['modules'][arm['why'][0]]['reasons']}")
    for f in failed:
        print(f"  FAILED {f}")
    print(f"SELFTEST={'ok' if not failed else 'FAIL'} arms={len(arms)} failed={len(failed)}")
    return 0 if not failed else 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--dump", type=Path, help="the CANDIDATE dump directory (a TRUST_IR_BUILD_DUMP)")
    ap.add_argument("--flip-log", type=Path, default=None, help="the candidate build's flip log")
    ap.add_argument("--strict", action="store_true", help="AMBER fails too")
    ap.add_argument("--json", type=Path, default=None, help="write the machine-readable report here")
    ap.add_argument("--prov-dir", type=Path, default=PROV_DIR, help=argparse.SUPPRESS)
    ap.add_argument("--self-test", action="store_true", help="run the synthetic mutation arms")
    ap.add_argument("--pinned-inputs", action="store_true",
                    help="print the first-party modules this script runs besides itself; run nothing")
    args = ap.parse_args()
    if args.pinned_inputs:
        print("\n".join(tir_symbols.first_party_imports(Path(__file__))))
        return 0
    if args.self_test:
        return self_test()
    if args.dump is None:
        print("LINK4_JOIN=REFUSED: --dump <candidate-dir> is required", file=sys.stderr)
        return 2
    try:
        code, report = run(args.prov_dir, args.dump, args.flip_log, args.strict)
    except Refused as exc:
        print(f"REFUSED: {exc}")
        print("LINK4_JOIN=REFUSED green=0 amber=0 red=0 refused=0")
        return 2
    except Exception as exc:  # an internal crash is not a verdict; exit 1 would read as RED
        import traceback
        traceback.print_exc()
        print(f"LINK4_JOIN=REFUSED internal error: {type(exc).__name__}: {exc}")
        return 2
    print("\n".join(render(report)))
    if args.json:
        args.json.write_text(json.dumps(report, indent=1) + "\n", encoding="utf-8")
        print(f"report: {args.json}")
    return code


if __name__ == "__main__":
    sys.exit(main())
