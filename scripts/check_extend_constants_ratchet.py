#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""Fail-closed ratchet for the extend_constants_* bulk-import bypass (#4).

extend_constants_unchecked / extend_constants_structural register constants in
bulk, bypassing per-declaration kernel type-checking. This scanner enumerates
every source `.extend_constants_*(` call site under crates/ and asserts each is
accounted for in data/unchecked_decl_ratchet.json (production_sites) and that
the production counts do not exceed the recorded baseline. A NEW, unaccounted
bypass fails the gate — forcing a // SOUNDNESS: comment + an explicit ratchet
entry before it can land.

WHY IT ACCOUNTS PER SITE (2026-08-25, lane LOOSE)
-------------------------------------------------
`production_sites` used to be read as a SET of (file, method) pairs. That is a
BLANKET suppression at FILE granularity — the same shape as the
`test_excluded_sites` skip list retired one layer up the same day, and it was
equally live. MEASURED at 0b3b94e5b:
crates/clean-mathverse/src/cli/per_constant_load.rs carried TWO calls (lines
1762 and 1767) under ONE row that declared no count, so a THIRD would have been
accepted with no entry of its own — bounded only by an aggregate that a
simultaneous removal elsewhere keeps flat. Its own `trust` text already said
"2 call sites"; nothing read it.

Two rules now, both lifted from the sibling scripts/check_add_decl_ratchet.py,
which has capped per site since 2026-08-22:

  * `occurrences` (default 1) CAPS the calls a row covers. More is RED; fewer
    is a NOTE to lower it. A non-positive or unparsable value is REFUSED, not
    read as "unlimited".
  * every accounted call must carry a `// SOUNDNESS:` comment within
    SOUNDNESS_WINDOW (40) lines above it. This gate has ASKED for that comment
    in its remediation text since 2026-06-17 and never checked it, while the
    ratchet file CLAIMED "each production site below carries a // SOUNDNESS:
    comment at its call". At HEAD all seven do; that is now a measurement.

WHY IT LEXES (2026-08-25, lane ANTICORR)
----------------------------------------
Until this change the scanner ran its regex over RAW LINES. It therefore
counted the token wherever it appeared — including inside a `//` comment, a
doc comment, or a string literal. That is the same defect that killed
`prover_phase_0_audit.sh` (see the `retired` list in data/gate_registry.json),
and here it was not merely loose, it was ANTI-CORRELATED with the property the
gate exists to protect, in the most direct way possible: the gate's OWN
remediation text says

    -> add a // SOUNDNESS: comment at the call AND an entry under
       data/unchecked_decl_ratchet.json

and writing that comment — if it quoted the call, which is the natural way to
write it — was itself a new "unaccounted call site". MEASURED 2026-08-25 at
438a64131: a two-line `// SOUNDNESS:` comment planted in
crates/clean-kernel/src/env/snapshot.rs reading

    // SOUNDNESS: this path deliberately does NOT call
    // env.extend_constants_unchecked(decls); every constant is re-checked.

turned this gate RED (`FAIL: unaccounted extend_constants_* bulk-bypass call
site(s): crates/clean-kernel/src/env/snapshot.rs:13`, exit=1) while
scripts/check_add_decl_ratchet.py — the parser-based sibling, on the same tree,
with the same plant — printed `OK` and exit 0. A gate that reddens on the
documentation it demands trains people to delete the documentation.

So the scanner now does what its two siblings
(scripts/check_add_decl_ratchet.py, scripts/check_env_bypass_census.py) already
did:

  * comments (line and block), string/char/raw-string literals are BLANKED
    before matching, line numbers preserved;
  * inline `#[cfg(test)] mod` blocks are excluded by brace tracking, in
    addition to the test-FILE predicate that was already here — and the
    tracker fails CLOSED, so a file whose braces do not balance is an error,
    never a silent skip.

`--selftest` pins all of that with mutation arms, including the exact plant
above; the gate runs it before every measurement, so a green from the gate is
also a statement that the gate can still say no.

Wired into scripts/local_gate.sh. Pure-stdlib; no cargo build required.

`--selftest` includes the lexing and per-site controls, plus a standing plant
in an isolated copy of the real scanner inputs. The real snapshot.rs bytes,
module graph and ratchet remain authoritative; no live kernel file is written.

Usage:
    python3 scripts/check_extend_constants_ratchet.py
    python3 scripts/check_extend_constants_ratchet.py --selftest
"""
from __future__ import annotations

import contextlib
import hashlib
import io
import json
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import time
import types
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
RATCHET_REL = Path("data") / "unchecked_decl_ratchet.json"
CRATES_REL = Path("crates")

# Dot-call form only: `<recv>.extend_constants_unchecked(` / `..._structural(`.
# This deliberately does NOT match the method definitions (`fn extend_constants_*`
# in env/registration.rs) or the trait delegation (`Environment::extend_constants_*`
# in env/trusted_ext.rs, a `::` call). Doc comments and string literals are not
# excluded by the REGEX — they are erased by strip_noncode() before it runs.
# CLOSED BY CONSTRUCTION (audit r11 M11-5). This was dot-only, and it is the
# SOLE gate over the bulk doors -- the env-bypass census hands them off via
# POINTER_METHODS and there is no Rust mirror. Measured at env/snapshot.rs:
# `env.extend_constants_unchecked(cs)` fired, while `Environment::...`,
# `TrustedEnvExt::...`, `<Environment as TrustedEnvExt>::...` and `Self::...`
# were ALL byte-identical to baseline -- and TrustedEnvExt is `pub use`-exported,
# so any of the 27 crates could spell it. Same rule as add_decl now: the NAME in
# call position, minus a definition. A list of accepted prefixes is always one
# spelling short.
CALL_RE = re.compile(r"\bextend_constants_(unchecked|structural)\s*\(")
DEFINITION_RE = re.compile(r"\bfn\s+extend_constants_(unchecked|structural)\s*[(<]")
QUICK_RE = re.compile(r"extend_constants_(unchecked|structural)")
CFG_TEST_RE = re.compile(r"#\[\s*cfg\s*\(\s*test\s*\)\s*\]")
MOD_RE = re.compile(r"\bmod\b")

# PER-SITE JUSTIFICATION (2026-08-25, lane LOOSE). Read on the RAW text, not
# the blanked text: this is the one place the gate WANTS the prose.
SOUNDNESS_RE = re.compile(r"//.*\bSOUNDNESS\b")
SOUNDNESS_WINDOW = 40

# The Rust lexer and the test-code classifier -- which crates/**/*.rs files
# rustc compiles only under cfg(test) -- are check_add_decl_ratchet.py's, executed
# from its source (ignored bytecode is not an input) rather than re-typed. Until
# 2026-11-16 this gate carried a byte-identical copy of both, ~1150 lines kept in
# step by hand; one copy is one rule by construction. check_gate_registry.py R7
# pins it through `--pinned-inputs`.
_reference = types.ModuleType("check_extend_constants_reference")
_reference.__file__ = str(Path(__file__).resolve().parent / "check_add_decl_ratchet.py")
exec(compile(Path(_reference.__file__).read_bytes(), _reference.__file__, "exec", dont_inherit=True),
     _reference.__dict__)

strip_noncode = _reference.strip_noncode
lexer_failures = _reference.lexer_failures
_LEXER_CASES = _reference._LEXER_CASES
_CFG_HEAD_CASES = _reference._CFG_HEAD_CASES
_CFG_LATTICE_CASES = _reference._CFG_LATTICE_CASES
_CLASSIFY_CACHE = _reference._CLASSIFY_CACHE
_EDGE_CASES = _reference._EDGE_CASES
_INCLUDE_CASES = _reference._INCLUDE_CASES
_MODULE_TREE_CASES = _reference._MODULE_TREE_CASES
_UNRESOLVED_EDGES = _reference._UNRESOLVED_EDGES
cfg_lattice_failures = _reference.cfg_lattice_failures
edge_extractor_failures = _reference.edge_extractor_failures
is_production_file = _reference.is_production_file
is_test_like = _reference.is_test_like
module_tree_failures = _reference.module_tree_failures

ANSWERS_PINNED_INPUTS = True
PINNED_INPUTS = ("scripts/check_add_decl_ratchet.py",)


def scan_file(path: Path, rel: Path) -> list[dict]:
    """Production `.extend_constants_*(` hits in one file.

    Comments and literals are erased first; inline `#[cfg(test)] mod` bodies are
    skipped by brace tracking. Raises on unbalanced braces (fail closed)."""
    raw_text = path.read_text(errors="strict")
    if not QUICK_RE.search(raw_text):
        return []
    lines = strip_noncode(raw_text).splitlines()
    prod: list[dict] = []
    in_cfg_test = False
    depth = 0
    pending_cfg = False
    for lineno, line in enumerate(lines, 1):
        if not in_cfg_test:
            if CFG_TEST_RE.search(line):
                pending_cfg = True
                continue
            if pending_cfg:
                if MOD_RE.search(line):
                    if "{" in line:
                        in_cfg_test = True
                        depth = line.count("{") - line.count("}")
                        if depth <= 0:
                            in_cfg_test = False
                    pending_cfg = False
                    continue
                if line.strip():
                    pending_cfg = False
        else:
            depth += line.count("{") - line.count("}")
            if depth <= 0:
                in_cfg_test = False
            continue
        # AUDIT r12 M12-4: the definition exclusion was LINE-granular, so a real
        # call sharing a line with a matching `fn` header was dropped whole --
        # measured with a one-line `#[rustfmt::skip] impl BackdoorExt for
        # Environment { fn extend_constants_unchecked(..) { Environment::extend_constants_unchecked(self, d) } }`
        # in a production kernel file: rc=0 on one line, rc=1 split over two.
        # Definitions are removed from the SPAN they occupy; calls elsewhere on
        # the line still count.
        line = DEFINITION_RE.sub(lambda m: " " * len(m.group(0)), line)
        if False:
            # a definition is not a use of the door (audit r11 M11-5)
            continue
        for m in CALL_RE.finditer(line):
            prod.append(
                {
                    "file": str(rel),
                    "line": lineno,
                    "method": f"extend_constants_{m.group(1)}",
                }
            )
    if in_cfg_test:
        raise ValueError(
            f"{rel}: a #[cfg(test)] mod block never closed (brace tracking ran off the "
            f"end of the file). Refusing to classify this file — fix the source or the "
            f"tracker; an unreadable file is not a clean one."
        )
    return prod



# AUDIT r15 M15-2 leg B: a justification must BELONG to the site it justifies.
# The window was `lineno - 1 - SOUNDNESS_WINDOW` unconditionally -- "is there
# ANY `// SOUNDNESS:` above" -- so in a file whose commented sites sit closer
# together than the window, every site is covered by its NEIGHBOUR's comment.
# Measured in crates/clean-kernel/src/env/trusted_ext.rs, whose 32 blocks sit
# 6-11 lines apart: per block, 31 of the 32 comments could be deleted with every
# gate still green, though each block's own text says removing it makes the call
# COUNTED. The floor is now the nearest of the window, the previous watched CALL
# in this file, and the top of the enclosing `fn`'s attribute/doc run.
_OWNER_FN_RE = re.compile(r"\bfn\s+[A-Za-z0-9_]+\s*[(<]")


def _owner_floor(lines: list[str], lineno: int, prev_call_line: int = 0) -> int:
    floor = max(0, lineno - 1 - SOUNDNESS_WINDOW)
    if prev_call_line:
        floor = max(floor, prev_call_line)
    i = lineno - 1
    while i > 0:
        if _OWNER_FN_RE.search(lines[i - 1]):
            j = i - 1
            while j > 0 and lines[j - 1].strip().startswith(("#[", "///", "//!")):
                j -= 1
            floor = max(floor, j)
            break
        i -= 1
    return floor


def has_soundness_comment(raw_lines: list[str], lineno: int,
                          prev_call_line: int = 0) -> bool:
    """True if a `// SOUNDNESS:` comment that BELONGS to this site sits above it.
    Same rule and window as the sibling scripts/check_add_decl_ratchet.py."""
    start = _owner_floor(raw_lines, lineno, prev_call_line)
    return any(SOUNDNESS_RE.search(l) for l in raw_lines[start:lineno])


def load_ratchet(root: Path) -> dict:
    try:
        data = json.loads((root / RATCHET_REL).read_text())
    except (OSError, json.JSONDecodeError) as exc:  # fail closed
        sys.exit(f"FAIL: cannot read {root / RATCHET_REL}: {exc}")
    block = data.get("extend_constants")
    if not isinstance(block, dict):
        sys.exit(f"FAIL: {root / RATCHET_REL} missing the 'extend_constants' block (#4).")
    return block


def run(root: Path) -> int:
    # AUDIT r15/r16: caches are keyed on the ROOT alone and the unresolved-edge
    # residue accumulates per pass; production runs once, a selftest does not.
    _CLASSIFY_CACHE.clear()
    _UNRESOLVED_EDGES.clear()
    block = load_ratchet(root)
    # PER-SITE, not per (file, method) BLANKET (2026-08-25, lane LOOSE).
    #
    # `production_sites` used to be read as a SET of (file, method) pairs, with
    # only the repo-wide `*_production_count` behind it. That is a blanket
    # suppression at file granularity and it was live: a second, undeclared
    # `env.extend_constants_structural(...)` in an already-listed file was
    # accepted with no entry of its own, bounded only by an aggregate that a
    # simultaneous removal elsewhere could keep flat. MEASURED at 0b3b94e5b:
    # crates/clean-mathverse/src/cli/per_constant_load.rs carried TWO calls
    # (lines 1762 and 1767) under ONE row that declared no count -- exactly the
    # `test_excluded_sites` shape lane ANTICORR retired one layer up.
    #
    # Two rules now, both taken from the sibling check_add_decl_ratchet.py:
    #   * `occurrences` (default 1) CAPS how many calls a row may cover, so a
    #     sanctioned site cannot quietly gain a neighbour;
    #   * every accounted call must carry its own `// SOUNDNESS:` comment within
    #     SOUNDNESS_WINDOW lines above it -- the half of the CLAUDE.md rule this
    #     gate has always ASKED for in its remediation text and never checked.
    declared: dict[tuple[str, str], int] = {}
    for s in block.get("production_sites", []):
        if "file" not in s or "method" not in s:
            continue
        try:
            occurrences = int(s.get("occurrences", 1))
        except (TypeError, ValueError):
            occurrences = -1
        if occurrences < 1:
            print(
                f"FAIL: production_sites row {s.get('file')} / {s.get('method')} has a "
                f"non-positive `occurrences`; a row justifies at least one call site.",
                file=sys.stderr,
            )
            return 1
        declared[(s["file"], s["method"])] = occurrences
    prod = set(declared)
    # `test_excluded_sites` is RETIRED, and refused rather than ignored.
    #
    # It was a hand-maintained list of (file, method) pairs to skip, written
    # because the old scanner could not see inline `#[cfg(test)] mod` blocks. It
    # is a BLANKET suppression of the pair: MEASURED 2026-08-25 (lane ANTICORR),
    # a real production `env.extend_constants_unchecked(cs)` planted in
    # crates/clean-olean/src/import/load_register.rs -- one of the six listed
    # files -- was accepted silently, exit 0, by the gate whose whole job is to
    # refuse exactly that. All six rows were dead: with the list emptied the
    # brace-tracked cfg(test) exclusion below keeps the gate green on its own.
    stale_excludes = [
        f"{s.get('file')}  {s.get('method')}"
        for s in block.get("test_excluded_sites", [])
        if "file" in s and "method" in s
    ]
    base_unchecked = int(block.get("unchecked_production_count", -1))
    base_structural = int(block.get("structural_production_count", -1))

    counts = {"unchecked": 0, "structural": 0}
    unaccounted: list[str] = []
    unjustified: list[str] = []
    seen: dict[tuple[str, str], int] = {}

    for path in sorted((root / CRATES_REL).rglob("*.rs")):
        rel = path.relative_to(root)
        # AUDIT r14 M14-1/M14-2: ONE target-side question. A file the compiler
        # reaches without a cfg(test) gate is production, whatever its name and
        # whatever any declaring file says; everything else that looks like test
        # code is excluded. This replaces the declaring-side stack (name
        # substring -> cfg(test)#[path] grep -> crate-wide mod grep -> proximity
        # window), through which round 14 measured six independent escapes.
        if not is_production_file(path) and is_test_like(path, rel):
            # test-only by NAME, or by being included solely through a
            # `#[cfg(test)] #[path=...] mod` declaration (audit r11 M11-3)
            continue
        try:
            hits = scan_file(path, rel)
        except OSError as exc:
            sys.exit(f"FAIL: cannot read {rel}: {exc}")
        except ValueError as exc:
            print(f"FAIL: {exc}", file=sys.stderr)
            return 1
        # Re-read for the SOUNDNESS-comment window: `scan_file` returns blanked
        # text, and this is the one place the gate wants the prose. Fail CLOSED
        # if the second read does not agree with the first.
        raw_lines: list[str] = []
        if hits:
            try:
                raw_lines = path.read_text(errors="strict").splitlines()
            except OSError as exc:
                print(f"FAIL: cannot re-read {rel} for its justification: {exc}", file=sys.stderr)
                return 1
        _prev_hit_line = 0
        for hit in hits:
            key = (hit["file"], hit["method"])
            _prev, _prev_hit_line = _prev_hit_line, hit["line"]
            if key in prod:
                counts[hit["method"].removeprefix("extend_constants_")] += 1
                seen[key] = seen.get(key, 0) + 1
                if not has_soundness_comment(raw_lines, hit["line"], _prev):
                    unjustified.append(f"{hit['file']}:{hit['line']}  {hit['method']}")
                continue
            unaccounted.append(f"{hit['file']}:{hit['line']}  {hit['method']}")

    ok = True
    for key, occurrences in sorted(declared.items()):
        found = seen.get(key, 0)
        if found > occurrences:
            ok = False
            print(
                f"FAIL: {key[0]} / {key[1]} has {found} production call sites but is "
                f"justified for {occurrences}. A sanctioned site is NOT a blanket "
                f"suppression of the file: give the new call its own row (or raise "
                f"`occurrences` with a justification that covers it).",
                file=sys.stderr,
            )
        elif found < occurrences:
            print(
                f"NOTE: {key[0]} / {key[1]} declares occurrences={occurrences} but "
                f"{found} were measured; lower it."
            )
    if unjustified:
        ok = False
        print(
            "FAIL: accounted extend_constants_* call site(s) with no // SOUNDNESS: "
            f"comment within {SOUNDNESS_WINDOW} lines above:",
            file=sys.stderr,
        )
        for u in unjustified:
            print(f"  {u}", file=sys.stderr)
        print(
            "  -> the ratchet entry is only half the rule. CLAUDE.md requires the "
            "justification AT THE CALL; data/unchecked_decl_ratchet.json has always "
            "CLAIMED every site carries one, and until 2026-08-25 nothing checked it.",
            file=sys.stderr,
        )
    if stale_excludes:
        ok = False
        print(
            "FAIL: data/unchecked_decl_ratchet.json -> extend_constants still lists "
            "test_excluded_sites, which is RETIRED:",
            file=sys.stderr,
        )
        for s in stale_excludes:
            print(f"  {s}", file=sys.stderr)
        print(
            "  -> the scanner now excludes inline #[cfg(test)] mod blocks by brace "
            "tracking, so the list is unnecessary; and it is a BLANKET (file, method) "
            "suppression that hides a future PRODUCTION bypass in the same file "
            "(measured 2026-08-25 in crates/clean-olean/src/import/load_register.rs). "
            "Delete the key.",
            file=sys.stderr,
        )
    if unaccounted:
        ok = False
        print("FAIL: unaccounted extend_constants_* bulk-bypass call site(s):", file=sys.stderr)
        for u in unaccounted:
            print(f"  {u}", file=sys.stderr)
        print(
            "  -> add a // SOUNDNESS: comment at the call AND a production_sites "
            "entry under data/unchecked_decl_ratchet.json -> extend_constants. "
            "(test_excluded_sites is RETIRED: inline #[cfg(test)] mod blocks are "
            "excluded automatically, and the list hid production bypasses.)",
            file=sys.stderr,
        )

    for label, found, base in (
        ("unchecked", counts["unchecked"], base_unchecked),
        ("structural", counts["structural"], base_structural),
    ):
        if found > base:
            ok = False
            print(
                f"FAIL: {label} production bypass count {found} exceeds baseline {base} "
                f"(data/unchecked_decl_ratchet.json). New bypass must be justified + ratcheted.",
                file=sys.stderr,
            )
        elif found < base:
            # Improvement — allowed, but the baseline is now stale.
            print(
                f"NOTE: {label} production bypass count {found} is BELOW baseline {base}; "
                f"lower extend_constants.{label}_production_count in the ratchet.",
            )

    if ok:
        print(
            f"OK: extend_constants bypass ratchet — "
            f"unchecked={counts['unchecked']}/{base_unchecked}, "
            f"structural={counts['structural']}/{base_structural} production sites accounted for."
        )
        return 0
    return 1


# ---------------------------------------------------------------------------
# Self-test: the gate must be able to say NO, and must NOT say no to prose.
# ---------------------------------------------------------------------------

def _selftest_tree() -> Path:
    """A minimal fake repo the mutation arms can edit freely."""
    tmp = Path(tempfile.mkdtemp(prefix="extend_constants_selftest_"))
    # AUDIT r15 M15-1: without a `.git`, `_repo_root_of` returns None, so
    # `is_production_file` is False and `is_test_like` falls back to the NAME
    # predicate -- i.e. `classify_paths`, the whole target-side rule round 14
    # introduced, was reached by NO selftest arm in any of the three scanners.
    # One mkdir makes every arm below exercise it.
    (tmp / ".git").mkdir()
    (tmp / "data").mkdir()
    (tmp / "crates" / "c" / "src").mkdir(parents=True)
    (tmp / "data" / RATCHET_REL.name).write_text(
        json.dumps(
            {
                "extend_constants": {
                    "unchecked_production_count": 0,
                    "structural_production_count": 0,
                    "production_sites": [],
                    "test_excluded_sites": [],
                }
            },
            indent=2,
        )
    )
    (tmp / "crates" / "c" / "src" / "lib.rs").write_text(
        "pub fn clean() {}\n"
        "\n"
        "#[cfg(test)]\n"
        "mod tests {\n"
        "    use super::*;\n"
        "    #[test]\n"
        "    fn t() {\n"
        "        env.extend_constants_unchecked(d);\n"
        "    }\n"
        "}\n"
    )
    return tmp


def _write_ratchet(root: Path, doc: dict) -> None:
    (root / RATCHET_REL).write_text(json.dumps(doc, indent=2))


def _read_ratchet(root: Path) -> dict:
    return json.loads((root / RATCHET_REL).read_text())


def _quiet_run(root: Path) -> tuple[int, str]:
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
        rc = run(root)
    return rc, buf.getvalue()


def _arm(name: str, root: Path, expect: int, contains: tuple[str, ...] = ()) -> bool:
    rc, captured = _quiet_run(root)
    good = rc == expect and all(text in captured for text in contains)
    print(f"  [{'ok ' if good else 'FAIL'}] {name}: exit {rc} (expected {expect})")
    if not good and captured:
        print("    --- the arm's own output ---")
        for line in captured.rstrip("\n").splitlines():
            print(f"    {line}")
    return good


PLANT = "\npub fn smuggle(env: &mut E, d: D) { env.extend_constants_unchecked(d); }\n"
# The same plant WITH the per-site justification CLAUDE.md requires at the call.
PLANT_JUSTIFIED = "\n// SOUNDNESS: selftest justification.\n" + PLANT.lstrip("\n")
# Two justified calls in ONE file: legal only if the row declares occurrences=2.
PLANT_JUSTIFIED_TWICE = PLANT_JUSTIFIED + PLANT_JUSTIFIED.replace("smuggle", "smuggle2")

# The exact prose that turned the OLD, raw-line scanner RED (see the header).
SOUNDNESS_PROSE = (
    "\n// SOUNDNESS: this path deliberately does NOT call\n"
    "// env.extend_constants_unchecked(decls); every constant is re-checked.\n"
)


def _git_clean(rel: str) -> bool:
    """True iff `rel` matches HEAD with nothing staged and nothing in the worktree."""
    for args in (["diff", "--quiet", "--", rel], ["diff", "--quiet", "--cached", "--", rel]):
        r = subprocess.run(["git", "-C", str(REPO_ROOT), *args], capture_output=True, check=False)
        if r.returncode != 0:
            return False
    return True


def _scanner_inputs(root: Path) -> list[Path]:
    """The complete input closure of run()/classify_paths(), not a Git inventory."""
    scope = root / CRATES_REL
    if not scope.is_dir() or scope.is_symlink():
        raise ValueError(f"scanner input directory is absent or symlinked: {scope}")
    sources = []
    for path in scope.rglob("*"):
        # Even an untraversed directory symlink can redirect a resolved module
        # edge. Omitting it would silently change the classifier's authority.
        if path.is_symlink() or path.name == ".git":
            raise ValueError(f"symlinked scanner input or nested repository marker: {path}")
        if path.name.endswith(".rs"):
            sources.append(path.relative_to(root))
    return [RATCHET_REL, *sorted(sources)]


def _scanner_input(root: Path, rel: Path) -> tuple[bytes, tuple]:
    path = root / rel
    if path.resolve() != path:
        raise ValueError(f"refusing symlinked scanner input: {rel}")
    before = path.stat()
    if not stat.S_ISREG(before.st_mode):
        raise ValueError(f"scanner input is not a regular file: {rel}")
    data = path.read_bytes()
    after = path.stat()

    def identity(info):
        return (info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns, info.st_ctime_ns)

    if identity(before) != identity(after):
        raise ValueError(f"scanner input changed while reading: {rel}")
    return data, (hashlib.sha256(data).digest(), identity(after))


def _scanner_input_state(root: Path) -> dict:
    return {rel: _scanner_input(root, rel)[1] for rel in _scanner_inputs(root)}


def _copy_scanner_inputs(source: Path, destination: Path) -> dict:
    """Copy every source/ledger byte independently; never link to the live tree."""
    source, destination = source.resolve(), destination.resolve()
    if source == destination or source in destination.parents or destination in source.parents:
        raise ValueError("scanner snapshot must not overlap the source tree")
    if any(destination.iterdir()):
        raise ValueError("scanner snapshot destination must be empty")
    state = {}
    for rel in _scanner_inputs(source):
        data, state[rel] = _scanner_input(source, rel)
        target = destination / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        with target.open("xb") as stream:
            stream.write(data)
        if target.read_bytes() != data:
            raise ValueError(f"scanner snapshot copy differs: {rel}")
    # This marker is essential: without it _repo_root_of bypasses the real
    # module classifier. No Git index, caches, or synthetic ratchet is copied.
    (destination / ".git").mkdir()
    if _scanner_input_state(source) != state:
        raise ValueError("scanner inputs changed while copying; refusing an incoherent baseline")
    return state


def _standing_plant_arms(root: Path, lock: Path) -> tuple[int, int, int]:
    """Real-input falsification without writing or restoring any live input."""
    root = root.resolve()
    rel = Path("crates/clean-kernel/src/env/snapshot.rs")
    real = root / rel
    holding = False
    for _ in range(600):
        try:
            lock.mkdir()
            holding = True
            break
        except FileExistsError:
            time.sleep(0.1)
    passed = failed = 0

    def check(name, copy, expect, contains=()):
        nonlocal passed, failed
        good = _arm(name, copy, expect, contains)
        passed += int(good)
        failed += int(not good)
        return good

    try:
        if not holding:
            print(f"  [SKIP] REAL INPUT arms: another selftest has held {lock} for 60 s")
            return 0, 0, 2
        if not real.is_file():
            print(f"  [FAIL] REAL INPUT arms: {rel} is absent — the arm IS the demonstration")
            return 0, 2, 0
        if not _git_clean(str(rel)):
            print(f"  [SKIP] REAL INPUT arms: {rel} is dirty in the working tree or index. "
                  "A dirty file may be a leaked plant from an older killed selftest; "
                  "it must not become a baseline. Commit or stash it and re-run.")
            return 0, 0, 2
        original_identity = None
        state = None
        try:
            _, original_identity = _scanner_input(root, rel)
            with tempfile.TemporaryDirectory(prefix="extend_constants_real_inputs_") as tmp:
                copy = Path(tmp).resolve()
                state = _copy_scanner_inputs(root, copy)
                snapshot = copy / rel
                original = snapshot.read_bytes()
                plant_line = len((original + b"\n").splitlines()) + 1
                if check("REAL INPUT copy unmodified baseline is green", copy, 0):
                    try:
                        snapshot.write_bytes(original + SOUNDNESS_PROSE.encode("utf-8"))
                        check("REAL INPUT copy + the // SOUNDNESS: prose is green", copy, 0)
                        snapshot.write_bytes(original + PLANT.encode("utf-8"))
                        check("REAL INPUT copy + a real unaccounted bypass is RED", copy, 1,
                              ("FAIL: unaccounted extend_constants_* bulk-bypass call site(s):",
                               f"{rel}:{plant_line}  extend_constants_unchecked"))
                    finally:
                        snapshot.write_bytes(original)
                    if snapshot.read_bytes() != original:
                        raise ValueError("isolated snapshot restoration differs from original bytes")
                    check("REAL INPUT copy restored baseline is green", copy, 0)
        except (OSError, ValueError, SystemExit) as exc:
            print(f"  [FAIL] REAL INPUT arms: {exc}")
            failed += 1
        finally:
            try:
                if original_identity is not None and _scanner_input(root, rel)[1] != original_identity:
                    raise ValueError(f"live {rel} changed during the arms; leaving all edits untouched")
                if state is not None and _scanner_input_state(root) != state:
                    raise ValueError("live scanner inputs changed during the arms; leaving edits untouched")
            except (OSError, ValueError) as exc:
                print(f"  [FAIL] REAL INPUT preservation: {exc}")
                failed += 1
        return passed, failed, 0
    finally:
        if holding:
            with contextlib.suppress(OSError):
                lock.rmdir()


def selftest() -> int:
    passed = failed = skipped = 0
    _edge_bad = edge_extractor_failures()
    if _edge_bad:
        print(f"  [FAIL] edge extractor: {_edge_bad}")
        failed += 1
    else:
        print(f"  [ok  ] edge extractor: {len(_EDGE_CASES) + len(_INCLUDE_CASES)} module-edge "
              f"spellings, including the cfg_attr form audit r16 M16-1 found invisible")
        passed += 1
    _lattice_bad = cfg_lattice_failures()
    if _lattice_bad:
        print(f"  [FAIL] cfg lattice: classified backwards: {_lattice_bad}")
        failed += 1
    else:
        print(f"  [ok  ] cfg lattice: {len(_CFG_LATTICE_CASES) + len(_CFG_HEAD_CASES)} spellings, "
              f"including the five audit r15 M15-1 found inverted and three tool paths")
        passed += 1
    _lexer_bad = lexer_failures()
    if _lexer_bad:
        print(f"  [FAIL] lexer: read differently from rustc: {_lexer_bad}")
        failed += 1
    else:
        print(f"  [ok  ] lexer: {len(_LEXER_CASES)} readings, nested comments and raw-string "
              f"prefixes among them")
        passed += 1
    _tree_bad = module_tree_failures()
    if _tree_bad:
        for _line in _tree_bad:
            print(f"  [FAIL] module tree: {_line}")
        failed += 1
    else:
        print(f"  [ok  ] module tree: {len(_MODULE_TREE_CASES)} layouts resolved as rustc "
              f"resolves them, including the 79a1983740 cfg(test) chain")
        passed += 1

    def check(name: str, root: Path, expect: int) -> None:
        nonlocal passed, failed
        if _arm(name, root, expect):
            passed += 1
        else:
            failed += 1

    root = _selftest_tree()
    lib = root / "crates" / "c" / "src" / "lib.rs"
    baseline = lib.read_text()
    try:
        # 1. pristine tree: the only hit is inside `#[cfg(test)] mod` -> green
        check("pristine tree with only a cfg(test) bypass is green", root, 0)

        # 1c. The 79a1983740 shape, end to end: a bypass in a module the
        # compiler reaches only through a cfg(test) gate one file up -- through
        # an ordinary `chain.rs` that owns `chain/` -- is test code; the same
        # files with that gate removed are production and RED.
        chain = root / "crates" / "c" / "src" / "chain.rs"
        chain_dir = root / "crates" / "c" / "src" / "chain"
        chain_dir.mkdir()
        chain.write_text("mod deep;\n")
        (chain_dir / "deep.rs").write_text(PLANT)
        for guard, want in (("#[cfg(test)]", 0), ("", 1)):
            lib.write_text(baseline + "\n" + guard + "\nmod chain;\n")
            check(
                f"a bypass in chain/deep.rs under `{guard or '<no guard>'} mod chain;` is "
                f"{'RED' if want else 'green'}",
                root,
                want,
            )
        shutil.rmtree(chain_dir)
        chain.unlink()
        lib.write_text(baseline)

        # 2. a production bypass, unaccounted -> RED
        lib.write_text(baseline + PLANT)
        check("NEW unaccounted production extend_constants_unchecked is RED", root, 1)

        # 3. same site, accounted AND justified at the call -> green
        lib.write_text(baseline + PLANT_JUSTIFIED)
        doc = _read_ratchet(root)
        doc["extend_constants"]["unchecked_production_count"] = 1
        doc["extend_constants"]["production_sites"] = [
            {
                "file": "crates/c/src/lib.rs",
                "method": "extend_constants_unchecked",
                "trust": "selftest",
            }
        ]
        _write_ratchet(root, doc)
        check("an accounted production bypass is green", root, 0)

        # 4. baseline lowered below the measured sites -> RED
        doc["extend_constants"]["unchecked_production_count"] = 0
        _write_ratchet(root, doc)
        check("measured sites exceeding the declared baseline is RED", root, 1)

        # 5. THE ANTI-CORRELATION ARM. The `// SOUNDNESS:` comment the gate's own
        #    remediation text demands, quoting the call, must NOT be a hit. The
        #    raw-line scanner this replaced failed exactly here (measured
        #    2026-08-25 at 438a64131 on the real crates/clean-kernel/src/env/
        #    snapshot.rs). If this arm ever goes red again, the gate is once more
        #    punishing the documentation it asks for.
        doc["extend_constants"]["unchecked_production_count"] = 0
        doc["extend_constants"]["production_sites"] = []
        _write_ratchet(root, doc)
        lib.write_text(baseline + SOUNDNESS_PROSE)
        check("a // SOUNDNESS: comment quoting the call is NOT a bypass", root, 0)

        # 6. a doc comment quoting the call is not a hit either
        lib.write_text(
            baseline
            + "\n/// Callers must not use `env.extend_constants_structural(d)` here.\n"
            + "/** block form: env.extend_constants_unchecked(d) */\n"
        )
        check("doc/block comments quoting the call are NOT bypasses", root, 0)

        # 7. a string literal naming the call is not a hit
        lib.write_text(
            baseline
            + '\npub fn msg() -> &\'static str { "use env.extend_constants_unchecked(d)" }\n'
        )
        check("a string literal naming the call is NOT a bypass", root, 0)

        # 8. ...but a real call on the SAME line as a comment still counts
        lib.write_text(
            baseline
            + "\npub fn s(env: &mut E, d: D) { env.extend_constants_unchecked(d); } // see above\n"
        )
        check("a real call with a trailing comment is still counted", root, 1)

        # 9. EVERY spelling of a call through the bulk door IS a bypass.
        #
        # THIS ARM USED TO ASSERT THE OPPOSITE (audit r11 M11-5): it pinned the
        # dot-only rule green, and this scanner is the SOLE gate over the bulk
        # doors -- the env census hands them off via POINTER_METHODS and there
        # is no Rust mirror. Measured then: `Environment::`, `TrustedEnvExt::`,
        # `<Environment as TrustedEnvExt>::` and `Self::` forms were all
        # byte-identical to baseline, and TrustedEnvExt is `pub use`-exported,
        # so any of the 27 crates could spell one.
        for label, call in (
            ("Environment::", "Environment::extend_constants_unchecked(e, d);"),
            ("TrustedEnvExt::", "TrustedEnvExt::extend_constants_unchecked(e, d);"),
            ("fully qualified", "<Environment as TrustedEnvExt>::extend_constants_unchecked(e, d);"),
            ("Self::", "Self::extend_constants_unchecked(e, d);"),
        ):
            lib.write_text(baseline + f"\npub fn deleg(e: &mut E, d: D) {{ {call} }}\n")
            check(f"a {label} call through the bulk door IS a bypass", root, 1)

        # 10. an unbalanced cfg(test) mod fails CLOSED, never skips
        lib.write_text(
            "#[cfg(test)]\nmod tests {\n    fn t() { env.extend_constants_unchecked(d); }\n"
        )
        check("an unterminated cfg(test) block fails closed", root, 1)

        # 10b-c. Test-ness a file carries (2026-11-16,
        # docs/issues/2026-11-16-python-rust-lexer-copies.md).
        src_dir = root / "crates" / "c" / "src"
        lib.write_text(baseline + "\nmod headed;\n")
        (src_dir / "headed.rs").write_text("// note\n\n#![cfg(test)]\n" + PLANT)
        check("a file headed #![cfg(test)] is test code, whatever declares it", root, 0)
        (src_dir / "headed.rs").write_text("// note\n\n#![cfg(any(test, feature = \"x\"))]\n" + PLANT)
        check("a file headed by any other cfg stays production", root, 1)
        (src_dir / "headed.rs").unlink()

        # 11. a leftover test_excluded_sites row is REFUSED, not honoured
        lib.write_text(baseline + PLANT)
        doc = _read_ratchet(root)
        doc["extend_constants"]["unchecked_production_count"] = 0
        doc["extend_constants"]["production_sites"] = []
        doc["extend_constants"]["test_excluded_sites"] = [
            {"file": "crates/c/src/lib.rs", "method": "extend_constants_unchecked"}
        ]
        _write_ratchet(root, doc)
        check("a test_excluded_sites row can no longer hide a production bypass", root, 1)

        # 12. PER-SITE JUSTIFICATION (lane LOOSE): an ACCOUNTED site whose
        #     `// SOUNDNESS:` comment is deleted is RED. The ratchet entry is
        #     only half the rule; this gate asked for the other half in its
        #     remediation text for two months and never checked it.
        lib.write_text(baseline + PLANT)
        doc = _read_ratchet(root)
        doc["extend_constants"].pop("test_excluded_sites", None)
        doc["extend_constants"]["unchecked_production_count"] = 1
        doc["extend_constants"]["production_sites"] = [
            {
                "file": "crates/c/src/lib.rs",
                "method": "extend_constants_unchecked",
                "trust": "selftest",
            }
        ]
        _write_ratchet(root, doc)
        check("an accounted site with NO // SOUNDNESS: comment is RED", root, 1)

        # 13. THE BLANKET-SUPPRESSION ARM. A row is not a licence for the FILE.
        #     A second justified call under a row that declares no `occurrences`
        #     is RED -- this is the shape that let a real production bypass hide
        #     behind `test_excluded_sites` (retired 2026-08-25), one layer up.
        lib.write_text(baseline + PLANT_JUSTIFIED_TWICE)
        doc["extend_constants"]["unchecked_production_count"] = 2
        _write_ratchet(root, doc)
        check("a SECOND call under a one-site row is RED", root, 1)

        # 14. ...and legal once the row declares it, with a justification that
        #     covers both calls.
        doc["extend_constants"]["production_sites"][0]["occurrences"] = 2
        _write_ratchet(root, doc)
        check("two calls under a row declaring occurrences=2 is green", root, 0)

        # 15. a row may not declare a non-positive or unparsable `occurrences`
        #     and thereby cover nothing while still marking the pair accounted.
        doc["extend_constants"]["production_sites"][0]["occurrences"] = 0
        _write_ratchet(root, doc)
        check("occurrences=0 is REFUSED, not read as 'unlimited'", root, 1)

        # 16. an unreadable ratchet fails closed
        lib.write_text(baseline)
        (root / RATCHET_REL).write_text("{ not json")
        rc = 0
        try:
            _quiet_run(root)
        except SystemExit as exc:
            rc = 1 if exc.code else 0
        good = rc == 1
        print(f"  [{'ok ' if good else 'FAIL'}] an unparsable ratchet fails closed: {good}")
        passed += 1 if good else 0
        failed += 0 if good else 1

        # 17. The standing plant uses the REAL source graph and ledger, copied
        # into isolation. The old live-file arm leaked a plant under concurrent
        # runs (2026-09-14) and invalidated kernel build fingerprints even when
        # restored. Keep its lock/cleanliness policies; never write live inputs.
        lock = Path(tempfile.gettempdir()) / "clean-extend-constants-selftest.lock"
        real_passed, real_failed, real_skipped = _standing_plant_arms(REPO_ROOT, lock)
        passed += real_passed
        failed += real_failed
        skipped += real_skipped
    finally:
        shutil.rmtree(root, ignore_errors=True)

    tail = f", {skipped} SKIPPED (never counted as passed)" if skipped else ""
    print(f"selftest: {passed} passed, {failed} failed{tail}")
    return 0 if failed == 0 else 2


def main(argv: list[str]) -> int:
    if "--pinned-inputs" in argv:
        print(*PINNED_INPUTS, sep="\n")
        return 0
    # The runners call the isolated selftest first, then measure the live tree.
    # Neither invocation writes or restores any tracked scanner input.
    if "--selftest" in argv:
        return selftest()
    return run(REPO_ROOT)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
