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

`--selftest` has 18 arms: 13 from the lexing rewrite (arms 5-8 the
anti-correlation arms, 16-17 the standing plant on the real
crates/clean-kernel/src/env/snapshot.rs) and 5 from the per-site rules above.

Usage:
    python3 scripts/check_extend_constants_ratchet.py
    python3 scripts/check_extend_constants_ratchet.py --selftest
"""
from __future__ import annotations

import contextlib
import io
import json
import re
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
RATCHET_REL = Path("data") / "unchecked_decl_ratchet.json"
CRATES_REL = Path("crates")

# Dot-call form only: `<recv>.extend_constants_unchecked(` / `..._structural(`.
# This deliberately does NOT match the method definitions (`fn extend_constants_*`
# in env/registration.rs) or the trait delegation (`Environment::extend_constants_*`
# in env/trusted_ext.rs, a `::` call). Doc comments and string literals are not
# excluded by the REGEX — they are erased by strip_noncode() before it runs.
CALL_RE = re.compile(r"\.extend_constants_(unchecked|structural)\s*\(")
QUICK_RE = re.compile(r"extend_constants_(unchecked|structural)")
CFG_TEST_RE = re.compile(r"#\[\s*cfg\s*\(\s*test\s*\)\s*\]")
MOD_RE = re.compile(r"\bmod\b")

# PER-SITE JUSTIFICATION (2026-08-25, lane LOOSE). Read on the RAW text, not
# the blanked text: this is the one place the gate WANTS the prose.
SOUNDNESS_RE = re.compile(r"//.*\bSOUNDNESS\b")
SOUNDNESS_WINDOW = 40

# Rust non-code spans — same construction and rationale as
# check_add_decl_ratchet.py and check_env_bypass_census.py (ordered alternation;
# each match is replaced by blanks so line/column geometry is preserved).
NONCODE_RE = re.compile(
    r"/\*.*?\*/"                    # block comment (non-nested)
    r"|//[^\n]*"                    # line comment
    r'|(?:b?r)(#*)"(?:.|\n)*?"\1'   # raw string   r"..."  r#"..."#
    r'|b?"(?:\\.|[^"\\])*"'         # string literal
    r"|'(?:\\.|[^\\'])'",           # char literal
    re.DOTALL,
)


def _blank(match: re.Match[str]) -> str:
    return "".join("\n" if ch == "\n" else " " for ch in match.group(0))


def strip_noncode(text: str) -> str:
    return NONCODE_RE.sub(_blank, text)


def is_test_path(rel: Path) -> bool:
    """True for test FILES (whole-file test targets). Inline #[cfg(test)] blocks
    inside otherwise-production files are handled by scan_file's brace tracker;
    entries still listed in test_excluded_sites are honoured for compatibility."""
    parts = set(rel.parts)
    if "tests" in parts or "tests2" in parts:
        return True
    name = rel.name
    # `tests.rs`, `*_tests.rs`, `test_*.rs`, `tests_*.rs`
    return bool(re.search(r"(^test_|_tests?\.rs$|^tests?\.rs$|^tests_)", name)) or "test" in name


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


def has_soundness_comment(raw_lines: list[str], lineno: int) -> bool:
    """True if a `// SOUNDNESS:` comment sits within SOUNDNESS_WINDOW lines above
    (or on) the call at 1-indexed `lineno`. Same rule and window as the sibling
    scripts/check_add_decl_ratchet.py."""
    start = max(0, lineno - 1 - SOUNDNESS_WINDOW)
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
        if is_test_path(rel):
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
        for hit in hits:
            key = (hit["file"], hit["method"])
            if key in prod:
                counts[hit["method"].removeprefix("extend_constants_")] += 1
                seen[key] = seen.get(key, 0) + 1
                if not has_soundness_comment(raw_lines, hit["line"]):
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


def _arm(name: str, root: Path, expect: int) -> bool:
    rc, captured = _quiet_run(root)
    good = rc == expect
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


def selftest() -> int:
    passed = failed = 0

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

        # 9. the `::` delegation form is not a dot-call bypass
        lib.write_text(
            baseline
            + "\npub fn deleg(e: &mut E, d: D) { Environment::extend_constants_unchecked(e, d); }\n"
        )
        check(":: delegation form is not counted as a bypass", root, 0)

        # 10. an unbalanced cfg(test) mod fails CLOSED, never skips
        lib.write_text(
            "#[cfg(test)]\nmod tests {\n    fn t() { env.extend_constants_unchecked(d); }\n"
        )
        check("an unterminated cfg(test) block fails closed", root, 1)

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

        # 17. THE STANDING PLANT, on the REAL tree: the same `// SOUNDNESS:`
        #     prose in the real crates/clean-kernel/src/env/snapshot.rs must
        #     leave the REAL gate green, and a real production call there must
        #     turn it RED. This is the falsification that justified the rewrite,
        #     kept as an arm so it cannot decay into a commit-message anecdote.
        real = REPO_ROOT / "crates" / "clean-kernel" / "src" / "env" / "snapshot.rs"
        if real.is_file():
            original = real.read_text()
            try:
                real.write_text(original + SOUNDNESS_PROSE)
                good = _arm(
                    "REAL TREE + the // SOUNDNESS: prose is green (the anti-correlation)",
                    REPO_ROOT,
                    0,
                )
                passed += 1 if good else 0
                failed += 0 if good else 1
                real.write_text(original + PLANT)
                good = _arm("REAL TREE + a real unaccounted bypass is RED", REPO_ROOT, 1)
                passed += 1 if good else 0
                failed += 0 if good else 1
            finally:
                real.write_text(original)
    finally:
        import shutil

        shutil.rmtree(root, ignore_errors=True)

    print(f"selftest: {passed} passed, {failed} failed")
    return 0 if failed == 0 else 2


def main(argv: list[str]) -> int:
    # `--selftest` is a SEPARATE invocation, exactly as for the sibling
    # `scripts/check_add_decl_ratchet.py`: arms 16-17 write to the REAL
    # crates/clean-kernel/src/env/snapshot.rs, and a measurement run must never
    # touch a tracked file. The runners call it first and then measure.
    if "--selftest" in argv:
        return selftest()
    return run(REPO_ROOT)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
