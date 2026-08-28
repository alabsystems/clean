#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""The add_decl_structural / add_decl_unchecked bypass ratchet, MEASURED.

WHY THIS EXISTS
---------------
CLAUDE.md makes this a first-class soundness rule:

    `add_decl_structural` / `add_decl_unchecked` require a `// SOUNDNESS:`
    comment and a tracking issue. Tracked in
    `data/unchecked_decl_ratchet.json`; only goes down.

Two gates read that artifact and neither reads the SOURCE TREE:

  * `validate_unchecked_decl_ratchet` (crates/clean-cli/src/cmd_replacement/
    gate_checks.rs) checks the JSON is internally consistent — rows sum to the
    declared counts, trust strings non-empty, no zero counts.
  * `check_unchecked_decl_ratchet_zero` (scripts/deny_sorry_gate.sh) asserted the
    two declared counts were literally `0`, and recorded
    `unchecked_decl_ratchet_zero: passed` into
    reports/deny-sorry-launch-evidence.json. SUPERSEDED 2026-08-23 (G6): the
    literal 0 was false, and that lane is now
    `unchecked_decl_ratchet_accounted`, which imports SANCTIONED_SITES from here
    and calls this scanner instead of reading a number.

So the whole "the unchecked-decl ratchet is at 0/0" claim was a claim about a
JSON literal. Nothing re-derived it from the tree. Adding
`env.add_decl_unchecked(d)` to a production file — no `// SOUNDNESS:` comment,
no ratchet entry — passed every gate in the repo (demonstrated 2026-08-22 by
planting exactly that in crates/clean-kernel/src/env/snapshot.rs: seven
python gates plus paragon were byte-identical with and without it).

This is the missing scanner. It is the same shape as
scripts/check_extend_constants_ratchet.py, which does for the *bulk*
`extend_constants_*` bypass exactly what nobody had done for `add_decl_*`.

WHAT IT MEASURES
----------------
Dot-call form only: `<recv>.add_decl_unchecked(` / `<recv>.add_decl_structural(`.
This deliberately does NOT match the method definitions (`fn add_decl_*` in
env/decl_add.rs), the trait declarations or the `Environment::add_decl_*(self, …)`
delegations in env/trusted_ext.rs (a `::` call), doc comments, or string
literals — the same exclusions the extend_constants gate documents.

Test code is excluded two ways, because both classes exist here:
  * test FILES, by the byte-identical predicate the extend_constants gate uses;
  * inline `#[cfg(test)] mod` blocks inside otherwise-production files, by brace
    tracking. 48 of the tree's 49 non-test-path hits are of this second kind, so
    a gate without it would be 48 false positives and would be switched off.
    The tracker fails CLOSED: a file whose braces do not balance is an error,
    never a skip.

VERDICTS
--------
A measured production site must be ACCOUNTED FOR, one of two ways:
  * `add_decl_{structural,unchecked}_production_sites` — the normal route; the
    site counts toward the ratchet total and `deny_sorry_gate.sh` sees it.
  * `add_decl_measured_disagreements` — a site the tree HAS and the counts do
    NOT, recorded with its reason and the reconciliation owed. The disagreement
    is printed on every run instead of being silently excluded. A disagreement
    row that no longer matches a live site is STALE and fails — the debt cannot
    be abandoned quietly either.

…and, either way, the site must be named in `SANCTIONED_SITES` BELOW — the
allowlist that lives in CODE, not in the artifact. That is the half of "only
goes down" a JSON count can never enforce: before it, a new bypass could be
legalised by writing a row about it. Now legalising one requires editing this
file, and the per-site cap means even a sanctioned site cannot quietly gain a
second occurrence.

Every accounted site must still carry a `// SOUNDNESS:` comment within
`SOUNDNESS_WINDOW` lines above the call. That is the half of the CLAUDE.md rule
no gate has ever enforced.

Exit codes: 0 accounted, 1 unaccounted/unsanctioned/stale/over-baseline, 2 self-test
failure.

Usage:
    python3 scripts/check_add_decl_ratchet.py
    python3 scripts/check_add_decl_ratchet.py --list
    python3 scripts/check_add_decl_ratchet.py --selftest
"""

from __future__ import annotations

import contextlib
import io
import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
RATCHET_REL = Path("data") / "unchecked_decl_ratchet.json"
CRATES_REL = Path("crates")

CALL_RE = re.compile(r"\.add_decl_(unchecked|structural)\s*\(")
CFG_TEST_RE = re.compile(r"#\[\s*cfg\s*\(\s*test\s*\)\s*\]")
MOD_RE = re.compile(r"\bmod\b")
SOUNDNESS_RE = re.compile(r"//.*\bSOUNDNESS\b")
SOUNDNESS_WINDOW = 40

# The sanctioned production bypasses, PINNED IN CODE: (file, method) -> the
# maximum number of production call sites that site may contain.
#
# A ratchet row — a `*_production_sites` entry OR an
# `add_decl_measured_disagreements` entry — is honoured ONLY for a key named
# here. Both routes suppress a RED, so both must cost a reviewed source change;
# otherwise "the artifact says it is fine" remains a self-issued licence, which
# is the exact failure this gate was written for.
#
# G6 (2026-08-23): the one entry is the Metamath two-pass PASS-1 proof-drop arm
# of `Environment::add_decl`. It registers a `Declaration::Axiom` without
# `infer_sort`/`check_type`, and it is sound only because (1) it fails closed
# outside the `MmAxiomOnlyGuard` two-pass sentinel, (2) PASS-2 re-adds every
# in-range theorem through the CHECKED `add_decl`, and (3) `mm_gate` drops any
# verified theorem whose transitive `$p` closure is not itself verified, so only
# that gated set is ever exported. The full argument, with the file references,
# is the `trust` prose on the site's row in data/unchecked_decl_ratchet.json.
SANCTIONED_SITES: dict[tuple[str, str], int] = {
    ("crates/clean-kernel/src/env/decl_add.rs", "add_decl_unchecked"): 1,
}


def is_test_path(rel: Path) -> bool:
    """True for test FILES. Byte-identical to check_extend_constants_ratchet.py
    so the two bypass gates cannot drift into disagreeing about what a test is."""
    parts = set(rel.parts)
    if "tests" in parts or "tests2" in parts:
        return True
    name = rel.name
    return bool(re.search(r"(^test_|_tests?\.rs$|^tests?\.rs$|^tests_)", name)) or "test" in name


# Rust non-code spans, in the order a lexer would see them. Ordered
# alternation matters: a `//` inside a string literal must not win, so the
# string alternatives come after the comment ones only where they cannot
# overlap — block and line comments first, then raw strings (whose `#`-fence
# backreference makes them unambiguous), then plain strings, then chars.
NONCODE_RE = re.compile(
    r"/\*.*?\*/"                    # block comment (non-nested)
    r"|//[^\n]*"                    # line comment
    r'|(?:b?r)(#*)"(?:.|\n)*?"\1'   # raw string   r"..."  r#"..."#
    r'|b?"(?:\\.|[^"\\])*"'         # string literal
    r"|'(?:\\.|[^\\'])'",           # char literal
    re.DOTALL,
)


def _blank(match: re.Match[str]) -> str:
    """Replace a non-code span with spaces, preserving newlines.

    Line numbers and column positions therefore survive stripping exactly, so a
    hit's reported line still indexes the ORIGINAL file.
    """
    return "".join("\n" if ch == "\n" else " " for ch in match.group(0))


def strip_noncode(text: str) -> str:
    """Blank out comments and string/raw-string/char literals.

    Brace counting over the raw text is wrong: `'{'`, `"}"` and a `{` inside a
    doc comment all unbalance it. Measured 2026-08-22 over the 6,815 .rs files
    under crates/: raw counting leaves 22 files apparently unbalanced (and a
    gate that fails closed on 22 healthy files is a gate that gets deleted);
    after stripping, ZERO are unbalanced. 4.8 s for the whole tree.
    """
    return NONCODE_RE.sub(_blank, text)


def scan_file(path: Path, rel: Path) -> tuple[list[dict], list[dict]]:
    """(production hits, cfg(test) hits) for one file. Raises on unbalanced braces."""
    raw_text = path.read_text(errors="strict")
    raw_lines = raw_text.splitlines()
    lines = strip_noncode(raw_text).splitlines()
    prod: list[dict] = []
    tested: list[dict] = []
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
                    # the attribute annotated something that is not a `mod` (a
                    # fn, a use, a const): not a block, so nothing to track.
                    pending_cfg = False
        else:
            depth += line.count("{") - line.count("}")
            if depth <= 0:
                in_cfg_test = False
        m = CALL_RE.search(line)
        if not m:
            continue
        hit = {
            "file": str(rel),
            "line": lineno,
            "method": f"add_decl_{m.group(1)}",
            "text": raw_lines[lineno - 1].strip()[:100],
        }
        (tested if in_cfg_test else prod).append(hit)
    if in_cfg_test:
        raise ValueError(
            f"{rel}: a #[cfg(test)] mod block never closed (brace tracking ran off the "
            f"end of the file). Refusing to classify this file — fix the source or the "
            f"tracker; an unreadable file is not a clean one."
        )
    return prod, tested


def has_soundness_comment(path: Path, lineno: int) -> bool:
    lines = path.read_text(errors="strict").splitlines()
    start = max(0, lineno - 1 - SOUNDNESS_WINDOW)
    return any(SOUNDNESS_RE.search(l) for l in lines[start:lineno])


def measure(root: Path) -> tuple[list[dict], list[dict], list[str]]:
    prod: list[dict] = []
    tested: list[dict] = []
    errors: list[str] = []
    for path in sorted((root / CRATES_REL).rglob("*.rs")):
        rel = path.relative_to(root)
        if is_test_path(rel):
            continue
        try:
            p, t = scan_file(path, rel)
        except (OSError, UnicodeDecodeError) as exc:
            errors.append(f"cannot read {rel}: {exc}")
            continue
        except ValueError as exc:
            errors.append(str(exc))
            continue
        prod.extend(p)
        tested.extend(t)
    return prod, tested, errors


def load_ratchet(root: Path) -> dict:
    path = root / RATCHET_REL
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:  # fail closed
        raise SystemExit(f"FAIL: cannot read {RATCHET_REL}: {exc}")


def run(
    root: Path,
    list_only: bool = False,
    sanctioned: dict[tuple[str, str], int] | None = None,
) -> int:
    sanctioned = SANCTIONED_SITES if sanctioned is None else sanctioned
    ratchet = load_ratchet(root)
    prod, tested, errors = measure(root)

    accounted: dict[tuple[str, str], str] = {}
    for key, method in (
        ("add_decl_structural_production_sites", "add_decl_structural"),
        ("add_decl_unchecked_production_sites", "add_decl_unchecked"),
    ):
        for site in ratchet.get(key, []) or []:
            if isinstance(site, dict) and "file" in site:
                accounted[(site["file"], site.get("method", method))] = "counted"
    disagreements = ratchet.get("add_decl_measured_disagreements", []) or []
    for row in disagreements:
        if isinstance(row, dict) and "file" in row and "method" in row:
            accounted[(row["file"], row["method"])] = "disagreement"

    if list_only:
        print(f"production sites ({len(prod)}):")
        for h in prod:
            print(f"  {h['file']}:{h['line']}  {h['method']}  | {h['text']}")
        print(f"inline cfg(test) sites: {len(tested)}")
        return 0

    ok = True
    if errors:
        ok = False
        print("FAIL: the add_decl scanner could not classify part of the tree:", file=sys.stderr)
        for e in errors:
            print(f"  {e}", file=sys.stderr)

    unaccounted = [h for h in prod if (h["file"], h["method"]) not in accounted]
    if unaccounted:
        ok = False
        print("FAIL: unaccounted add_decl_* bypass call site(s) in production code:", file=sys.stderr)
        for h in unaccounted:
            print(f"  {h['file']}:{h['line']}  {h['method']}  | {h['text']}", file=sys.stderr)
        print(
            "  -> a declaration registered without type checking. Add a // SOUNDNESS: "
            "comment at the call AND an entry under data/unchecked_decl_ratchet.json "
            "(add_decl_*_production_sites, which raises the ratchet count and is seen by "
            "scripts/deny_sorry_gate.sh).",
            file=sys.stderr,
        )

    # Every accounted site must actually carry its SOUNDNESS comment — the half
    # of the CLAUDE.md rule no gate has enforced.
    for h in prod:
        if (h["file"], h["method"]) not in accounted:
            continue
        if not has_soundness_comment(root / h["file"], h["line"]):
            ok = False
            print(
                f"FAIL: {h['file']}:{h['line']} {h['method']} is accounted for in the ratchet "
                f"but carries no // SOUNDNESS: comment within {SOUNDNESS_WINDOW} lines above "
                f"the call.",
                file=sys.stderr,
            )

    # A ratchet row may only speak for a site the CODE allowlist sanctions. An
    # artifact that could legalise its own bypass is not a ratchet.
    for (f, m), kind in sorted(accounted.items()):
        if (f, m) not in sanctioned:
            ok = False
            print(
                f"FAIL: data/unchecked_decl_ratchet.json records a {kind} row for {f} / {m}, "
                f"which is NOT in SANCTIONED_SITES in {Path(__file__).name}. A ratchet row cannot "
                f"authorize a bypass by itself — add the site to the code allowlist, with its "
                f"soundness argument, or remove the bypass.",
                file=sys.stderr,
            )

    # A sanctioned site may not quietly grow extra call sites either.
    per_site: dict[tuple[str, str], int] = {}
    for h in prod:
        key = (h["file"], h["method"])
        per_site[key] = per_site.get(key, 0) + 1
    for key, seen in sorted(per_site.items()):
        cap = sanctioned.get(key)
        if cap is not None and seen > cap:
            ok = False
            print(
                f"FAIL: {key[0]} / {key[1]} has {seen} production call sites but "
                f"SANCTIONED_SITES caps it at {cap}. A sanctioned bypass does not license "
                f"further copies of itself.",
                file=sys.stderr,
            )

    # A ratchet row that no longer matches a live site is STALE. Debt may be
    # paid off, but it is not allowed to evaporate unremarked.
    live = {(h["file"], h["method"]) for h in prod}
    for (f, m), kind in sorted(accounted.items()):
        if (f, m) not in live:
            ok = False
            print(
                f"FAIL: data/unchecked_decl_ratchet.json records a {kind} row for "
                f"{f} / {m} and no such production call site exists in the tree. "
                f"If the bypass was removed, remove the row (the ratchet only goes down).",
                file=sys.stderr,
            )

    counts = {"add_decl_structural": 0, "add_decl_unchecked": 0}
    for h in prod:
        if accounted.get((h["file"], h["method"])) == "counted":
            counts[h["method"]] += 1
    for method, declared_key in (
        ("add_decl_structural", "add_decl_structural_count"),
        ("add_decl_unchecked", "add_decl_unchecked_count"),
    ):
        declared = ratchet.get(declared_key)
        if not isinstance(declared, int):
            ok = False
            print(f"FAIL: {RATCHET_REL} has no integer {declared_key}", file=sys.stderr)
            continue
        if counts[method] > declared:
            ok = False
            print(
                f"FAIL: measured {method} production sites {counts[method]} exceeds the "
                f"declared {declared_key}={declared}. A new bypass must be justified and "
                f"ratcheted, never absorbed.",
                file=sys.stderr,
            )

    if disagreements:
        print("ADD_DECL_RATCHET=disagreement — the tree and the counts do not agree:")
        for row in disagreements:
            print(f"  {row.get('file')} / {row.get('method')}: {row.get('reason', '(no reason given)')}")
            if row.get("reconciliation"):
                print(f"    owed: {row['reconciliation']}")

    if ok:
        print(
            f"OK: add_decl bypass ratchet — production sites: "
            f"structural={counts['add_decl_structural']}/"
            f"{ratchet.get('add_decl_structural_count')}, "
            f"unchecked={counts['add_decl_unchecked']}/"
            f"{ratchet.get('add_decl_unchecked_count')}, "
            f"disagreements={len(disagreements)}; "
            f"{len(tested)} inline cfg(test) sites excluded."
        )
        return 0
    return 1


# ---------------------------------------------------------------------------
# self-test: a gate that has never been shown to fail is not a gate
# ---------------------------------------------------------------------------

SELFTEST_CASES: list[tuple[str, str]] = []


def _selftest_tree() -> Path:
    """A minimal fake repo the mutation arms can edit freely."""
    tmp = Path(tempfile.mkdtemp(prefix="add_decl_selftest_"))
    (tmp / "data").mkdir()
    (tmp / "crates" / "c" / "src").mkdir(parents=True)
    (tmp / "data" / RATCHET_REL.name).write_text(
        json.dumps(
            {
                "add_decl_structural_count": 0,
                "add_decl_unchecked_count": 0,
                "add_decl_structural_production_sites": [],
                "add_decl_unchecked_production_sites": [],
                "files": [],
                "last_updated": "selftest",
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
        "        env.add_decl_unchecked(d);\n"
        "    }\n"
        "}\n"
    )
    return tmp


def _write_ratchet(root: Path, doc: dict) -> None:
    (root / RATCHET_REL).write_text(json.dumps(doc, indent=2))


def _read_ratchet(root: Path) -> dict:
    return json.loads((root / RATCHET_REL).read_text())


def _quiet_run(root: Path, sanctioned: dict[tuple[str, str], int] | None) -> tuple[int, str]:
    """Run the gate capturing its output: a mutation arm is SUPPOSED to print
    failures, and a passing self-test that fills the log with `FAIL:` lines is a
    log nobody can read. The capture is replayed only when an arm misbehaves."""
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
        rc = run(root, sanctioned=sanctioned)
    return rc, buf.getvalue()


def _arm(
    name: str,
    root: Path,
    expect: int,
    sanctioned: dict[tuple[str, str], int] | None = None,
) -> bool:
    rc, captured = _quiet_run(root, sanctioned)
    good = rc == expect
    print(f"  [{'ok ' if good else 'FAIL'}] {name}: exit {rc} (expected {expect})")
    if not good and captured:
        print("    --- the arm's own output ---")
        for line in captured.rstrip("\n").splitlines():
            print(f"    {line}")
    return good


# The fake tree's own allowlist. Arms 1-12 exercise the accounting logic on a
# synthetic path, so they carry a synthetic sanction; arms 13-16 use the REAL
# SANCTIONED_SITES and are the ones that pin the shipped allowlist.
FAKE_SANCTIONED: dict[tuple[str, str], int] = {
    ("crates/c/src/lib.rs", "add_decl_unchecked"): 1,
    ("crates/c/src/lib.rs", "add_decl_structural"): 1,
}

PLANT = "\npub fn smuggle(env: &mut E, d: D) { env.add_decl_unchecked(d); }\n"


def selftest() -> int:
    passed = failed = 0

    def check(
        name: str,
        root: Path,
        expect: int,
        sanctioned: dict[tuple[str, str], int] | None = FAKE_SANCTIONED,
    ) -> None:
        nonlocal passed, failed
        if _arm(name, root, expect, sanctioned):
            passed += 1
        else:
            failed += 1

    root = _selftest_tree()
    lib = root / "crates" / "c" / "src" / "lib.rs"
    baseline = lib.read_text()
    try:
        # 1. pristine tree: only a cfg(test) hit -> green
        check("pristine tree with only a cfg(test) bypass is green", root, 0)

        # 2. a production bypass, unaccounted -> RED
        lib.write_text(baseline + "\npub fn smuggle(env: &mut E, d: D) { env.add_decl_unchecked(d); }\n")
        check("NEW unaccounted production add_decl_unchecked is RED", root, 1)

        # 3. same, but accounted AND with a SOUNDNESS comment -> green
        doc = _read_ratchet(root)
        doc["add_decl_unchecked_count"] = 1
        doc["add_decl_unchecked_production_sites"] = [
            {"file": "crates/c/src/lib.rs", "method": "add_decl_unchecked", "trust": "selftest"}
        ]
        _write_ratchet(root, doc)
        lib.write_text(
            baseline
            + "\n// SOUNDNESS: selftest justification.\npub fn smuggle(env: &mut E, d: D) { env.add_decl_unchecked(d); }\n"
        )
        check("accounted + SOUNDNESS-commented production bypass is green", root, 0)

        # 4. accounted but the SOUNDNESS comment removed -> RED
        lib.write_text(baseline + "\npub fn smuggle(env: &mut E, d: D) { env.add_decl_unchecked(d); }\n")
        check("accounted site whose SOUNDNESS comment was deleted is RED", root, 1)

        # 5. count lowered below the measured sites -> RED
        lib.write_text(
            baseline
            + "\n// SOUNDNESS: selftest justification.\npub fn smuggle(env: &mut E, d: D) { env.add_decl_unchecked(d); }\n"
        )
        doc = _read_ratchet(root)
        doc["add_decl_unchecked_count"] = 0
        _write_ratchet(root, doc)
        check("measured sites exceeding the declared count is RED", root, 1)

        # 6. the bypass removed but the row left behind -> RED (stale)
        lib.write_text(baseline)
        doc["add_decl_unchecked_count"] = 1
        _write_ratchet(root, doc)
        check("a ratchet row with no live call site is RED (stale debt)", root, 1)

        # 7. a disagreement row accounts for a site the counts do not -> green
        lib.write_text(
            baseline
            + "\n// SOUNDNESS: selftest justification.\npub fn smuggle(env: &mut E, d: D) { env.add_decl_unchecked(d); }\n"
        )
        doc = _read_ratchet(root)
        doc["add_decl_unchecked_count"] = 0
        doc["add_decl_unchecked_production_sites"] = []
        doc["add_decl_measured_disagreements"] = [
            {
                "file": "crates/c/src/lib.rs",
                "method": "add_decl_unchecked",
                "reason": "selftest disagreement",
                "reconciliation": "selftest",
            }
        ]
        _write_ratchet(root, doc)
        check("a recorded disagreement accounts for the site (and prints)", root, 0)

        # 8. a SECOND production bypass is still RED even with a disagreement row
        lib.write_text(
            lib.read_text()
            + "\n// SOUNDNESS: second.\npub fn smuggle2(env: &mut E, d: D) { env.add_decl_structural(d); }\n"
        )
        check("a second, different-method bypass is still RED", root, 1)

        # 9. `Environment::add_decl_unchecked(self, d)` (the :: delegation) is NOT a hit
        lib.write_text(baseline + "\npub fn deleg(e: &mut E, d: D) { Environment::add_decl_unchecked(e, d); }\n")
        doc = _read_ratchet(root)
        doc["add_decl_measured_disagreements"] = []
        _write_ratchet(root, doc)
        check(":: delegation form is not counted as a bypass", root, 0)

        # 10. a call quoted in a `//` comment is NOT a hit
        lib.write_text(baseline + "\n// see env.add_decl_unchecked(d) for the bypass\n")
        check("a call quoted in a comment is not counted", root, 0)

        # 11. an unbalanced cfg(test) mod fails CLOSED, never skips
        lib.write_text("#[cfg(test)]\nmod tests {\n    fn t() { env.add_decl_unchecked(d); }\n")
        check("an unterminated cfg(test) block fails closed", root, 1)

        # 12. an unreadable ratchet fails closed
        lib.write_text(baseline)
        (root / RATCHET_REL).write_text("{ not json")
        rc = 0
        try:
            _quiet_run(root, FAKE_SANCTIONED)
        except SystemExit as exc:
            rc = 1 if exc.code else 0
        good = rc == 1
        print(f"  [{'ok ' if good else 'FAIL'}] an unparsable ratchet fails closed: {good}")
        passed += 1 if good else 0
        failed += 0 if good else 1

        # -------------------------------------------------------------------
        # 13-16 run against the REAL SANCTIONED_SITES.
        #
        # 13/14 are THE PERMANENT PLANT. The 2026-08-22 falsification that
        # justified writing this gate was an `env.add_decl_unchecked(d)` added
        # to production code in crates/clean-kernel/src/env/snapshot.rs, with no
        # SOUNDNESS comment and no ratchet entry: six python gates plus paragon
        # were byte-identical with and without it. It is kept here as a standing
        # arm, on the REAL file at its REAL repo-relative path, so the
        # demonstration cannot decay into an anecdote in a commit message. The
        # unplanted copy must be GREEN — that is not free: snapshot.rs already
        # contains two `add_decl_unchecked` calls inside a `#[cfg(test)] mod`,
        # so arm 13 also pins the brace tracking on a real file — and the
        # planted copy must be RED.
        real = REPO_ROOT / "crates" / "clean-kernel" / "src" / "env" / "snapshot.rs"
        plant_root = Path(tempfile.mkdtemp(prefix="add_decl_selftest_plant_"))
        try:
            (plant_root / "data").mkdir()
            snap_rel = Path("crates/clean-kernel/src/env/snapshot.rs")
            (plant_root / snap_rel).parent.mkdir(parents=True)
            _write_ratchet(
                plant_root,
                {
                    "add_decl_structural_count": 0,
                    "add_decl_unchecked_count": 0,
                    "add_decl_structural_production_sites": [],
                    "add_decl_unchecked_production_sites": [],
                    "files": [],
                    "last_updated": "selftest",
                },
            )
            if not real.is_file():
                print(
                    "  [FAIL] the permanent plant arm cannot find "
                    f"{snap_rel} — the arm is the demonstration, not an optional extra"
                )
                failed += 1
            else:
                clean_src = real.read_text(encoding="utf-8")
                (plant_root / snap_rel).write_text(clean_src)
                check(
                    "REAL snapshot.rs, unplanted, is green (its cfg(test) bypasses excluded)",
                    plant_root,
                    0,
                    None,
                )

                (plant_root / snap_rel).write_text(clean_src + PLANT)
                check(
                    "REAL snapshot.rs + the 2026-08-22 planted bypass is RED",
                    plant_root,
                    1,
                    None,
                )

                # 15. …and a ratchet row written ABOUT the plant does not
                # legalise it: snapshot.rs is not in SANCTIONED_SITES.
                (plant_root / snap_rel).write_text(
                    clean_src + "\n// SOUNDNESS: fabricated justification.\n" + PLANT
                )
                _write_ratchet(
                    plant_root,
                    {
                        "add_decl_structural_count": 0,
                        "add_decl_unchecked_count": 1,
                        "add_decl_structural_production_sites": [],
                        "add_decl_unchecked_production_sites": [
                            {
                                "file": str(snap_rel),
                                "method": "add_decl_unchecked",
                                "trust": "fabricated",
                            }
                        ],
                        "files": [],
                        "last_updated": "selftest",
                    },
                )
                check(
                    "a ratchet row + SOUNDNESS comment CANNOT self-authorize an "
                    "unsanctioned bypass",
                    plant_root,
                    1,
                    None,
                )

            # 16. the sanctioned site does not license a SECOND copy of itself.
            sanct_rel = Path("crates/clean-kernel/src/env/decl_add.rs")
            (plant_root / snap_rel).unlink(missing_ok=True)
            (plant_root / sanct_rel).write_text(
                "// SOUNDNESS: the sanctioned one.\n"
                "pub fn a(env: &mut E, d: D) { env.add_decl_unchecked(d); }\n"
                "// SOUNDNESS: a second, unsanctioned copy.\n"
                "pub fn b(env: &mut E, d: D) { env.add_decl_unchecked(d); }\n"
            )
            _write_ratchet(
                plant_root,
                {
                    "add_decl_structural_count": 0,
                    "add_decl_unchecked_count": 2,
                    "add_decl_structural_production_sites": [],
                    "add_decl_unchecked_production_sites": [
                        {
                            "file": str(sanct_rel),
                            "method": "add_decl_unchecked",
                            "occurrences": 2,
                            "trust": "the real row, widened",
                        }
                    ],
                    "files": [],
                    "last_updated": "selftest",
                },
            )
            check(
                "a SECOND call site in the sanctioned file exceeds its cap and is RED",
                plant_root,
                1,
                None,
            )
        finally:
            shutil.rmtree(plant_root, ignore_errors=True)
    finally:
        shutil.rmtree(root, ignore_errors=True)

    print(f"selftest: {passed} passed, {failed} failed")
    return 0 if failed == 0 else 2


def main(argv: list[str]) -> int:
    if "--selftest" in argv:
        return selftest()
    return run(REPO_ROOT, list_only="--list" in argv)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
