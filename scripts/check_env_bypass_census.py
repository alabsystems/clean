#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
"""The widened environment-bypass census scanner (program G-SCAN, 2026-08-23).

WHY THIS EXISTS
---------------
Two scanners watch four methods:

  * scripts/check_add_decl_ratchet.py       — add_decl_unchecked / add_decl_structural
  * scripts/check_extend_constants_ratchet.py — extend_constants_unchecked / _structural

The recon census (docs/analysis/spine-lattice-recon-2026-08-22.md §3, 18 items)
measured that those four are a fraction of the surface through which a
declaration, an inductive family, a recursor, an axiom, or a whole deserialized
Environment becomes visible to the kernel without full checking. The
`TrustedEnvExt` trait (crates/clean-kernel/src/env/trusted_ext.rs) is the
deliberate cross-crate choke point enumerating most of that surface — and until
this scanner, items 5-13 and 16-18 of the census had partial or ZERO scanner
coverage: `env.extend_inductives_unchecked(..)` could be added to any
production file and every gate in the repo stayed green.

WHAT IT MEASURES
----------------
Production call sites (crates/**/*.rs, test files and inline #[cfg(test)] mods
excluded) of every watched method, in BOTH call forms:

  * dot-call:            `<recv>.upgrade_axiom_stubs(`
  * qualified:           `Environment::register_inductive(` /
                         `TrustedEnvExt::register_inductive(`

plus the three env deserialization entry points, which are associated
functions (no receiver) and are matched in `Environment::<name>(` form only:
`from_json`, `load_from_file`, `load_snapshot`.

`crates/clean-kernel/src/env/trusted_ext.rs` is excluded wholesale: its impl
bodies are the definitions/delegations (`Environment::method(self, …)`), not
usage. Known match-form limits, inherited deliberately from the two sibling
scanners: an aliased qualified call (`use Environment as E; E::from_json(..)`)
or a function-pointer capture is not matched; dot-call matching is
receiver-blind, so a same-named method on another type over-matches (fails
CLOSED, and the census names the file, so a false positive is visible and
cheap to account).

The watched-method list lives IN THIS FILE (code, not artifact), and the
scanner additionally re-parses the `TrustedEnvExt` trait on every run: a new
trait method that is neither watched here nor covered by a sibling scanner is
a RED, so the choke point cannot quietly widen.

THE CENSUS ARTIFACT
-------------------
data/env_bypass_census.json — one row per watched method/site-class, seeded
from the recon's numbered census with classification (E/P/S), guard notes, and
the R1-* disposition job from designs/2026-08-22-spine-and-lattice-program.md
§5. The add_decl_* / extend_constants_* rows already ledgered in
data/unchecked_decl_ratchet.json are CROSS-REFERENCED (a pointer row naming
the ledger and its scanner), never copied — one accounting point per site.

VERDICTS (all fail-closed)
--------------------------
  * a production call whose (method, file) no census row accounts for → RED
  * a census row naming a site (or prefix) with no live call left     → RED (stale)
  * a row's measured occurrences above its max_occurrences baseline   → RED
  * a TrustedEnvExt trait method neither watched nor cross-referenced → RED
  * census incomplete (a watched method in no row), or a row naming an
    unwatched/duplicated method                                       → RED
  * a cross-reference pointing at a scanner or ledger that is gone    → RED
  * an unreadable census, or an unbalanced #[cfg(test)] mod           → fail closed

// SOUNDNESS comment enforcement is deliberately NOT part of this gate yet:
the newly-watched sites predate the census, and requiring the comment today
would redden ~60 sites at once. Adding the comments (or removing the doors) is
exactly the R1-* ring work each row's disposition_job names.

Exit codes: 0 accounted, 1 unaccounted/stale/over-baseline/drift, 2 self-test
failure.

Usage:
    python3 scripts/check_env_bypass_census.py
    python3 scripts/check_env_bypass_census.py --list
    python3 scripts/check_env_bypass_census.py --selftest
"""

from __future__ import annotations

import contextlib
import io
import json
import re
import shutil
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
CENSUS_REL = Path("data") / "env_bypass_census.json"
CRATES_REL = Path("crates")
TRUSTED_EXT_REL = Path("crates/clean-kernel/src/env/trusted_ext.rs")

# ---------------------------------------------------------------------------
# The watched surface, PINNED IN CODE. A census row may only speak for a
# method named here; widening the census artifact alone cannot widen the watch.
# ---------------------------------------------------------------------------

# TrustedEnvExt methods NOT already watched by a sibling scanner, plus the
# bypass-capable Environment methods the recon found outside the trait.
DOT_WATCHED: frozenset[str] = frozenset(
    {
        # TrustedEnvExt (trusted_ext.rs), minus the four cross-referenced ones
        "init_quot",
        "clone_pruned_shadowing_overlay",
        "set_param_names",
        "set_param_infos",
        "register_structure_fields",
        "register_recursor_unchecked",
        "extend_inductives_unchecked",
        "extend_constructors_unchecked",
        "extend_recursors_unchecked",
        "register_persistent_extension",
        "add_persistent_extension_entries",
        "get_persistent_extension_state",
        "get_persistent_extension_module_entries",
        "register_inductive",
        "register_constructor",
        "register_recursor",
        "set_reducibility",
        "upgrade_axiom_stubs",
        # R1-STUB / R1-IND replacement lanes (2026-08-24): the checked stub
        # upgrade and the structural inductive-family tier. Hardened, but they
        # still admit declarations below FullKernelCheck, so they stay watched
        # rather than silently trusted.
        "upgrade_axiom_stubs_checked",
        "extend_inductives_structural",
        "extend_constructors_structural",
        "extend_recursors_structural",
        "discharge_axiom_stub_for_inductive_import",
        "init_native_reducers",
        "init_arith_native_reducers",
        "materialize_extension_states",
        "export_extension_states",
        # bypass doors outside the trait (recon §3 items 5, 10, 11, 12)
        "register_inductive_unchecked",
        "register_constructor_unchecked",
        "add_skolem_axiom",
        "add_constant_unchecked_for_test",
        "set_constant_source",
    }
)

# Env deserialization entry points: associated functions, matched only as
# `Environment::<name>(` (they take no receiver, so no dot form exists).
ASSOC_WATCHED: frozenset[str] = frozenset({"from_json", "load_from_file", "load_snapshot"})

# Watched by the sibling scanners; cross-referenced in the census, never
# scanned here — one accounting point per site.
POINTER_METHODS: frozenset[str] = frozenset(
    {
        "add_decl_unchecked",
        "add_decl_structural",
        "extend_constants_unchecked",
        "extend_constants_structural",
    }
)

WATCHED: frozenset[str] = DOT_WATCHED | ASSOC_WATCHED

_dot_alt = "|".join(sorted(DOT_WATCHED, key=len, reverse=True))
CALL_RE = re.compile(
    r"(?:\.|\b(?:Environment|TrustedEnvExt)\s*::\s*)(" + _dot_alt + r")\s*\("
)
ASSOC_RE = re.compile(
    r"\bEnvironment\s*::\s*(" + "|".join(sorted(ASSOC_WATCHED, key=len, reverse=True)) + r")\s*\("
)
# Cheap prefilter: only files containing a watched name as a substring pay for
# noncode stripping + cfg(test) tracking. A file without the substring cannot
# contain a hit.
QUICK_RE = re.compile("|".join(sorted(WATCHED, key=len, reverse=True)))

CFG_TEST_RE = re.compile(r"#\[\s*cfg\s*\(\s*test\s*\)\s*\]")
MOD_RE = re.compile(r"\bmod\b")
TRAIT_FN_RE = re.compile(r"\bfn\s+([A-Za-z0-9_]+)\s*\(")


def is_test_path(rel: Path) -> bool:
    """True for test FILES. Byte-identical to check_add_decl_ratchet.py /
    check_extend_constants_ratchet.py so the three bypass gates cannot drift
    into disagreeing about what a test is."""
    parts = set(rel.parts)
    if "tests" in parts or "tests2" in parts:
        return True
    name = rel.name
    return bool(re.search(r"(^test_|_tests?\.rs$|^tests?\.rs$|^tests_)", name)) or "test" in name


# Rust non-code spans — same construction and rationale as
# check_add_decl_ratchet.py (ordered alternation; measured there: raw brace
# counting leaves 22 healthy files apparently unbalanced, stripping leaves 0).
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


def scan_file(path: Path, rel: Path) -> tuple[list[dict], list[dict]]:
    """(production hits, cfg(test) hits) for one file. Raises on unbalanced braces."""
    raw_text = path.read_text(errors="strict")
    if not QUICK_RE.search(raw_text):
        return [], []
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
                    pending_cfg = False
        else:
            depth += line.count("{") - line.count("}")
            if depth <= 0:
                in_cfg_test = False
        for m in list(CALL_RE.finditer(line)) + list(ASSOC_RE.finditer(line)):
            hit = {
                "file": str(rel),
                "line": lineno,
                "method": m.group(1),
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


def measure(root: Path) -> tuple[list[dict], list[dict], list[str]]:
    prod: list[dict] = []
    tested: list[dict] = []
    errors: list[str] = []
    for path in sorted((root / CRATES_REL).rglob("*.rs")):
        rel = path.relative_to(root)
        if is_test_path(rel):
            continue
        if rel == TRUSTED_EXT_REL:
            continue  # the trait + its Environment delegations: definitions, not usage
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


def trait_methods(root: Path) -> tuple[set[str], str | None]:
    """Every named fn in trusted_ext.rs (trait decls + impl delegations — the
    same set). Returns (names, error)."""
    path = root / TRUSTED_EXT_REL
    try:
        text = strip_noncode(path.read_text(errors="strict"))
    except (OSError, UnicodeDecodeError) as exc:
        return set(), f"cannot read {TRUSTED_EXT_REL}: {exc} — the choke-point trait is unreadable"
    return set(TRAIT_FN_RE.findall(text)), None


def load_census(root: Path) -> dict:
    path = root / CENSUS_REL
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:  # fail closed
        raise SystemExit(f"FAIL: cannot read {CENSUS_REL}: {exc}")


def run(root: Path, list_only: bool = False, require_complete: bool = True) -> int:
    census = load_census(root)
    prod, tested, errors = measure(root)

    if list_only:
        print(f"production sites ({len(prod)}):")
        for h in prod:
            print(f"  {h['file']}:{h['line']}  {h['method']}  | {h['text']}")
        print(f"inline cfg(test) sites: {len(tested)}")
        return 0

    ok = True

    def red(msg: str) -> None:
        nonlocal ok
        ok = False
        print(msg, file=sys.stderr)

    if errors:
        red("FAIL: the env-bypass scanner could not classify part of the tree:")
        for e in errors:
            print(f"  {e}", file=sys.stderr)

    # ---- config sanity: rows may only name watched methods, once each -------
    rows = census.get("rows", []) or []
    method_to_row: dict[str, dict] = {}
    for row in rows:
        if not isinstance(row, dict) or not row.get("id") or not row.get("methods"):
            red(f"FAIL: {CENSUS_REL} has a malformed row (needs 'id' and 'methods'): {row!r}")
            continue
        for meth in row["methods"]:
            if meth in POINTER_METHODS:
                red(
                    f"FAIL: census row {row['id']!r} names {meth}, which is watched by a "
                    f"sibling scanner — it belongs in cross_references (one accounting "
                    f"point per site), never in a scanned row."
                )
            elif meth not in WATCHED:
                red(
                    f"FAIL: census row {row['id']!r} names {meth}, which this scanner does "
                    f"not watch. The watched list lives in code "
                    f"({Path(__file__).name}); widen it there, with review, first."
                )
            elif meth in method_to_row:
                red(
                    f"FAIL: {meth} appears in census rows {method_to_row[meth]['id']!r} and "
                    f"{row['id']!r} — one accounting point per method."
                )
            else:
                method_to_row[meth] = row

    if require_complete:
        unrowed = sorted(WATCHED - set(method_to_row))
        if unrowed:
            red(
                f"FAIL: watched method(s) with no census row: {unrowed}. Every watched "
                f"method needs a row in {CENSUS_REL} — an expect-zero row (empty sites) "
                f"if it has no production caller."
            )

    # ---- trait drift: the choke point cannot quietly widen ------------------
    tmethods, terr = trait_methods(root)
    if terr:
        red(f"FAIL: {terr}")
    for meth in sorted(tmethods - DOT_WATCHED - POINTER_METHODS):
        red(
            f"FAIL: TrustedEnvExt ({TRUSTED_EXT_REL}) has a method {meth!r} that no "
            f"scanner watches — a new cross-crate mutation hook must be added to "
            f"DOT_WATCHED here (plus a census row) before it can land."
        )

    # ---- cross-references: pointers must still point at something -----------
    for xref in census.get("cross_references", []) or []:
        for key in ("methods", "scanner", "ledger"):
            if not xref.get(key):
                red(f"FAIL: cross-reference row {xref.get('id')!r} lacks {key!r}")
        scanner = xref.get("scanner")
        if scanner and not (root / scanner).is_file():
            red(
                f"FAIL: cross-reference {xref.get('id')!r} points at {scanner}, which does "
                f"not exist — the sibling scanner this census delegates to is gone."
            )
        ledger = xref.get("ledger")
        if ledger:
            try:
                ledger_doc = json.loads((root / ledger).read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError) as exc:
                red(f"FAIL: cross-reference {xref.get('id')!r}: cannot read {ledger}: {exc}")
                ledger_doc = None
            block = xref.get("ledger_key")
            if ledger_doc is not None and block and block not in ledger_doc:
                red(
                    f"FAIL: cross-reference {xref.get('id')!r}: {ledger} no longer has the "
                    f"{block!r} block it points at."
                )

    # ---- accounting: every production hit must land in its method's row -----
    def accounted(row: dict, file: str) -> bool:
        if any(site.get("file") == file for site in row.get("sites", []) or []):
            return True
        return any(file.startswith(p) for p in row.get("site_prefixes", []) or [])

    row_occurrences: dict[str, int] = {}
    unaccounted: list[dict] = []
    for h in prod:
        row = method_to_row.get(h["method"])
        if row is None or not accounted(row, h["file"]):
            unaccounted.append(h)
        else:
            row_occurrences[row["id"]] = row_occurrences.get(row["id"], 0) + 1
    if unaccounted:
        ok = False
        print(
            "FAIL: unaccounted environment-bypass call site(s) in production code:",
            file=sys.stderr,
        )
        for h in unaccounted:
            print(f"  {h['file']}:{h['line']}  {h['method']}  | {h['text']}", file=sys.stderr)
        print(
            "  -> a kernel-environment mutation/deserialization door outside the census. "
            f"Account for it in {CENSUS_REL} (the row watching that method), with its "
            "guard notes and R1-* disposition — or remove the call.",
            file=sys.stderr,
        )

    # ---- staleness: named sites and prefixes must still be live -------------
    live_by_row: dict[str, set[str]] = {}
    for h in prod:
        row = method_to_row.get(h["method"])
        if row is not None:
            live_by_row.setdefault(row["id"], set()).add(h["file"])
    for row in rows:
        if not isinstance(row, dict) or row.get("id") is None:
            continue
        live = live_by_row.get(row["id"], set())
        for site in row.get("sites", []) or []:
            f = site.get("file")
            if f and f not in live:
                red(
                    f"FAIL: census row {row['id']!r} names {f} and no production call to "
                    f"{'/'.join(row['methods'])} remains there. If the door was closed, "
                    f"remove the site row (the census only shrinks)."
                )
        for prefix in row.get("site_prefixes", []) or []:
            if not any(f.startswith(prefix) for f in live):
                red(
                    f"FAIL: census row {row['id']!r} carries site_prefix {prefix!r} with no "
                    f"live production call under it. Remove the prefix (stale class)."
                )

    # ---- ratchet: a row cannot quietly grow occurrences ---------------------
    for row in rows:
        if not isinstance(row, dict) or row.get("id") is None:
            continue
        cap = row.get("max_occurrences")
        if cap is None:
            continue
        seen = row_occurrences.get(row["id"], 0)
        if seen > cap:
            red(
                f"FAIL: census row {row['id']!r} measures {seen} production occurrences, "
                f"above its max_occurrences baseline {cap}. A new call through a watched "
                f"door must be justified and the baseline raised in review, never absorbed."
            )
        elif seen < cap:
            print(
                f"NOTE: census row {row['id']!r} measures {seen} production occurrences, "
                f"BELOW baseline {cap}; lower max_occurrences in {CENSUS_REL}."
            )

    if ok:
        total = sum(row_occurrences.values())
        print(
            f"OK: env-bypass census — {total} production call sites across "
            f"{len(rows)} census rows all accounted for; "
            f"{len(census.get('cross_references', []) or [])} cross-referenced ledger rows; "
            f"{len(tested)} inline cfg(test) sites excluded."
        )
        return 0
    return 1


# ---------------------------------------------------------------------------
# self-test: a gate that has never been shown to fail is not a gate
# ---------------------------------------------------------------------------

FAKE_TRUSTED_EXT = """\
pub trait TrustedEnvExt {
    fn init_quot(&mut self);
    fn add_decl_unchecked(&mut self, decl: Declaration);
    fn upgrade_axiom_stubs(&mut self, constants: C) -> usize;
}
"""

FAKE_LIB = """\
pub fn wire(env: &mut E, s: S) {
    env.set_constant_source(s);
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn t() {
        env.upgrade_axiom_stubs(d);
    }
}
"""

FAKE_KERNEL_BUILDER = """\
pub fn build(env: &mut E) {
    env.init_quot();
}
"""

FAKE_CENSUS = {
    "rows": [
        {
            "id": "stub-upgrade",
            "methods": ["upgrade_axiom_stubs"],
            "classification": "E",
            "disposition_job": "R1-STUB",
            "sites": [],
        },
        {
            "id": "lazy-source",
            "methods": ["set_constant_source"],
            "classification": "S/P",
            "disposition_job": "R1-LAZY",
            "sites": [{"file": "crates/c/src/lib.rs"}],
            "max_occurrences": 1,
        },
        {
            "id": "builders",
            "methods": ["init_quot"],
            "classification": "P",
            "disposition_job": "R1-EQREC",
            "sites": [],
            "site_prefixes": ["crates/k/"],
        },
    ],
    "cross_references": [],
}


def _selftest_tree() -> Path:
    tmp = Path(tempfile.mkdtemp(prefix="env_bypass_selftest_"))
    (tmp / "data").mkdir()
    (tmp / "crates" / "c" / "src").mkdir(parents=True)
    (tmp / "crates" / "k" / "src").mkdir(parents=True)
    (tmp / TRUSTED_EXT_REL).parent.mkdir(parents=True)
    (tmp / TRUSTED_EXT_REL).write_text(FAKE_TRUSTED_EXT)
    (tmp / CENSUS_REL).write_text(json.dumps(FAKE_CENSUS, indent=2))
    (tmp / "crates" / "c" / "src" / "lib.rs").write_text(FAKE_LIB)
    (tmp / "crates" / "k" / "src" / "builder.rs").write_text(FAKE_KERNEL_BUILDER)
    return tmp


def _quiet_run(root: Path, require_complete: bool = False) -> tuple[int, str]:
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
        rc = run(root, require_complete=require_complete)
    return rc, buf.getvalue()


def _arm(name: str, root: Path, expect: int, require_complete: bool = False) -> bool:
    rc, captured = _quiet_run(root, require_complete)
    good = rc == expect
    print(f"  [{'ok ' if good else 'FAIL'}] {name}: exit {rc} (expected {expect})")
    if not good and captured:
        print("    --- the arm's own output ---")
        for line in captured.rstrip("\n").splitlines():
            print(f"    {line}")
    return good


def selftest() -> int:
    passed = failed = 0

    def check(name: str, root: Path, expect: int, require_complete: bool = False) -> None:
        nonlocal passed, failed
        if _arm(name, root, expect, require_complete):
            passed += 1
        else:
            failed += 1

    root = _selftest_tree()
    lib = root / "crates" / "c" / "src" / "lib.rs"
    baseline = FAKE_LIB
    try:
        # 1. pristine tree: an accounted prod call, a prefix-class call, and a
        #    cfg(test)-excluded call -> green
        check("pristine tree (accounted site + prefix class + cfg(test) exclusion) is green", root, 0)

        # 2. NEW unaccounted dot-call bypass -> RED
        lib.write_text(baseline + "\npub fn smuggle(env: &mut E, d: D) { env.upgrade_axiom_stubs(d); }\n")
        check("NEW unaccounted dot-call (upgrade_axiom_stubs) is RED", root, 1)

        # 3. plant removed -> green again
        lib.write_text(baseline)
        check("removing the planted call restores green", root, 0)

        # 4. Environment::-qualified call form is caught too
        lib.write_text(baseline + "\npub fn q(e: &mut E, v: V) { Environment::register_inductive(e, v); }\n")
        check("Environment::-qualified call (register_inductive) is RED", root, 1)

        # 5. trait-qualified call form is caught too
        lib.write_text(baseline + "\npub fn tq(e: &mut E, r: R) { TrustedEnvExt::register_recursor(e, r); }\n")
        check("TrustedEnvExt::-qualified call (register_recursor) is RED", root, 1)

        # 6. the associated deserialization entry points are caught
        lib.write_text(baseline + "\npub fn deser(s: &str) { let _ = Environment::from_json(s); }\n")
        check("Environment::from_json (env deserialization) is RED", root, 1)

        # 7. the same call inside a #[cfg(test)] mod is EXCLUDED
        lib.write_text(
            baseline
            + "\n#[cfg(test)]\nmod more_tests {\n    fn t2() { let _ = Environment::from_json(s); }\n}\n"
        )
        check("the same call inside #[cfg(test)] mod is excluded (green)", root, 0)

        # 8. a call in a tests/ dir file is EXCLUDED
        lib.write_text(baseline)
        tdir = root / "crates" / "c" / "tests"
        tdir.mkdir()
        (tdir / "t.rs").write_text("fn t() { env.add_skolem_axiom(n, ty); }\n")
        check("a call in a tests/ dir is excluded (green)", root, 0)
        shutil.rmtree(tdir)

        # 9. a call quoted in a comment is NOT a hit
        lib.write_text(baseline + "\n// see env.add_skolem_axiom(n, ty) for the door\n")
        check("a call quoted in a comment is not counted", root, 0)

        # 10. a named site with no live call left is RED (stale row)
        lib.write_text("pub fn clean() {}\n")
        check("a census site row with no live call is RED (stale)", root, 1)

        # 11. a second occurrence beyond max_occurrences is RED
        lib.write_text(
            baseline + "\npub fn wire2(env: &mut E, s: S) { env.set_constant_source(s); }\n"
        )
        check("a second call over the row's max_occurrences cap is RED", root, 1)

        # 12. a stale site_prefix (class with no live call under it) is RED
        lib.write_text(baseline)
        builder = root / "crates" / "k" / "src" / "builder.rs"
        builder.write_text("pub fn clean() {}\n")
        check("a site_prefix with no live call under it is RED (stale class)", root, 1)
        builder.write_text(FAKE_KERNEL_BUILDER)

        # 13. a NEW TrustedEnvExt method nobody watches is RED (trait drift)
        (root / TRUSTED_EXT_REL).write_text(
            FAKE_TRUSTED_EXT.replace(
                "}", "    fn brand_new_door(&mut self, d: D);\n}", 1
            )
        )
        check("a new unwatched TrustedEnvExt method is RED (trait drift)", root, 1)
        (root / TRUSTED_EXT_REL).write_text(FAKE_TRUSTED_EXT)

        # 14. an unbalanced #[cfg(test)] mod fails CLOSED, never skips
        lib.write_text("#[cfg(test)]\nmod tests {\n    fn t() { env.upgrade_axiom_stubs(d); }\n")
        check("an unterminated cfg(test) block fails closed", root, 1)
        lib.write_text(baseline)

        # 15. census completeness: with require_complete (the real-run mode),
        #     the fake census's missing watched methods are RED
        check("an incomplete census is RED under the real-run completeness check", root, 1, True)

        # 16. an unreadable census fails closed
        (root / CENSUS_REL).write_text("{ not json")
        rc = 0
        try:
            _quiet_run(root)
        except SystemExit as exc:
            rc = 1 if exc.code else 0
        good = rc == 1
        print(f"  [{'ok ' if good else 'FAIL'}] an unparsable census fails closed: {good}")
        passed += 1 if good else 0
        failed += 0 if good else 1
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
